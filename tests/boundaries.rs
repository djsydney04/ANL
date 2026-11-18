use anl::{
    core::{self, ImportError},
    eval::{self, Value},
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output, Stdio},
    sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
// A concurrently spawned child can retain another test's pipe reader until
// exec, making a supposedly broken output pipe temporarily writable.
static PROCESS_LOCK: Mutex<()> = Mutex::new(());
struct Input {
    directory: PathBuf,
    path: PathBuf,
}
impl Input {
    fn new(bytes: impl AsRef<[u8]>) -> Self {
        let directory = std::env::temp_dir().join(format!(
            "apl-boundaries-{}-{}",
            std::process::id(),
            NEXT_ID.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let path = directory.join("case.apl");
        fs::write(&path, bytes).unwrap();
        fs::write(directory.join("readonly-output"), b"").unwrap();
        Self { directory, path }
    }
    fn command(&self, command: &str) -> Command {
        let mut process = Command::new(env!("CARGO_BIN_EXE_anl"));
        process.arg(command).arg(&self.path);
        process
    }
}
impl Drop for Input {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn checked_program_remains_usable_through_public_source_and_json_apis() {
    let program = anl::compile("fn main()->i64{if true {42} else {0}}").unwrap();
    let entry = program.entry().unwrap();
    assert_eq!(eval::evaluate(&program, entry, 100), Ok(Value::Integer(42)));
    let json = core::export(&program, entry).unwrap().to_string();
    let imported = core::import(&json).unwrap();
    assert_eq!(
        eval::evaluate(&imported.program, imported.entry, 100),
        Ok(Value::Integer(42))
    );
}

#[test]
fn duplicate_keys_cannot_impersonate_a_json_recursion_failure() {
    let _guard = PROCESS_LOCK.lock().unwrap();
    for text in [
        r#"{"recursion limit exceeded":0,"recursion limit exceeded":1}"#,
        r#"{"recursion limit exceeded":0,"\u0072ecursion limit exceeded":1}"#,
        r#"{"expression":{"\u0072ecursion limit exceeded":0,"recursion limit exceeded":1}}"#,
        r#"{"recursion limit exceeded at line 1 column 1":0,"recursion limit exceeded at line 1 column 1":1}"#,
    ] {
        assert!(
            matches!(core::import(text), Err(ImportError::Invalid(_))),
            "{text}"
        );
        let input = Input::new(text);
        let output = input.command("eval-core").output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(1),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            serde_json::from_slice::<serde_json::Value>(&output.stdout).unwrap(),
            serde_json::json!({"outcome":"invalid_ir"})
        );
    }
}

#[test]
fn actual_json_recursion_exhaustion_still_reports_resource_limit() {
    let _guard = PROCESS_LOCK.lock().unwrap();
    let text = format!("{}0{}", "[".repeat(1000), "]".repeat(1000));
    assert!(matches!(
        core::import(&text),
        Err(ImportError::ResourceLimit(_))
    ));
    let input = Input::new(text);
    let output = input.command("eval-core").output().unwrap();
    assert_eq!(output.status.code(), Some(3));
    assert_eq!(
        serde_json::from_slice::<serde_json::Value>(&output.stdout).unwrap(),
        serde_json::json!({"outcome":"resource_limit"})
    );
}

#[derive(Clone, Copy, Debug)]
enum Unwritable {
    BrokenPipe,
    ReadOnly,
}
impl Unwritable {
    fn stdio(self, input: &Input) -> Stdio {
        match self {
            Self::BrokenPipe => {
                let (reader, writer) = std::io::pipe().unwrap();
                drop(reader);
                Stdio::from(writer)
            }
            Self::ReadOnly => {
                Stdio::from(fs::File::open(input.directory.join("readonly-output")).unwrap())
            }
        }
    }
}

fn unavailable_stderr(command: &mut Command, mode: Unwritable, input: &Input) -> Output {
    let output = command.stderr(mode.stdio(input)).output().unwrap();
    assert_eq!(
        fs::read(input.directory.join("readonly-output")).unwrap(),
        b""
    );
    output
}

#[test]
fn unavailable_stderr_is_an_infrastructure_failure_across_diagnostic_paths() {
    let _guard = PROCESS_LOCK.lock().unwrap();
    for (bytes, command, extra, normal_code) in [
        (
            b"fn main()->i64{missing}".as_slice(),
            "check",
            Vec::<&str>::new(),
            1,
        ),
        (b"fn helper()->i64{42}".as_slice(), "eval", vec![], 1),
        (b"fn main()->i64{1 / 0}".as_slice(), "eval", vec![], 2),
        (
            b"fn main()->i64{42}".as_slice(),
            "eval",
            vec!["--fuel", "0"],
            3,
        ),
        (b"\xff".as_slice(), "check", vec![], 1),
        (b"{}".as_slice(), "eval-core", vec![], 1),
    ] {
        let input = Input::new(bytes);
        let normal = input.command(command).args(&extra).output().unwrap();
        assert_eq!(normal.status.code(), Some(normal_code));
        for mode in [Unwritable::BrokenPipe, Unwritable::ReadOnly] {
            let failed = unavailable_stderr(input.command(command).args(&extra), mode, &input);
            assert_eq!(
                failed.status.code(),
                Some(4),
                "command {command}, input {bytes:?}, descriptor {mode:?}"
            );
        }
    }
    let oversized = Input::new(vec![b' '; anl::MAX_SOURCE_BYTES + 1]);
    let missing = Input::new("");
    fs::remove_file(&missing.path).unwrap();
    for mode in [Unwritable::BrokenPipe, Unwritable::ReadOnly] {
        assert_eq!(
            unavailable_stderr(&mut oversized.command("check"), mode, &oversized)
                .status
                .code(),
            Some(4)
        );
        assert_eq!(
            unavailable_stderr(&mut missing.command("check"), mode, &missing)
                .status
                .code(),
            Some(4)
        );
        let mut misuse = Command::new(env!("CARGO_BIN_EXE_anl"));
        misuse.arg("unknown-command");
        assert_eq!(
            unavailable_stderr(&mut misuse, mode, &missing)
                .status
                .code(),
            Some(4)
        );
    }
}

#[test]
fn successful_execution_does_not_require_stderr() {
    let _guard = PROCESS_LOCK.lock().unwrap();
    let input = Input::new("fn main()->i64{42}");
    for mode in [Unwritable::BrokenPipe, Unwritable::ReadOnly] {
        let output = unavailable_stderr(&mut input.command("eval"), mode, &input);
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, b"42\n");
    }
}

#[test]
fn unavailable_stdout_and_stderr_do_not_trigger_a_secondary_panic() {
    let _guard = PROCESS_LOCK.lock().unwrap();
    let input = Input::new("fn main()->i64{42}");
    for mode in [Unwritable::BrokenPipe, Unwritable::ReadOnly] {
        let mut command = input.command("eval");
        command.stdout(mode.stdio(&input));
        let output = unavailable_stderr(&mut command, mode, &input);
        assert_eq!(output.status.code(), Some(4));
    }
}

#[test]
fn required_stdout_failure_is_an_infrastructure_error() {
    let _guard = PROCESS_LOCK.lock().unwrap();
    let input = Input::new("fn main()->i64{cast i64(40u8 + 2u8)}");
    for action in ["--version", "eval", "emit-c"] {
        let command = || {
            if action == "--version" {
                let mut command = Command::new(env!("CARGO_BIN_EXE_anl"));
                command.arg(action);
                command
            } else {
                input.command(action)
            }
        };
        let normal = command().output().unwrap();
        assert_eq!(normal.status.code(), Some(0));
        assert!(normal.stderr.is_empty());
        match action {
            "--version" => assert_eq!(
                normal.stdout,
                concat!("anl ", env!("CARGO_PKG_VERSION"), "\n").as_bytes()
            ),
            "eval" => assert_eq!(normal.stdout, b"42\n"),
            "emit-c" => assert!(
                String::from_utf8(normal.stdout)
                    .unwrap()
                    .contains("int main(void)")
            ),
            _ => unreachable!(),
        }
        for mode in [Unwritable::BrokenPipe, Unwritable::ReadOnly] {
            let failed = command().stdout(mode.stdio(&input)).output().unwrap();
            assert_eq!(failed.status.code(), Some(4), "{action}: {mode:?}");
            assert!(failed.stdout.is_empty());
            assert!(failed.stderr.starts_with(b"anl: cannot write stdout:"));
            assert_eq!(
                fs::read(input.directory.join("readonly-output")).unwrap(),
                b""
            );
        }
    }
}
