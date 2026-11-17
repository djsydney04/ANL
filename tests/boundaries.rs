use apl::{
    core::{self, ImportError},
    eval::{self, Value},
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
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
        Self { directory, path }
    }
    fn command(&self, command: &str) -> Command {
        let mut process = Command::new(env!("CARGO_BIN_EXE_apl"));
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
    let program = apl::compile("fn main()->i64{if true {42} else {0}}").unwrap();
    let entry = program.entry().unwrap();
    assert_eq!(eval::evaluate(&program, entry, 100), Ok(Value::Integer(42)));
    let json = core::export(&program, entry).to_string();
    let imported = core::import(&json).unwrap();
    assert_eq!(
        eval::evaluate(&imported.program, imported.entry, 100),
        Ok(Value::Integer(42))
    );
}

#[test]
fn duplicate_keys_cannot_impersonate_a_json_recursion_failure() {
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

fn closed_stderr(command: &mut Command) -> Output {
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    command.stderr(Stdio::from(writer)).output().unwrap()
}

#[test]
fn closed_stderr_is_an_infrastructure_failure_across_diagnostic_paths() {
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
        let closed = closed_stderr(input.command(command).args(&extra));
        assert_eq!(
            closed.status.code(),
            Some(4),
            "command {command}, input {bytes:?}"
        );
    }
    let oversized = Input::new(vec![b' '; apl::MAX_SOURCE_BYTES + 1]);
    assert_eq!(
        closed_stderr(&mut oversized.command("check")).status.code(),
        Some(4)
    );
    let missing = Input::new("");
    fs::remove_file(&missing.path).unwrap();
    assert_eq!(
        closed_stderr(&mut missing.command("check")).status.code(),
        Some(4)
    );
    let mut misuse = Command::new(env!("CARGO_BIN_EXE_apl"));
    misuse.arg("unknown-command");
    assert_eq!(closed_stderr(&mut misuse).status.code(), Some(4));
}

#[test]
fn successful_execution_does_not_require_stderr() {
    let input = Input::new("fn main()->i64{42}");
    let output = closed_stderr(&mut input.command("eval"));
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42\n");
}

#[test]
fn closed_stdout_and_stderr_do_not_trigger_a_secondary_panic() {
    let input = Input::new("fn main()->i64{42}");
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let mut command = input.command("eval");
    command.stdout(Stdio::from(writer));
    let output = closed_stderr(&mut command);
    assert_eq!(output.status.code(), Some(4));
}
