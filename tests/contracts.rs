//! Contract syntax, mathematical typing, scope, and erasure at real compiler boundaries.
use anl::{
    core,
    eval::{self, Value},
};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "apl-contracts-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn file(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, source).unwrap();
        path
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn bounded(mut command: Command) -> Output {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if child.try_wait().unwrap().is_some() {
            return child.wait_with_output().unwrap();
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            panic!("contract command timed out: {:?}", child.wait_with_output());
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}
fn cli(command: &str, path: &Path) -> Command {
    let mut process = Command::new(env!("CARGO_BIN_EXE_anl"));
    process.arg(command).arg(path);
    process
}
fn succeeds(output: Output, stdout: &[u8]) {
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(output.stdout, stdout);
    assert!(output.stderr.is_empty(), "{output:?}");
}
fn rejected(source: &str, message: &str) {
    let error = anl::compile(source).unwrap_err();
    assert!(!error.resource_limit, "{error:?}");
    let rendered = error.render("case.apl", source);
    assert!(rendered.contains(message), "{rendered}");
}

#[test]
fn contracts_are_checked_then_erased_from_execution_and_core() {
    let bare = "fn main()->i64 { 42 }";
    let annotated = "fn main()->i64
        requires 1 / 0 == 0;
        ensures (answer) answer == 9223372036854775808 * 9223372036854775808;
        { 42 }";
    let plain = anl::compile(bare).unwrap();
    let program = anl::compile(annotated).unwrap();
    let entry = program.entry().unwrap();
    assert_eq!(eval::evaluate(&program, entry, 100), Ok(Value::Integer(42)));
    let json = core::export(&program, entry).unwrap();
    assert_eq!(json, core::export(&plain, plain.entry().unwrap()).unwrap());
    let imported = core::import(&json.to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&imported.program, imported.entry, 100),
        Ok(Value::Integer(42))
    );

    let project = Project::new();
    let path = project.file("main.apl", annotated);
    succeeds(bounded(cli("check", &path)), b"");
    succeeds(bounded(cli("eval", &path)), b"42\n");
    succeeds(bounded(cli("run", &path)), b"42\n");
    let executable = project.0.join("result");
    let mut build = cli("build", &path);
    build.arg("-o").arg(&executable);
    succeeds(bounded(build), b"");
    succeeds(bounded(Command::new(executable)), b"42\n");
}

#[test]
fn mathematical_contracts_accept_scalar_types_and_contextual_identifiers() {
    let source = "fn requires(ensures:i64, flag:bool, nothing:unit)->i64
        requires flag || !flag;
        requires nothing == ();
        requires ensures > -9223372036854775809;
        ensures (requires) requires == ensures + 1;
        ensures (requires) (requires == ensures + 1) && 00042 == 42;
        { let requires = ensures + 1; requires }
        fn bool_result()->bool ensures (answer) answer || !answer; {true}
        fn unit_result()->unit ensures (answer) answer == (); {}
        fn main()->i64 { requires(41, bool_result(), unit_result()) }";
    let program = anl::compile(source).unwrap();
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100),
        Ok(Value::Integer(42))
    );
    assert!(anl::compile("fn helper(x:i64)->i64 requires x > 0; { x }").is_ok());
}

#[test]
fn clause_types_and_scope_are_enforced_before_any_execution() {
    for (source, message) in [
        ("fn f()->i64 requires 1; {0}", "must have type bool"),
        (
            "fn f()->i64 ensures (answer) answer; {0}",
            "must have type bool",
        ),
        (
            "fn f(x:bool)->i64 requires x + 1 == 2; {0}",
            "does not accept bool and int",
        ),
        (
            "fn f(x:unit)->i64 requires x < (); {0}",
            "does not accept unit and unit",
        ),
        (
            "fn f()->i64 requires -true == 0; {0}",
            "requires int, found bool",
        ),
        ("fn f()->i64 requires !1; {0}", "requires bool, found int"),
        (
            "fn f(x:i64)->i64 ensures (x) x == 0; {x}",
            "cannot shadow a parameter",
        ),
        (
            "fn f()->i64 requires answer == 0; {0}",
            "undefined specification name `answer`",
        ),
        (
            "fn f()->i64 ensures (answer) answer == local; {let local = 0; local}",
            "undefined specification name `local`",
        ),
        (
            "fn f()->i64 ensures (first) first == 0; ensures (second) first == second; {0}",
            "undefined specification name `first`",
        ),
        (
            "fn f()->i64 ensures (answer) answer == 0; {answer}",
            "undefined name `answer`",
        ),
        (
            "fn f()->i64 requires g == 0; {0} fn g()->i64 {0}",
            "undefined specification name `g`",
        ),
        (
            "fn f()->bool ensures (answer) answer == 0; {true}",
            "does not accept bool and int",
        ),
        (
            "fn main()->i64 {42} fn unused()->i64 requires missing; {0}",
            "undefined specification name `missing`",
        ),
    ] {
        rejected(source, message);
    }
}

#[test]
fn specifications_reject_unsupported_executable_constructs() {
    for (predicate, message) in [
        ("helper()", "function calls are not allowed"),
        ("{ true }", "blocks and local declarations are not allowed"),
        (
            "{ let x = true; x }",
            "blocks and local declarations are not allowed",
        ),
        (
            "if true {true} else {false}",
            "conditional expressions are not allowed",
        ),
        ("false && helper()", "function calls are not allowed"),
    ] {
        rejected(
            &format!("fn helper()->bool {{true}} fn main()->i64 requires {predicate}; {{42}}"),
            message,
        );
    }
    for (source, message) in [
        (
            "fn f()->i64 ensures (x) true; requires true; {0}",
            "requires clauses must precede ensures",
        ),
        ("fn f()->i64 requires true {0}", "; after requires clause"),
        ("fn f()->i64 ensures x true; {0}", "( before result binder"),
        ("fn f()->i64 ensures () true; {0}", "expected identifier"),
        ("fn f()->i64 ensures (x) true {0}", "; after ensures clause"),
    ] {
        rejected(source, message);
    }
}

#[test]
fn specification_literal_and_nesting_limits_do_not_change_runtime_literals() {
    let digits = "9".repeat(4096);
    let program = anl::compile(&format!(
        "fn main()->i64 requires -{digits} < {digits}; {{42}}"
    ))
    .unwrap();
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100),
        Ok(Value::Integer(42))
    );
    for digits in ["9".repeat(4097), "0".repeat(4097)] {
        let error =
            anl::compile(&format!("fn f()->i64 requires {digits} == 0; {{0}}")).unwrap_err();
        assert!(error.resource_limit, "{error:?}");
        assert!(error.message.contains("4096"));
    }
    let deep = format!(
        "fn f()->i64 requires {}true{}; {{0}}",
        "(".repeat(200),
        ")".repeat(200)
    );
    assert!(anl::compile(&deep).unwrap_err().resource_limit);
    rejected("fn main()->i64 {9223372036854775808}", "outside i64 range");
}

#[test]
fn imported_contract_errors_retain_their_file_and_binder_locations() {
    let project = Project::new();
    let root = project.file("main.apl", "mod math; fn main()->i64 {math::answer()}");
    let imported = project.file(
        "math.apl",
        "// imported Ω\npub fn answer()->i64\n    ensures (answer) answer == 42;\n{42}\n",
    );
    succeeds(bounded(cli("eval", &root)), b"42\n");
    fs::write(
        &imported,
        "pub fn answer()->i64 {42}\nfn unused(x:i64)->i64\n    ensures (x) true;\n{x}\n",
    )
    .unwrap();
    let output = bounded(cli("check", &root));
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let diagnostic = String::from_utf8(output.stderr).unwrap();
    assert!(
        diagnostic.contains(&format!("{}:3:", imported.display())),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("cannot shadow a parameter"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains(&format!("{}:2:", imported.display())),
        "{diagnostic}"
    );
}
