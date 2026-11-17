//! Invariant typing and source-only erasure; this does not enable loop verification.
use anl::{
    codegen, core,
    eval::{self, EvalError, Trap, Value},
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Value(Value),
    Trap(Trap),
    Resource(&'static str),
    InvalidIr,
}
fn outcome(program: &anl::types::Program, fuel: u64) -> Outcome {
    match eval::evaluate(program, program.entry().unwrap(), fuel) {
        Ok(value) => Outcome::Value(value),
        Err(EvalError::Trap { kind, .. }) => Outcome::Trap(kind),
        Err(EvalError::ResourceLimit { reason, .. }) => Outcome::Resource(reason),
        Err(EvalError::InvalidIr) => Outcome::InvalidIr,
        Err(EvalError::Infrastructure(reason)) => {
            panic!("unexpected infrastructure failure: {reason}")
        }
    }
}
fn checked(source: &str) -> anl::types::Program {
    anl::compile(source).unwrap_or_else(|error| panic!("{}", error.render("case.apl", source)))
}
fn rejected(source: &str, message: &str) {
    let error = anl::compile(source).unwrap_err();
    assert!(!error.resource_limit, "{error:?}");
    let rendered = error.render("case.apl", source);
    assert!(rendered.contains(message), "{rendered}");
}

#[test]
fn valid_false_undefined_and_mathematical_annotations_erase_exactly() {
    let template = "fn main()->i64 {let mut x=0;let start=x;
        while(x<3) ANNOTATIONS {x=x+1;} x+39}";
    let plain = checked(&template.replace("ANNOTATIONS", ""));
    let plain_core = core::export(&plain, plain.entry().unwrap())
        .unwrap()
        .to_string();
    let plain_c = codegen::emit_c(&plain, plain.entry().unwrap()).unwrap();
    for clauses in [
        "invariant x>=start; invariant x<=3;".to_owned(),
        "invariant false; invariant 1/0==0;".to_owned(),
        "invariant -9223372036854775808 / -1 == 9223372036854775808; invariant ()==(); invariant !false && (true || false);".to_owned(),
        format!("invariant {} > -{};", "9".repeat(4096), "9".repeat(4096)),
    ] {
        let annotated = checked(&template.replace("ANNOTATIONS", &clauses));
        let entry = annotated.entry().unwrap();
        assert_eq!(core::export(&annotated, entry).unwrap().to_string(), plain_core);
        assert_eq!(codegen::emit_c(&annotated, entry).unwrap(), plain_c);
        assert_eq!(outcome(&annotated, 1000), Outcome::Value(Value::Integer(42)));
        assert_eq!(annotated.semantic_revision(), "local-state-2026-11-17");
    }
    let imported = core::import(&plain_core).unwrap();
    assert_eq!(
        outcome(&imported.program, 1000),
        Outcome::Value(Value::Integer(42))
    );
    let mut forged: serde_json::Value = serde_json::from_str(&plain_core).unwrap();
    forged["invariants"] = serde_json::json!([true]);
    assert!(core::import(&forged.to_string()).is_err());
}

#[test]
fn erasure_preserves_every_tested_fuel_boundary_trap_kind_and_resource_reason() {
    for (template, expected) in [
        (
            "fn main()->i64 {while(false) ANNOTATION {} 7}",
            Outcome::Value(Value::Integer(7)),
        ),
        (
            "fn main()->i64 {let mut x=0;while({x=x+1;x<4}) ANNOTATION {x=x+1;} x}",
            Outcome::Value(Value::Integer(5)),
        ),
        (
            "fn main()->i64 {let mut x=9223372036854775807;while({x=x+1;true}) ANNOTATION {} x}",
            Outcome::Trap(Trap::ArithmeticOverflow),
        ),
        (
            "fn main()->i64 {while(true) ANNOTATION {1/0;} 7}",
            Outcome::Trap(Trap::DivisionByZero),
        ),
        (
            "fn main()->i64 {while(true) ANNOTATION {} 7}",
            Outcome::Resource("fuel exhausted"),
        ),
    ] {
        let plain = checked(&template.replace("ANNOTATION", ""));
        let annotated =
            checked(&template.replace("ANNOTATION", "invariant false; invariant 1/0==0;"));
        let plain_core = core::export(&plain, plain.entry().unwrap()).unwrap();
        assert_eq!(
            core::export(&annotated, annotated.entry().unwrap()).unwrap(),
            plain_core
        );
        assert_eq!(
            codegen::emit_c(&plain, plain.entry().unwrap()).unwrap(),
            codegen::emit_c(&annotated, annotated.entry().unwrap()).unwrap()
        );
        let imported = core::import(&plain_core.to_string()).unwrap();
        for fuel in 0..160 {
            let baseline = outcome(&plain, fuel);
            assert_eq!(
                outcome(&annotated, fuel),
                baseline,
                "fuel {fuel}: {template}"
            );
            assert_eq!(
                outcome(&imported.program, fuel),
                baseline,
                "core fuel {fuel}: {template}"
            );
        }
        assert_eq!(outcome(&annotated, 10_000), expected);
    }
    let zero = checked("fn main()->i64 {while(false) invariant false; {} 7}");
    assert_eq!(outcome(&zero, 3), Outcome::Resource("fuel exhausted"));
    assert_eq!(outcome(&zero, 4), Outcome::Value(Value::Integer(7)));
}

#[test]
fn contextual_words_remain_names_and_unannotated_loops_remain_valid() {
    let program = checked(
        "fn invariant(while:i64)->i64 {while}
        fn while(mut:i64)->i64 {invariant(mut)}
        fn main()->i64 {let invariant=true;let old=();
            while(false) invariant invariant; invariant old==(); {}
            while(false) {} while(42)}",
    );
    assert_eq!(outcome(&program, 100), Outcome::Value(Value::Integer(42)));
    let pure =
        checked("fn while(invariant:i64)->i64 {let mut=invariant;mut} fn main()->i64 {while(42)}");
    assert_eq!(pure.semantic_revision(), "m1-2026-11-16");
    assert_eq!(outcome(&pure, 100), Outcome::Value(Value::Integer(42)));
    // An ordinary local may share the spelling of an ensures binder.
    checked(
        "fn main()->i64 ensures(answer) answer==42; {let answer=true;while(false) invariant answer; {} 42}",
    );
}

#[test]
fn annotations_are_strictly_typed_in_head_scope_without_executing_them() {
    for (clause, message) in [
        ("1", "must have type bool"),
        ("()", "must have type bool"),
        ("!1", "requires bool"),
        ("true + 1 == 0", "does not accept bool and int"),
        ("x == true", "does not accept int and bool"),
        ("false && unknown", "undefined invariant name `unknown`"),
        ("f()", "function calls are not allowed"),
        ("old(x)==x", "function calls are not allowed"),
        ("f == f", "undefined invariant name `f`"),
        ("{let y=1;y==1}", "blocks and local declarations"),
        ("if true {true}else{false}", "conditional expressions"),
        ("x=1", "; after invariant clause"),
    ] {
        rejected(
            &format!(
                "fn f()->bool {{true}} fn main()->i64 {{let x=0;while(false) invariant {clause}; {{}} 42}}"
            ),
            message,
        );
    }
    for source in [
        "fn main()->i64 {while({let hidden=true;hidden}) invariant hidden; {} 42}",
        "fn main()->i64 {while(false) invariant hidden; {let hidden=true;} 42}",
        "fn main()->i64 {while(false) invariant hidden; {} let hidden=true;42}",
        "fn main()->i64 {if false {while(false) invariant hidden; {}}else{};42}",
        "fn main()->i64 {42} fn unused()->unit {while(false) invariant hidden; {}}",
    ] {
        rejected(source, "undefined invariant name `hidden`");
    }
    rejected(
        "fn main()->i64 ensures(answer) answer==42; {while(false) invariant answer==42; {} 42}",
        "undefined invariant name `answer`",
    );
}

#[test]
fn malformed_clauses_and_body_boundaries_are_rejected() {
    for (source, message) in [
        (
            "fn main()->i64 {while(false) invariant true {} 42}",
            "; after invariant clause",
        ),
        (
            "fn main()->i64 {while(false) invariant; {} 42}",
            "expected expression",
        ),
        (
            "fn main()->i64 {while(false) invariant true; 42}",
            "expected {",
        ),
        (
            "fn main()->i64 {while(false) invariant true; {}; 42}",
            "expected expression",
        ),
        (
            "fn main()->i64 {while(false) invariant true; {1} 42}",
            "expected unit",
        ),
        (
            "fn main()->i64 {while(1) invariant true; {} 42}",
            "expected bool",
        ),
    ] {
        rejected(source, message);
    }
}

#[test]
fn annotation_resource_limits_cover_literals_expression_depth_and_tokens() {
    let literal = format!(
        "fn main()->i64 {{while(false) invariant {}==0; {{}}42}}",
        "9".repeat(4097)
    );
    let depth = format!(
        "fn main()->i64 {{while(false) invariant {}true; {{}}42}}",
        "!".repeat(200)
    );
    let tokens = format!(
        "fn main()->i64 {{while(false) {} {{}}42}}",
        "invariant true;".repeat(anl::MAX_TOKENS / 3)
    );
    for (source, message) in [
        (literal, "4096 decimal digits"),
        (depth, "limit exceeded"),
        (tokens, "token limit exceeded"),
    ] {
        let error = anl::compile(&source).unwrap_err();
        assert!(error.resource_limit, "{error:?}");
        assert!(
            error.render("case.apl", &source).contains(message),
            "{error:?}"
        );
    }
    // Clause count does not become executable statement count or typed depth.
    let many = checked(&format!(
        "fn main()->i64 {{while(false) {} {{}}42}}",
        "invariant true;".repeat(200)
    ));
    assert_eq!(outcome(&many, 4), Outcome::Value(Value::Integer(42)));
}

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "apl-loop-annotations-{}-{}",
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
            panic!(
                "annotation command timed out: {:?}",
                child.wait_with_output()
            );
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

#[test]
fn imported_unused_annotations_are_checked_with_their_own_source_locations() {
    let project = Project::new();
    let root = project.file("main.apl", "mod helper;fn main()->i64 {42}");
    let imported = project.file(
        "helper.apl",
        "fn unused()->unit {\n while(false)\n invariant unknown;\n {}\n}",
    );
    let error = anl::compile_file(&root).unwrap_err();
    let rendered = error.render("unused", "");
    assert!(
        rendered.contains(&format!("{}:3:", imported.display())),
        "{rendered}"
    );
    assert!(
        rendered.contains("undefined invariant name `unknown`"),
        "{rendered}"
    );
    project.file(
        "helper.apl",
        "fn unused()->unit {while(false) invariant false; invariant 1/0==0; {}}",
    );
    let program = anl::compile_file(&root).unwrap();
    assert_eq!(outcome(&program, 1), Outcome::Value(Value::Integer(42)));
}

#[test]
fn ordinary_cli_commands_erase_annotations_before_native_execution() {
    let project = Project::new();
    let path = project.file(
        "main.apl",
        "fn main()->i64 {let mut x=40;while(x<42) invariant false; invariant 1/0==0; {x=x+1;} x}",
    );
    for (command, stdout) in [
        ("check", b"".as_slice()),
        ("eval", b"42\n".as_slice()),
        ("run", b"42\n".as_slice()),
    ] {
        let mut process = Command::new(env!("CARGO_BIN_EXE_anl"));
        process.arg(command).arg(&path);
        let output = bounded(process);
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        assert_eq!(output.stdout, stdout);
        assert!(output.stderr.is_empty(), "{output:?}");
    }
}
