//! Local state semantics through source checking and strict core interchange.
use anl::{
    core,
    eval::{self, EvalError, Trap, Value},
};
use serde_json::{Value as Json, json};
use std::{
    fs,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

fn source_result(source: &str, fuel: u64) -> Result<Value, EvalError> {
    let program =
        anl::compile(source).unwrap_or_else(|error| panic!("{}", error.render("case.apl", source)));
    eval::evaluate(&program, program.entry().unwrap(), fuel)
}

fn result(source: &str, expected: i64) {
    let program =
        anl::compile(source).unwrap_or_else(|error| panic!("{}", error.render("case.apl", source)));
    let entry = program.entry().unwrap();
    assert_eq!(
        eval::evaluate(&program, entry, 1_000_000),
        Ok(Value::Integer(expected)),
        "{source}"
    );
    let exported = core::export(&program, entry).unwrap();
    assert_eq!(exported["schema"], "apl-core-v1", "{source}");
    assert_eq!(exported["semantic_revision"], "local-state-2026-11-17");
    let imported = core::import(&exported.to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&imported.program, imported.entry, 1_000_000),
        Ok(Value::Integer(expected)),
        "imported {source}"
    );
}

fn body(source: &str, expected: i64) {
    result(&format!("fn main()->i64 {{ {source} }}"), expected);
}

fn rejects(source: &str, message: &str) {
    let error = anl::compile(source).unwrap_err();
    assert!(!error.resource_limit, "{error:?}");
    let rendered = error.render("case.apl", source);
    assert!(rendered.contains(message), "{rendered}");
}

#[test]
fn lexical_scope_preserves_outer_writes_and_restores_shadowed_bindings() {
    for (source, expected) in [
        ("let mut x = 1; x", 1),
        ("let mut x=1; {x=2;}; x", 2),
        ("let mut x=1; {let mut x=2; x=3;}; x", 1),
        ("let mut x=1; let y={x=2;3}; y*10+x", 32),
        ("let mut x=2; 9; x=x+3; 8; x", 5),
        ("let mut x=1; x={x=2; x+3}; x", 5),
        ("let mut x=1; let mut y={x=4; x+2}; y=y+1; x*10+y", 47),
    ] {
        body(source, expected);
    }
    rejects(
        "fn main()->i64 { let mut x=1; {let x=2; x=3;}; x }",
        "immutable binding `x`",
    );
}

#[test]
fn assignment_reacquires_its_target_after_rhs_scope_growth() {
    let mut source = String::from("let mut x=1; x={let x=9;");
    for i in 0..40 {
        source.push_str(&format!("let pad{i}={i};"));
    }
    source.push_str("x+33}; x");
    body(&source, 42);
}

#[test]
fn ordered_expressions_observe_current_state_and_short_circuit_effects() {
    for (source, expected) in [
        ("let mut x=0; {x=1;x}+{x=x+1;x}", 3),
        ("let mut x=0; if {x=2;true} {x=x+1;} else {()}; x", 3),
        ("let mut x=0; {x=1;false} && {x=9;true}; x", 1),
        ("let mut x=0; {x=1;true} || {x=9;false}; x", 1),
        ("let mut x=0; {x=1;true} && {x=x+2;true}; x", 3),
        ("let mut x=0; if false {x=9;} else {x=4;}; x", 4),
    ] {
        body(source, expected);
    }
}

#[test]
fn arguments_mutate_the_caller_in_order_and_callees_have_isolated_locals() {
    result(
        "fn pair(a:i64,b:i64)->i64 {a*10+b}
        fn main()->i64 {let mut x=0; pair({x=1;x},{x=x+1;x})*10+x}",
        122,
    );
    result(
        "fn change(x:i64)->i64 {let mut x=x; x=9; x}
        fn main()->i64 {let mut x=1; change(x); x}",
        1,
    );
    result(
        "fn identity(x:i64)->i64 {x}
        fn pair(a:i64,b:i64)->i64 {a*10+b}
        fn main()->i64 {let mut x=0; pair(identity({x=1;x}),{x=x+1;x})*10+x}",
        122,
    );
    result(
        "fn sum(n:i64)->i64 {let mut answer=n;
            if n>0 {answer=answer+sum(n-1);} else {()}; answer}
        fn main()->i64 {sum(10)}",
        55,
    );
}

#[test]
fn loops_repeat_the_guard_reinitialize_locals_and_keep_final_false_effects() {
    for (source, expected) in [
        ("let mut x=0; while(false) {x=1/0;} x", 0),
        ("let mut x=0; while({x=x+1;x<4}) {} x", 4),
        (
            "let mut i=0; let mut sum=0; while(i<3) {let mut local=1; local=local+1; sum=sum+local; i=i+1;} sum",
            6,
        ),
        (
            "let mut i=0; let mut count=0; while(i<3) {let mut j=0; while(j<4) {count=count+1; j=j+1;} i=i+1;} count",
            12,
        ),
        (
            "let mut running=true; let mut nothing=(); let mut count=0; while(running) {nothing=(); count=count+1; running=false;} if nothing==() {count} else {0}",
            1,
        ),
        ("let mut i=0; while(i<100000) {i=i+1;} i", 100000),
    ] {
        body(source, expected);
    }
}

#[test]
fn loops_and_assignments_preserve_defined_traps_and_trap_order() {
    for (source, expected) in [
        ("let mut x=0; x=1/0; x", Trap::DivisionByZero),
        (
            "let mut x=9223372036854775807; x=x+1; x",
            Trap::ArithmeticOverflow,
        ),
        (
            "while({1/0; true}) {9223372036854775807+1; } 0",
            Trap::DivisionByZero,
        ),
        (
            "let mut x=0; while(x<3) {x=x+1; 1/(2-x);} x",
            Trap::DivisionByZero,
        ),
        (
            "let mut x=0; x={9223372036854775807+1; 1/0}; x",
            Trap::ArithmeticOverflow,
        ),
    ] {
        let source = format!("fn main()->i64 {{ {source} }}");
        let program = anl::compile(&source).unwrap();
        let entry = program.entry().unwrap();
        assert!(
            matches!(eval::evaluate(&program, entry, 1000), Err(EvalError::Trap {kind, ..}) if kind==expected),
            "{source}"
        );
        let imported = core::import(&core::export(&program, entry).unwrap().to_string()).unwrap();
        assert!(
            matches!(eval::evaluate(&imported.program, imported.entry, 1000), Err(EvalError::Trap {kind, ..}) if kind==expected),
            "{source}"
        );
    }
}

#[test]
fn loop_fuel_counts_visits_without_increasing_nesting_each_iteration() {
    let source = "fn main()->i64 {while(false) {} 7}";
    assert_eq!(source_result(source, 4), Ok(Value::Integer(7)));
    assert!(matches!(
        source_result(source, 3),
        Err(EvalError::ResourceLimit {
            reason: "fuel exhausted",
            ..
        })
    ));
    let source = "fn main()->i64 {while(true) {} 7}";
    assert!(matches!(
        source_result(source, 10000),
        Err(EvalError::ResourceLimit {
            reason: "fuel exhausted",
            ..
        })
    ));
    let source = "fn main()->i64 {let mut x=0; x=1; x}";
    assert_eq!(source_result(source, 6), Ok(Value::Integer(1)));
    assert!(matches!(
        source_result(source, 5),
        Err(EvalError::ResourceLimit {
            reason: "fuel exhausted",
            ..
        })
    ));
}

#[test]
fn static_permissions_and_statement_types_are_enforced_in_all_code() {
    for (source, message) in [
        ("fn main()->i64 {let x=1; x=2; x}", "immutable binding"),
        ("fn f(x:i64)->i64 {x=2; x}", "immutable binding"),
        (
            "fn main()->i64 {missing=2; 0}",
            "undefined assignment target",
        ),
        ("fn main()->i64 {let mut x=1; x=true; x}", "expected i64"),
        ("fn main()->i64 {let mut x:i64=true; 0}", "expected i64"),
        ("fn main()->i64 {let mut x=x; x}", "undefined name"),
        (
            "fn main()->i64 {let mut x=0; let x=1; x}",
            "duplicate local binding",
        ),
        ("fn main()->i64 {while(1) {} 0}", "expected bool"),
        ("fn main()->i64 {while(false) {1} 0}", "expected unit"),
        (
            "fn main()->i64 {while(false) {let x=1;} x}",
            "undefined name",
        ),
        (
            "fn main()->i64 {let x=0; if false {x=1;} else {()}; x}",
            "immutable binding",
        ),
        (
            "fn unused()->unit {let x=0; x=1;} fn main()->i64 {0}",
            "immutable binding",
        ),
    ] {
        rejects(source, message);
    }
    for source in [
        "fn main()->i64 {let mut x=0; x=x=1; x}",
        "fn main()->i64 {let mut x=0; x+=1; x}",
        "fn main()->i64 {let mut x=0; (x)=1; x}",
        "fn main()->i64 {let mut x=0; let y=(x=1); x}",
        "fn main()->i64 {while(true) {}; 0}",
        "fn main()->i64 {while true {} 0}",
        "fn main()->i64 {let mut x=0; while(x<1) {x=1} x}",
    ] {
        assert!(anl::compile(source).is_err(), "{source}");
    }
    let source = "fn main()->i64 {let mut x=1; x=true; x}";
    let error = anl::compile(source).unwrap_err();
    assert_eq!(error.span.start, source.find("true").unwrap());
    assert_eq!(error.related.unwrap().0.start, source.find("x=1").unwrap());
}

#[test]
fn contextual_words_preserve_old_programs_and_v0_export() {
    let source = "fn while(mut:i64)->i64 {mut+1}
        fn main()->i64 {let mut=40; while(mut); let while=2; mut+while}";
    let program = anl::compile(source).unwrap();
    assert!(!program.has_local_state());
    assert_eq!(program.semantic_revision(), "m1-2026-11-16");
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100),
        Ok(Value::Integer(42))
    );
    let json = core::export(&program, program.entry().unwrap()).unwrap();
    assert_eq!(json["schema"], "apl-core-v0");
    let imported = core::import(&json.to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&imported.program, imported.entry, 100),
        Ok(Value::Integer(42))
    );
    let plain = anl::compile("fn main()->i64 {42}").unwrap();
    assert_eq!(
        core::export(&plain, 0).unwrap().to_string(),
        r#"{"entry":0,"functions":[{"body":{"tag":"integer","ty":"i64","value":"42"},"id":0,"name":"main","params":[],"result":"i64"}],"schema":"apl-core-v0","semantic_revision":"m1-2026-11-16"}"#
    );
    body(
        "let mut mut=1; mut=mut+1; let mut while=mut; while=while+1; while",
        3,
    );
    result(
        "fn while(x:i64)->bool {x<2} fn main()->i64 {let mut x=0; while(while(x)) {x=x+1;} x}",
        2,
    );
}

#[test]
fn revision_selection_inspects_unused_functions_and_unselected_branches() {
    for source in [
        "fn unused()->unit {let mut x=0;} fn main()->i64 {42}",
        "fn unused()->unit {while(false) {}} fn main()->i64 {42}",
        "fn main()->i64 {if false {let mut x=0; x} else {42}}",
    ] {
        let program = anl::compile(source).unwrap();
        assert!(program.has_local_state());
        assert_eq!(program.semantic_revision(), "local-state-2026-11-17");
        assert_eq!(
            core::export(&program, program.entry().unwrap()).unwrap()["schema"],
            "apl-core-v1"
        );
    }
}

fn integer(value: i64) -> Json {
    json!({"tag":"integer", "ty":"i64", "value":value.to_string()})
}
fn unit() -> Json {
    json!({"tag":"unit", "ty":"unit"})
}
fn assignment(index: usize, value: Json) -> Json {
    json!({"tag":"assign", "ty":"unit", "index":index, "value":value})
}
fn mutable(value: Json, body: Json) -> Json {
    json!({"tag":"let_mut", "ty":body["ty"], "value":value, "body":body})
}
fn fixture(expression: Json) -> Json {
    json!({"schema":"apl-expr-v1", "semantic_revision":"local-state-2026-11-17", "expression":expression})
}
fn reject_core(artifact: Json, message: &str) {
    let error = match core::import(&artifact.to_string()) {
        Ok(_) => panic!("accepted invalid artifact: {artifact}"),
        Err(error) => error,
    };
    assert!(matches!(error, core::ImportError::Invalid(_)), "{error}");
    assert!(error.to_string().contains(message), "{error}");
}

#[test]
fn v1_import_checks_permissions_types_and_scope_independently() {
    let valid = fixture(mutable(integer(0), assignment(0, integer(1))));
    let artifact = core::import(&valid.to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&artifact.program, artifact.entry, 4),
        Ok(Value::Unit)
    );
    let empty_loop = fixture(
        json!({"tag":"while","ty":"unit","condition":{"tag":"boolean","ty":"bool","value":false},"body":unit()}),
    );
    let artifact = core::import(&empty_loop.to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&artifact.program, artifact.entry, 2),
        Ok(Value::Unit)
    );
    assert!(matches!(
        eval::evaluate(&artifact.program, artifact.entry, 1),
        Err(EvalError::ResourceLimit { .. })
    ));
    let mut immutable = valid.clone();
    immutable["expression"]["tag"] = "let".into();
    reject_core(immutable, "immutable");
    reject_core(fixture(assignment(0, integer(1))), "unbound");
    reject_core(
        fixture(mutable(integer(0), assignment(1, integer(1)))),
        "unbound",
    );
    reject_core(
        fixture(mutable(
            integer(0),
            assignment(0, json!({"tag":"boolean","ty":"bool","value":true})),
        )),
        "type mismatch",
    );
    let mut wrong_type = valid.clone();
    wrong_type["expression"]["body"]["ty"] = "i64".into();
    reject_core(wrong_type, "inferred type");
    let mut extra = valid.clone();
    extra["expression"]["mutable"] = true.into();
    reject_core(extra, "exactly members");
    let malformed_loop = json!({"tag":"while","ty":"unit","condition":integer(0),"body":unit()});
    reject_core(fixture(malformed_loop), "bool condition and unit body");
    let malformed_loop = json!({"tag":"while","ty":"unit","condition":{"tag":"boolean","ty":"bool","value":false},"body":integer(0)});
    reject_core(fixture(malformed_loop), "bool condition and unit body");
    let shadow =
        json!({"tag":"let","ty":"unit","value":integer(1),"body":assignment(0,integer(2))});
    reject_core(fixture(mutable(integer(0), shadow)), "immutable");
    let branch = json!({"tag":"if","ty":"unit","condition":{"tag":"boolean","ty":"bool","value":false},"then":assignment(1,integer(1)),"else":unit()});
    reject_core(fixture(mutable(integer(0), branch)), "unbound");
    let params = json!({"schema":"apl-core-v1","semantic_revision":"local-state-2026-11-17","entry":1,"functions":[
        {"id":0,"name":"f","params":["i64"],"result":"unit","body":assignment(0,integer(2))},
        {"id":1,"name":"main","params":[],"result":"i64","body":integer(0)}]});
    reject_core(params, "immutable");
}

#[test]
fn v1_rejects_schema_mismatches_duplicate_fields_and_invalid_indices() {
    let valid = fixture(mutable(integer(0), assignment(0, integer(1))));
    let mut old = valid.clone();
    old["schema"] = "apl-expr-v0".into();
    old["semantic_revision"] = "m1-2026-11-16".into();
    reject_core(old, "unknown expression constructor");
    for (schema, revision) in [
        ("apl-expr-v0", "local-state-2026-11-17"),
        ("apl-expr-v1", "m1-2026-11-16"),
    ] {
        let mut wrong = fixture(integer(0));
        wrong["schema"] = schema.into();
        wrong["semantic_revision"] = revision.into();
        reject_core(wrong, "unsupported semantic revision");
    }
    let old = core::import(&fixture(integer(42)).to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&old.program, old.entry, 1),
        Ok(Value::Integer(42))
    );
    for index in [json!(-1), json!(1.0), json!("0"), json!(u64::MAX)] {
        let mut wrong = valid.clone();
        wrong["expression"]["body"]["index"] = index;
        assert!(core::import(&wrong.to_string()).is_err());
    }
    let duplicate = valid
        .to_string()
        .replace("\"index\":0", "\"index\":0,\"index\":0");
    assert!(
        matches!(core::import(&duplicate), Err(core::ImportError::Invalid(message)) if message.contains("duplicate object member"))
    );
    let call = json!({"tag":"call","ty":"i64","function":0,"arguments":[]});
    reject_core(fixture(call), "outside expression fixture scope");
}

#[test]
fn erased_contracts_do_not_add_dynamic_checks_to_stateful_execution() {
    let bare = "fn main()->i64 {let mut x=0; while(x<3) {x=x+1;} x}";
    let annotated = "fn main()->i64 requires false; ensures(answer) answer==9; {let mut x=0; while(x<3) {x=x+1;} x}";
    let bare = anl::compile(bare).unwrap();
    let annotated = anl::compile(annotated).unwrap();
    assert_eq!(
        core::export(&bare, 0).unwrap(),
        core::export(&annotated, 0).unwrap()
    );
    assert_eq!(eval::evaluate(&annotated, 0, 100), Ok(Value::Integer(3)));
}

static NEXT: AtomicU64 = AtomicU64::new(0);

#[test]
fn cli_checks_evaluates_and_round_trips_v1() {
    let path = std::env::temp_dir().join(format!(
        "apl-control-flow-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(path.clone());
    let source = path.join("main.apl");
    let artifact = path.join("main.json");
    fs::write(
        &source,
        "fn main()->i64 {let mut x=0; while(x<42) {x=x+1;} x}",
    )
    .unwrap();
    for (command, input, expected) in [
        ("check", &source, Some(b"".as_slice())),
        ("eval", &source, Some(b"42\n".as_slice())),
        ("dump-core", &source, None),
        (
            "eval-core",
            &artifact,
            Some(b"{\"outcome\":\"value\",\"type\":\"i64\",\"value\":\"42\"}\n".as_slice()),
        ),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_anl"))
            .arg(command)
            .arg(input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                panic!("{command} exceeded test timeout");
            }
            std::thread::sleep(Duration::from_millis(2));
        }
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{command}: {output:?}");
        assert!(output.stderr.is_empty(), "{command}: {output:?}");
        if let Some(expected) = expected {
            assert_eq!(output.stdout, expected, "{command}");
        } else {
            let json: Json = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(json["schema"], "apl-core-v1");
            fs::write(&artifact, output.stdout).unwrap();
        }
    }
    fs::write(&source, "mod hidden; fn main()->i64 {42}").unwrap();
    fs::write(path.join("hidden.apl"), "fn unused()->unit {let mut x=0;}").unwrap();
    let program = anl::compile_file(&source).unwrap();
    assert!(program.has_local_state());
    assert_eq!(
        core::export(&program, program.entry().unwrap()).unwrap()["schema"],
        "apl-core-v1"
    );
}
