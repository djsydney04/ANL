use anl::{
    bounded::OutputError,
    core,
    eval::{self, EvalError, ScalarValue, Trap, TupleValue, Value},
    types::{ScalarType, TupleShape, Type},
};
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture {
    dir: PathBuf,
    source: PathBuf,
}
impl Fixture {
    fn new(text: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "apl-products-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).unwrap();
        let source = dir.join("main.apl");
        fs::write(&source, text).unwrap();
        Self { dir, source }
    }
    fn command(&self, name: &str) -> Command {
        let mut c = Command::new(env!("CARGO_BIN_EXE_anl"));
        c.arg(name).arg(&self.source);
        c
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}
fn result(source: &str) -> Result<Value, EvalError> {
    let p = anl::compile(source).unwrap();
    eval::evaluate(&p, p.entry().unwrap(), 10_000_000)
}
fn source(body: &str) -> String {
    format!("fn main()->i64{{{body}}}")
}
fn native_and_core(source: &str, expected: &str, exit: i32) {
    let fixture = Fixture::new(source);
    let p = anl::compile(source).unwrap();
    let entry = p.entry().unwrap();
    let json = core::export(&p, entry).unwrap();
    assert_eq!(json["schema"], "apl-core-v2");
    let imported = core::import(&json.to_string()).unwrap();
    assert_eq!(
        core::outcome(&eval::evaluate(&p, entry, 10000)),
        core::outcome(&eval::evaluate(&imported.program, imported.entry, 10000))
    );
    let c = anl::codegen::emit_c(&p, entry).unwrap();
    let emitted = fixture.command("emit-c").output().unwrap();
    assert_eq!(emitted.status.code(), Some(0));
    assert_eq!(
        emitted.stdout,
        c.as_bytes(),
        "v2 CLI emits the exact bounded translation unit"
    );
    assert!(!c.contains("memcmp"));
    let path = fixture.dir.join("program.c");
    fs::write(&path, c).unwrap();
    for flags in [
        &["-O0"][..],
        &["-O2"],
        &[
            "-O1",
            "-fsanitize=undefined,address",
            "-fno-sanitize-recover=all",
        ],
    ] {
        let binary = fixture.dir.join("native");
        let compile = Command::new("cc")
            .arg("-std=c11")
            .args(flags)
            .arg(&path)
            .arg("-o")
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            compile.status.success(),
            "{}",
            String::from_utf8_lossy(&compile.stderr)
        );
        let actual = Command::new(&binary).output().unwrap();
        assert_eq!(actual.status.code(), Some(exit));
        let observed = if exit == 0 {
            &actual.stdout
        } else {
            &actual.stderr
        };
        assert_eq!(String::from_utf8_lossy(observed), expected, "{source}");
    }
}
#[test]
fn opaque_shapes_and_values_enforce_width_and_scalar_identity() {
    for width in [0, 9] {
        assert!(TupleShape::new(&vec![ScalarType::I64; width]).is_err());
        assert!(TupleValue::new(&vec![ScalarValue::Integer(0); width]).is_err());
    }
    for width in 1..=8 {
        let shape = TupleShape::new(&vec![ScalarType::I64; width]).unwrap();
        assert_eq!(shape.fields().len(), width);
        assert_eq!(shape, TupleShape::new(shape.fields()).unwrap());
    }
    let tuple = TupleValue::new(&[
        ScalarValue::Integer(42),
        ScalarValue::Boolean(true),
        ScalarValue::Unit,
    ])
    .unwrap();
    assert_eq!(Value::Tuple(tuple.clone()).ty(), Type::Tuple(tuple.shape()));
    assert_eq!(Value::Tuple(tuple).to_string(), "(42, true, ())");
    assert_ne!(
        Value::Integer(42),
        Value::Tuple(TupleValue::new(&[ScalarValue::Integer(42)]).unwrap())
    );
}
#[test]
fn tuple_syntax_projection_and_type_errors_are_static() {
    for (body, value) in [
        ("(42,).0", 42),
        ("(1,2,3,4,5,6,7,42,).7", 42),
        (
            "let p:(i64,bool,unit,)=(42,true,()); if p.1 {p.0} else {0}",
            42,
        ),
        ("-(42,).0", -42),
        ("let p=(42,); {p}.0", 42),
    ] {
        assert_eq!(result(&source(body)), Ok(Value::Integer(value)));
    }
    for body in [
        "(1,2,3,4,5,6,7,8,9).0",
        "((1,),).0",
        "let p=(1,); (p,).0",
        "(1,).1",
        "(1,).01",
        "(1,).-1",
        "(1,).8",
        "(1,).0.0",
        "(1,).true",
        "let mut p=(1,);p.0=2;p.0",
        "(1,) + (2,)",
        "if (true,) {1}else{0}",
        "if (1,)==(true,) {1}else{0}",
        "let p:()=();0",
        "let p:(i64)=1;0",
        "let p:((i64,),) = ((1,),);0",
    ] {
        let error = anl::compile(&source(body)).unwrap_err();
        assert!(!error.resource_limit, "{body}");
    }
    assert!(anl::compile("fn f(x:(i64,),)->i64{x.0}").is_err());
    assert!(anl::compile("fn f(x:(i64,))->i64{x.0} fn main()->i64{f((1,),)}").is_err());
}
#[test]
fn construction_projection_and_equality_preserve_effect_order_and_copies() {
    for (body, expected) in [
        ("let mut x=1;let p=({x=x+1;x},{x=x+3;x});p.0*10+p.1", 25),
        (
            "let mut p=(1,true,());let q=p;p=(9,false,());if q.1 && q.2==() {q.0*10+p.0}else{0}",
            19,
        ),
        (
            "let mut x=0;let same=({x=x+1;(1,x)})==({x=x+1;(9,x)});if same {0}else{x}",
            2,
        ),
        ("let mut p=(0,true);while ({p=(p.0+1,p.0<2);p.1}) {} p.0", 3),
        ("if (1,true,())==(1,true,()) && (1,)!=(2,) {42}else{0}", 42),
    ] {
        let s = source(body);
        assert_eq!(result(&s), Ok(Value::Integer(expected)));
        native_and_core(&s, &format!("{expected}\n"), 0);
    }
    for (body, trap) in [
        ("(7,1/0).0", Trap::DivisionByZero),
        ("(9223372036854775807+1,1/0).1", Trap::ArithmeticOverflow),
        ("(1/0,9223372036854775807+1).1", Trap::DivisionByZero),
    ] {
        let s = source(body);
        assert!(matches!(result(&s),Err(EvalError::Trap{kind,..}) if kind==trap));
        native_and_core(&s, &format!("{}\n", trap.as_str()), 2);
    }
}
#[test]
fn call_capture_recursion_and_tuple_results_use_value_semantics() {
    let s = "fn f(a:(i64,),b:(i64,))->(i64,bool){(a.0*10+b.0,true)} fn recurse(p:(i64,))->(i64,){if p.0==0 {(1,)}else{let q=recurse((p.0-1,));(q.0+p.0,)}} fn main()->i64{let mut p=(1,);let r=f(p,{p=(9,);p});r.0+recurse((4,)).0}";
    assert_eq!(result(s), Ok(Value::Integer(30)));
    native_and_core(s, "30\n", 0);
}
fn literal(n: &str) -> serde_json::Value {
    serde_json::json!({"tag":"integer","ty":"i64","value":n})
}
fn expression(expr: serde_json::Value) -> serde_json::Value {
    serde_json::json!({"schema":"apl-expr-v2","semantic_revision":"flat-products-2026-11-17","expression":expr})
}
#[test]
fn strict_v2_artifacts_have_exact_types_values_and_scalar_normalization() {
    let tuple = serde_json::json!({"tag":"tuple","ty":{"tuple":["i64","bool","unit"]},"fields":[literal("42"),{"tag":"boolean","ty":"bool","value":true},{"tag":"unit","ty":"unit"}]});
    let valid = expression(tuple.clone());
    let a = core::import(&valid.to_string()).unwrap();
    assert_eq!(
        core::outcome(&eval::evaluate(&a.program, a.entry, 100)),
        serde_json::json!({"outcome":"value","type":{"tuple":["i64","bool","unit"]},"value":["42",true,null]})
    );
    for index in [
        serde_json::json!(0),
        serde_json::json!(1),
        serde_json::json!(2),
    ] {
        let ty = ["i64", "bool", "unit"][index.as_u64().unwrap() as usize];
        let a = core::import(
            &expression(serde_json::json!({"tag":"project","ty":ty,"value":tuple,"index":index}))
                .to_string(),
        )
        .unwrap();
        assert!(eval::evaluate(&a.program, a.entry, 100).is_ok());
    }
    for index in [
        serde_json::json!(3),
        serde_json::json!(8),
        serde_json::json!(-1),
        serde_json::json!(0.0),
        serde_json::json!("0"),
        serde_json::json!(true),
    ] {
        assert!(
            core::import(
                &expression(
                    serde_json::json!({"tag":"project","ty":"i64","value":tuple,"index":index})
                )
                .to_string()
            )
            .is_err()
        );
    }
    let mut invalid = Vec::new();
    for fields in [serde_json::json!([]), serde_json::json!(vec!["i64"; 9])] {
        let mut v = valid.clone();
        v["expression"]["ty"]["tuple"] = fields;
        invalid.push(v);
    }
    let mut v = valid.clone();
    v["expression"]["ty"]["tuple"][0] = serde_json::json!({"tuple":["i64"]});
    invalid.push(v);
    let mut v = valid.clone();
    v["expression"]["fields"][0] = tuple.clone();
    invalid.push(v);
    let mut v = valid.clone();
    v["expression"]["fields"][0]["ty"] = serde_json::json!("bool");
    invalid.push(v);
    let mut v = valid.clone();
    v["expression"]["extra"] = serde_json::json!(true);
    invalid.push(v);
    for version in ["0", "1"] {
        let mut v = valid.clone();
        v["schema"] = serde_json::json!(format!("apl-expr-v{version}"));
        v["semantic_revision"] = serde_json::json!(if version == "0" {
            core::SEMANTIC_REVISION
        } else {
            core::LOCAL_STATE_SEMANTIC_REVISION
        });
        invalid.push(v);
    }
    for v in invalid {
        assert!(core::import(&v.to_string()).is_err(), "{v}");
    }
    let p = anl::compile("fn main()->i64{42}").unwrap();
    let mut wire = core::export(&p, 0).unwrap();
    wire["schema"] = serde_json::json!("apl-core-v2");
    wire["semantic_revision"] = serde_json::json!(core::FLAT_PRODUCTS_SEMANTIC_REVISION);
    let a = core::import(&wire.to_string()).unwrap();
    assert!(!a.program.has_flat_products());
    assert_eq!(
        core::export(&a.program, a.entry).unwrap()["schema"],
        "apl-core-v0"
    );
}
#[test]
fn tuple_fuel_counts_only_executed_constructors() {
    let p = anl::compile(&source("(42,true).0")).unwrap();
    assert!(matches!(
        eval::evaluate(&p, 0, 3),
        Err(EvalError::ResourceLimit { .. })
    ));
    assert_eq!(eval::evaluate(&p, 0, 4), Ok(Value::Integer(42)));
    let p = anl::compile(&source("if true {42}else{(1/0,).0}")).unwrap();
    assert_eq!(eval::evaluate(&p, 0, 3), Ok(Value::Integer(42)));
}
#[test]
fn real_tuple_churn_charges_cumulative_allocations_without_retaining_old_values() {
    let p = anl::compile(&source(
        "let mut i=0;let mut p=(0,0,0,0,0,0,0,0);while(i<131071){p=(i,i,i,i,i,i,i,i);i=i+1;}p.0",
    ))
    .unwrap();
    assert_eq!(
        eval::evaluate(&p, 0, 10_000_000),
        Ok(Value::Integer(131070))
    );
    let p = anl::compile(&source(
        "let mut i=0;let mut p=(0,0,0,0,0,0,0,0);while(i<131072){p=(i,i,i,i,i,i,i,i);i=i+1;}p.0",
    ))
    .unwrap();
    assert!(
        matches!(eval::evaluate(&p,0,10_000_000),Err(EvalError::ResourceLimit{reason,..}) if reason.contains("tuple allocation"))
    );
}
#[test]
fn aggregate_verification_precedes_solver_and_other_unsupported_routes() {
    for s in [
        "fn unused(x:(i64,))->unit{} fn main()->i64{42}",
        "fn main()->i64{if true{42}else{(0,).0}}",
        "fn f(x:bool)->i64{if x {1}else{f(x)}} fn main()->i64{let p=(1,);f(false)}",
        "fn main()->i64{let p=(1,);while(false){}p.0}",
        "fn f(p:(i64,),x:i64)->(bool,) requires x>0; ensures (r) x>0; {(true,)} fn main()->i64{42}",
        "fn main()->i64{let mut x=0;let p=(1,);while(x<2) invariant x>=0;{x=x+1;}x}",
    ] {
        let f = Fixture::new(s);
        let marker = f.dir.join("solver-ran");
        let solver = f.dir.join("solver");
        fs::write(
            &solver,
            format!("#!/bin/sh\ntouch '{}'\nexit 1\n", marker.display()),
        )
        .unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&solver, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let r = f
            .command("verify")
            .arg("--solver")
            .arg(&solver)
            .arg("--json")
            .output()
            .unwrap();
        assert_eq!(
            r.status.code(),
            Some(7),
            "{}",
            String::from_utf8_lossy(&r.stderr)
        );
        assert!(!marker.exists());
        let report: serde_json::Value = serde_json::from_slice(&r.stdout).unwrap();
        assert_eq!(report["schema"], "apl-verify-v2");
        assert_eq!(
            report["verification_revision"],
            "apl-flat-products-unsupported-v1"
        );
        assert_eq!(report["solver"], serde_json::Value::Null);
        assert_eq!(report["obligations"], serde_json::json!([]));
        assert_eq!(report["type_checked"], true);
        assert_eq!(report["scope"]["arithmetic_safety"], false);
    }
    for s in [
        "fn f(p:(i64,))->unit requires p==p; {}",
        "fn f()->(i64,) ensures (r) r==r; {(1,)}",
        "fn main()->i64{let p=(1,);while(false) invariant p==p;{}0}",
        "fn f()->i64 requires (1,).0==1; {1}",
    ] {
        assert!(anl::compile(s).is_err());
    }
}
#[test]
fn oversized_v2_json_fails_without_publishing_a_prefix() {
    let mut s = String::from("fn product()->(i64,){(1,)}");
    for i in 0..700 {
        s.push_str(&format!(
            "fn f{i}()->i64{{{} }}",
            (0..50).map(|_| "1").collect::<Vec<_>>().join("+")
        ));
    }
    s.push_str("fn main()->i64{42}");
    let f = Fixture::new(&s);
    let p = anl::compile(&s).unwrap();
    assert!(matches!(
        core::export(&p, p.entry().unwrap()),
        Err(OutputError::ResourceLimit(_))
    ));
    let r = f.command("dump-core").output().unwrap();
    assert_eq!(r.status.code(), Some(3));
    assert!(r.stdout.is_empty());
}

#[test]
fn wide_recursive_calls_reach_slot_limit_before_host_depth_or_unbounded_reservation() {
    let params = (0..3000)
        .map(|i| format!("x{i}:i64"))
        .collect::<Vec<_>>()
        .join(",");
    let args = (0..3000)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let initial = vec!["0"; 3000].join(",");
    let s = format!("fn f({params})->i64{{f({args})}} fn main()->i64{{let p=(1,);f({initial})}}");
    let p = anl::compile(&s).unwrap();
    assert!(
        matches!(eval::evaluate(&p,p.entry().unwrap(),10_000_000),Err(EvalError::ResourceLimit{reason,..}) if reason.contains("slot"))
    );
}
#[test]
fn unused_imported_products_are_checked_and_reject_before_solver_discovery() {
    let f = Fixture::new("mod hidden;fn main()->i64{42}");
    fs::write(
        f.dir.join("hidden.apl"),
        "fn unused(p:(i64,bool))->unit requires true; {}",
    )
    .unwrap();
    let r = f
        .command("verify")
        .args(["--solver", "/definitely/not/a/solver", "--json"])
        .output()
        .unwrap();
    assert_eq!(r.status.code(), Some(7));
    let report: serde_json::Value = serde_json::from_slice(&r.stdout).unwrap();
    assert_eq!(report["schema"], "apl-verify-v2");
    assert_eq!(report["sources"].as_array().unwrap().len(), 2);
    fs::write(
        f.dir.join("hidden.apl"),
        "fn unused(p:(i64,bool))->unit requires p==p; {}",
    )
    .unwrap();
    let r = f
        .command("verify")
        .args(["--solver", "/definitely/not/a/solver", "--json"])
        .output()
        .unwrap();
    assert_eq!(r.status.code(), Some(1));
}
