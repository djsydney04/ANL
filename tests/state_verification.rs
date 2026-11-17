//! Real solver evidence for loop-free mutable state; no model-to-Rust proof claim.
use apl::eval::{self, Value as Scalar};
use serde_json::{Value, json};
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
    time::{Duration, Instant},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "apl-state-verify-{}-{}",
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
    fn verify(&self, source: &str) -> (Output, Value) {
        verify(&self.file("main.apl", source), 30_000)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn solver() -> PathBuf {
    std::env::var_os("APL_TEST_SOLVER")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let local = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join(".tools/z3-5.3.3-arm64-osx-13.3/bin/z3");
            if local.is_file() { local } else { "z3".into() }
        })
}
fn verify(source: &Path, timeout: u64) -> (Output, Value) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_apl"));
    command
        .arg("verify")
        .arg(source)
        .arg("--solver")
        .arg(solver())
        .arg("--timeout-ms")
        .arg(timeout.to_string())
        .arg("--json");
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    let mut stderr = child.stderr.take().unwrap();
    let out = thread::spawn(move || {
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes).unwrap();
        bytes
    });
    let err = thread::spawn(move || {
        let mut bytes = Vec::new();
        stderr.read_to_end(&mut bytes).unwrap();
        bytes
    });
    let deadline = Instant::now() + Duration::from_millis(timeout + 10_000);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            #[cfg(unix)]
            {
                use nix::{
                    sys::signal::{Signal, killpg},
                    unistd::Pid,
                };
                let _ = killpg(Pid::from_raw(child.id() as i32), Signal::SIGKILL);
            }
            let _ = child.kill();
            let _ = child.wait();
            panic!("state verification exceeded its process deadline");
        }
        thread::sleep(Duration::from_millis(2));
    };
    let output = Output {
        status,
        stdout: out.join().unwrap(),
        stderr: err.join().unwrap(),
    };
    let report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("invalid report {e}: {output:?}"));
    (output, report)
}
fn status(output: &Output, report: &Value, code: i32, expected: &str) {
    assert_eq!(output.status.code(), Some(code), "{report}");
    assert_eq!(report["status"], expected, "{report}");
    assert_eq!(report["schema"], "apl-verify-v1");
    assert_eq!(report["verification_revision"], "apl-state-verify-v1");
    assert_eq!(report["semantic_revision"], "local-state-2026-11-17");
}
fn evaluates(source: &str, expected: i64) {
    let program = apl::compile(source).unwrap();
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100_000),
        Ok(Scalar::Integer(expected)),
        "{source}"
    );
}

#[test]
fn mutable_state_queries_agree_with_independent_finite_outcomes() {
    let cases = [
        ("let mut x=1;{x=x+2;};x", 3),
        ("let mut x=1;let old=x;x=3;old*10+x", 13),
        ("let mut x=1;let a={x=3;x}+{x=x+4;x};a*10+x", 107),
        ("let mut x=1;x={let mut y=9;x=x+2;let z=y;x+z};x", 12),
        ("let mut x=1;let y={x=5;x};x+y", 10),
        ("let mut x=0;if {x=1;true} {x=x+2;}else{x=9;};x", 3),
        (
            "let mut x=0;false && {x=1;1/0==0};true || {x=2;1/0==0};x",
            0,
        ),
        (
            "let mut x=0;{x=1;true} && {x=x+2;true};{x=x+3;false} || {x=x+4;true};x",
            10,
        ),
        (
            "let mut b=false;let mut u=();b=true;u=();if b && u==() {42}else{0}",
            42,
        ),
        (
            "let mut x=1;let r=pack({x=x+1;x},{x=x*3;x},{x=x+1;x});r*10+x",
            2677,
        ),
        ("let mut x=7;let r=change(x,x);r*10+x", 1067),
        ("let mut x=0;if false {x=1/0;}else{x=42;};x", 42),
    ];
    let mut source = String::from(
        "fn pack(a:i64,b:i64,c:i64)->i64 requires a>=0 && a<=10;requires b>=0 && b<=10;requires c>=0 && c<=10;{100*a+10*b+c}\nfn change(a:i64,b:i64)->i64 requires b>=0 && b<=100;{let mut a=a;a=99;a+b}\n",
    );
    for (i, (body, expected)) in cases.iter().enumerate() {
        source.push_str(&format!(
            "fn f{i}()->i64 ensures(r)r=={expected};{{{body}}}\n"
        ));
    }
    for (i, (_, expected)) in cases.iter().enumerate() {
        evaluates(&format!("{source}fn main()->i64{{f{i}()}}"), *expected);
    }
    let (output, report) = Fixture::new().verify(&source);
    status(&output, &report, 0, "verified");
}

#[test]
fn symbolic_branch_merges_and_posts_keep_original_entry_parameters() {
    let source = "fn f(p:bool,a:i64,u:unit)->i64 requires a>=0 && a<=10;ensures(r)(p && r==a+3)||(!p && r==a+5);{let mut a=a;a=a+1;if p {a=a+2;}else{a=a+4;};a}\nfn g(p:bool)->i64 ensures(r)(p && r==13)||(!p && r==23);{let mut x=0;let old=if p{x=1;x}else{x=2;x};x=3;old*10+x}";
    for p in [false, true] {
        for a in [0, 3, 10] {
            evaluates(
                &format!("{source}fn main()->i64{{f({p},{a},())}}"),
                a + if p { 3 } else { 5 },
            );
        }
        evaluates(
            &format!("{source}fn main()->i64{{g({p})}}"),
            if p { 13 } else { 23 },
        );
    }
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 0, "verified");
}

#[test]
fn unsafe_mutations_and_callee_contracts_are_never_assumed_away() {
    let source = "fn overflow()->i64{let mut x=9223372036854775807;x=x+1;x=x-1;x}\nfn divided()->i64{let mut x=1;if true{x=0;}else{};1/x}\nfn positive(x:i64)->i64 requires x>0;{x}\nfn caller()->i64{let mut x=1;x=-1;positive(x)}\nfn liar(x:i64)->i64 ensures(r)r==0;{x}\nfn assumed()->i64 ensures(r)r==0;{let mut x=0;x=1;liar(x)}\nfn independent()->i64 ensures(r)r!=0;ensures(r)1/r==1;{let mut x=1;x=0;x}\nfn main()->i64{42}";
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 5, "failed");
    for (function, kind) in [
        ("overflow", "body_safe"),
        ("divided", "body_safe"),
        ("caller", "body_safe"),
        ("liar", "postcondition"),
        ("assumed", "postcondition"),
        ("independent", "postcondition"),
    ] {
        assert!(
            report["obligations"]
                .as_array()
                .unwrap()
                .iter()
                .any(|q| q["function"] == function && q["kind"] == kind && q["status"] == "failed"),
            "missing failure for {function}: {report}"
        );
    }
    assert_eq!(report["functions"].as_array().unwrap().len(), 8);
}

#[test]
fn state_reports_bind_complete_parameter_models_and_checked_error_envelopes() {
    let fixture = Fixture::new();
    let (output, report) = fixture.verify(
        "fn f(x:i64,unused:bool,u:unit)->i64 requires x==0;ensures(r)r==2;{let mut y=x;y=1;y}",
    );
    status(&output, &report, 5, "failed");
    let keys: std::collections::BTreeSet<_> = report
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect();
    assert_eq!(
        keys,
        [
            "schema",
            "verification_revision",
            "semantic_revision",
            "status",
            "trust",
            "scope",
            "type_checked",
            "tested",
            "dynamic_checks",
            "contracts_erased",
            "limits",
            "compiler",
            "solver",
            "sources",
            "functions",
            "obligations",
            "message",
            "expanded_nodes"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(report["scope"]["fragment"], "loop_free_local_state_acyclic");
    assert_eq!(report["limits"]["symbolic_work"], 1_000_000);
    assert_eq!(report["limits"]["arena_nodes"], 100_000);
    assert!(report["limits"].get("head_symbols").is_none());
    for obligation in report["obligations"].as_array().unwrap() {
        assert_eq!(
            obligation["model_symbols"],
            json!([
                {"symbol":"p0","type":"i64","origin":{"kind":"parameter","index":0}},
                {"symbol":"p1","type":"bool","origin":{"kind":"parameter","index":1}}
            ])
        );
        if obligation["solver_status"] == "sat" {
            let assignments = obligation["model"]["assignments"].as_array().unwrap();
            assert_eq!(assignments.len(), 2);
            assert_eq!(assignments[0]["parameter"], 0);
            assert_eq!(assignments[1]["parameter"], 1);
            assert_eq!(obligation["model"]["replayed"], false);
        }
    }
    let invalid = fixture.file("bad.apl", "fn f()->i64{let mut x=false;x}");
    let (_, invalid) = verify(&invalid, 30_000);
    assert_eq!(invalid["schema"], "apl-verify-v0");
    assert!(invalid["semantic_revision"].is_null());
    assert!(invalid.get("verification_revision").is_none());
    let bad_options = Command::new(env!("CARGO_BIN_EXE_apl"))
        .arg("verify")
        .arg(fixture.0.join("main.apl"))
        .args(["--timeout-ms", "0", "--json"])
        .output()
        .unwrap();
    assert_eq!(bad_options.status.code(), Some(4));
    assert!(bad_options.stdout.is_empty());
    assert!(!bad_options.stderr.is_empty());
    let error = apl::verify::verify_file(
        fixture.0.join("absent.apl"),
        &apl::verify::VerifyOptions {
            solver: solver(),
            timeout_ms: 0,
        },
    )
    .unwrap_err();
    let report = apl::verify::VerificationReport::source_error(&error);
    assert_eq!(report.json()["schema"], "apl-verify-v0");
    assert!(report.json()["semantic_revision"].is_null());
    assert!(report.json().get("verification_revision").is_none());
}

#[test]
fn many_parameter_branch_merges_exhaust_work_before_unbounded_allocation() {
    let fixture = Fixture::new();
    let params = (0..8000)
        .map(|i| format!("p{i}:unit"))
        .collect::<Vec<_>>()
        .join(",");
    let source = format!(
        "fn f({params})->i64{{let mut x=0;{}x}}",
        "if true {}else{};".repeat(95)
    );
    let path = fixture.file("wide.apl", &source);
    let started = Instant::now();
    let (output, report) = verify(&path, 10_000);
    status(&output, &report, 6, "unknown");
    assert!(
        report["message"]
            .as_str()
            .unwrap()
            .contains("symbolic work"),
        "{report}"
    );
    assert!(report["expanded_nodes"].as_u64().unwrap() > 0);
    assert!(report["obligations"].as_array().unwrap().is_empty());
    assert!(started.elapsed() < Duration::from_secs(15));
}

#[test]
fn unused_cross_module_mutation_is_checked_with_the_complete_graph() {
    let fixture = Fixture::new();
    fixture.file("helper.apl", "pub fn value()->i64 ensures(r)r==42;{let mut x=40;x=x+2;x} fn unused()->i64{let mut x=1;x=0;1/x}");
    let source = fixture.file(
        "main.apl",
        "mod helper;fn main()->i64 ensures(r)r==42;{helper::value()}",
    );
    let (output, report) = verify(&source, 30_000);
    status(&output, &report, 5, "failed");
    assert_eq!(report["sources"].as_array().unwrap().len(), 2);
    assert!(
        report["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|q| q["function"] == "unused"
                && q["kind"] == "body_safe"
                && q["status"] == "failed"),
        "{report}"
    );
}
