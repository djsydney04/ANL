use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "apl-verify-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn file(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }
    fn verify(&self, source: &str) -> (Output, Value) {
        let path = self.file("main.apl", source);
        verify(&path, &solver(), 30_000)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn solver() -> PathBuf {
    if let Some(path) =
        std::env::var_os("ANL_TEST_SOLVER").or_else(|| std::env::var_os("APL_TEST_SOLVER"))
    {
        return path.into();
    }
    let local =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".tools/z3-5.3.3-arm64-osx-13.3/bin/z3");
    if local.is_file() { local } else { "z3".into() }
}
fn verify(path: &Path, solver: &Path, timeout: u64) -> (Output, Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_anl"))
        .arg("verify")
        .arg(path)
        .arg("--solver")
        .arg(solver)
        .arg("--timeout-ms")
        .arg(timeout.to_string())
        .arg("--json")
        .output()
        .unwrap();
    let report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("invalid report {e}: {output:?}"));
    (output, report)
}
fn status(output: &Output, report: &Value, code: i32, name: &str) {
    assert_eq!(output.status.code(), Some(code), "{report}");
    assert_eq!(report["status"], name, "{report}");
    assert_eq!(report["schema"], "apl-verify-v0");
}
#[test]
fn real_solver_checks_contracts_arithmetic_scopes_and_heterogeneous_parameters() {
    let fixture = Fixture::new();
    let (output, report) = fixture.verify("fn inc(x:i64)->i64 requires x<9223372036854775807; ensures(r) r==x+1; {x+1} fn main()->i64 ensures(r)r==42;{inc(41)}");
    status(&output, &report, 0, "verified");
    assert_eq!(report["semantic_revision"], "m1-2026-11-16");
    for source in [
        "fn same(p:bool,x:i64,u:unit)->i64 ensures(r)r==x;{let y={let x=7;x};let z=if p {()}else{()};x} fn main()->i64 ensures(r)r==42;{same(false,42,())}",
        "fn f(x:i64)->i64 requires x!=0; requires 10/x>1; ensures(r)r==10/x;{10/x}",
        "fn f()->i64 ensures(r) -9223372036854775808 / -1 == 9223372036854775808; ensures(r) -9223372036854775808 % -1 == 0; {42}",
        "fn f(x:i64)->bool ensures(r) r==false; {false && (1/0==x)} fn g()->bool ensures(r)r;{true || (1/0==0)}",
        "fn f(x:i64)->i64 ensures(r) r==x; {if false {1/0}else{x}}",
        "fn f()->unit ensures(r) r==(); {()}",
    ] {
        let (o, r) = fixture.verify(source);
        status(&o, &r, 0, "verified");
    }
}
#[test]
fn real_solver_rejects_false_vacuous_undefined_and_overflowing_properties() {
    let fixture = Fixture::new();
    for (source, kind) in [
        ("fn f(x:i64)->i64 ensures(r)r==x+1;{x}", "postcondition"),
        ("fn f(x:i64)->i64{(x+1)-1}", "body_safe"),
        ("fn f()->i64{-9223372036854775808/-1}", "body_safe"),
        ("fn f()->i64{-9223372036854775808%-1}", "body_safe"),
        ("fn f(x:i64)->i64{1/x}", "body_safe"),
        (
            "fn f(x:i64)->i64 requires x>0; requires x<0; {x}",
            "precondition_satisfiable",
        ),
        (
            "fn f(x:i64)->i64 requires 1/x==0; requires x!=0; {x}",
            "precondition_defined",
        ),
        (
            "fn f(x:i64)->i64 requires 1/0==0; {x}",
            "precondition_defined",
        ),
        (
            "fn f(x:i64)->i64 ensures(r)r!=0; ensures(r)1/r==1;{x}",
            "postcondition",
        ),
        (
            "fn helper(x:i64)->i64 requires x>0;{x} fn main()->i64{helper(0)}",
            "body_safe",
        ),
        (
            "fn helper(x:i64)->i64 ensures(r)r==0;{x} fn main()->i64 ensures(r)r==0;{helper(1)}",
            "postcondition",
        ),
        ("fn main()->i64{let ignored=1/0;42}", "body_safe"),
    ] {
        let (o, r) = fixture.verify(source);
        status(&o, &r, 5, "failed");
        assert!(
            r["obligations"]
                .as_array()
                .unwrap()
                .iter()
                .any(|q| q["kind"] == kind && q["status"] == "failed"),
            "{r}"
        );
    }
}
#[test]
fn signed_division_and_remainder_use_independent_expected_results() {
    let fixture = Fixture::new();
    let mut source = String::new();
    for (i, (a, b, q, m)) in [
        (-7, 3, -2, -1),
        (7, -3, -2, 1),
        (-7, -3, 2, -1),
        (7, 3, 2, 1),
        (-8, 3, -2, -2),
        (8, -3, -2, 2),
    ]
    .iter()
    .enumerate()
    {
        source.push_str(&format!(
            "fn f{i}()->i64 ensures(r)r=={q}; ensures(r){a}%{b}=={m};{{{a}/{b}}}\n"
        ));
    }
    let (o, r) = fixture.verify(&source);
    status(&o, &r, 0, "verified");
}
#[test]
fn modules_models_and_artifact_bindings_use_the_inspected_source_snapshot() {
    let fixture = Fixture::new();
    let root = fixture.file(
        "main.apl",
        "mod helper; fn main()->i64 ensures(r)r==42;{helper::value(41)}",
    );
    let helper = fixture.file(
        "helper.apl",
        "pub fn value(x:i64)->i64 requires x<9223372036854775807; ensures(r)r==x+1;{x+1}",
    );
    let (o, r) = verify(&root, &solver(), 30_000);
    status(&o, &r, 0, "verified");
    assert_eq!(r["sources"].as_array().unwrap().len(), 2);
    assert_eq!(r["trust"], "smt-trusted");
    assert_eq!(r["dynamic_checks"], false);
    assert_eq!(r["tested"], false);
    for item in r["obligations"].as_array().unwrap() {
        assert_eq!(item["query_sha256"].as_str().unwrap().len(), 64);
    }
    fs::write(
        &helper,
        "pub fn value(x:i64)->i64 requires x<9223372036854775807; ensures(r)r==x+1;{x}",
    )
    .unwrap();
    let (o, changed) = verify(&root, &solver(), 30_000);
    status(&o, &changed, 5, "failed");
    assert_ne!(r["sources"][1]["sha256"], changed["sources"][1]["sha256"]);
    let (o, bad) = fixture.verify("fn f(x:i64)->i64 ensures(r)r==x+1;{x}");
    status(&o, &bad, 5, "failed");
    let model = &bad["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["status"] == "failed")
        .unwrap()["model"];
    assert_eq!(model["replayed"], false);
    assert_eq!(model["assignments"][0]["parameter"], 0);
    assert!(
        model["assignments"][0]["value"]
            .as_str()
            .unwrap()
            .parse::<i64>()
            .is_ok()
    );
}
#[test]
fn unsupported_empty_source_errors_and_missing_tools_never_succeed() {
    let fixture = Fixture::new();
    let missing = fixture.0.join("no-solver");
    for source in [
        "fn f()->i64{f()}",
        "fn f()->i64{g()} fn g()->i64{f()} fn main()->i64{42}",
        "fn f()->i64{if false{f()}else{42}}",
    ] {
        let path = fixture.file("main.apl", source);
        let (o, r) = verify(&path, &missing, 30_000);
        status(&o, &r, 7, "unsupported");
        assert!(r["obligations"].as_array().unwrap().is_empty());
    }
    let path = fixture.file("main.apl", "");
    let (o, r) = verify(&path, &missing, 30_000);
    status(&o, &r, 7, "not_requested");
    let path = fixture.file("main.apl", "fn main()->i64{false}");
    let (o, r) = verify(&path, &missing, 30_000);
    status(&o, &r, 1, "error");
    assert_eq!(r["type_checked"], false);
    assert!(r["semantic_revision"].is_null());
    let path = fixture.file("main.apl", "fn main()->i64{42}");
    let (o, r) = verify(&path, &missing, 30_000);
    status(&o, &r, 4, "error");
    let (o, r) = verify(&fixture.0.join("missing.apl"), &missing, 30_000);
    status(&o, &r, 4, "error");
}
#[test]
#[cfg(unix)]
fn loop_preflight_rejects_unused_dead_and_recursive_state_without_starting_solver() {
    use std::os::unix::fs::PermissionsExt;
    let fixture = Fixture::new();
    let marker = fixture.0.join("invoked");
    let solver = fixture.file(
        "solver",
        &format!(
            "#!/bin/sh\nprintf invoked > '{}'\nexit 99\n",
            marker.display()
        ),
    );
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    for (source, construct) in [
        ("fn main()->i64 {let mut x=42;while (false) {} x}", "while"),
        (
            "fn main()->i64 {42} fn unused()->i64 {let mut x=0;while (false) {x=1;}x}",
            "while",
        ),
        (
            "fn main()->i64 {if false {let mut x=0;while (true) {} x}else{42}}",
            "while",
        ),
        ("fn main()->i64 {while (false) {} 42}", "while"),
        (
            "fn main()->i64 {if true {42}else{while (true) {} 0}}",
            "while",
        ),
        (
            "fn main()->i64 {42} fn unused()->unit {while (true) {}}",
            "while",
        ),
        ("fn main()->i64 {let mut x=0;x=main();x}", "recursive"),
        (
            "fn main()->i64 {let mut x=0;x} fn unused()->i64 {unused()}",
            "recursive",
        ),
    ] {
        let path = fixture.file("main.apl", source);
        let (output, report) = verify(&path, &solver, 30_000);
        assert_eq!(output.status.code(), Some(7), "{report}");
        assert_eq!(report["status"], "unsupported");
        assert_eq!(report["schema"], "apl-verify-v1");
        assert_eq!(
            report["verification_revision"],
            if construct == "while" {
                "apl-loop-verify-v1"
            } else {
                "apl-state-verify-v1"
            }
        );
        assert_eq!(report["expanded_nodes"], 0);
        assert_eq!(report["semantic_revision"], "local-state-2026-11-17");
        assert!(
            report["message"].as_str().unwrap().contains(construct),
            "{report}"
        );
        assert_eq!(report["type_checked"], true);
        assert!(report["compiler"].is_null());
        assert!(report["solver"].is_null());
        assert!(report["obligations"].as_array().unwrap().is_empty());
        assert!(!marker.exists(), "unsupported program started a solver");
    }
    let path = fixture.file("main.apl", "mod helper; fn main()->i64 {42}");
    fixture.file("helper.apl", "fn unused()->unit {while (false) {}}");
    let (output, report) = verify(&path, &solver, 30_000);
    assert_eq!(output.status.code(), Some(7), "{report}");
    assert_eq!(report["status"], "unsupported");
    assert_eq!(report["schema"], "apl-verify-v1");
    assert_eq!(report["verification_revision"], "apl-loop-verify-v1");
    assert_eq!(report["expanded_nodes"], 0);
    assert_eq!(report["semantic_revision"], "local-state-2026-11-17");
    assert_eq!(report["sources"].as_array().unwrap().len(), 2);
    assert!(report["obligations"].as_array().unwrap().is_empty());
    assert!(!marker.exists());
}

#[test]
#[cfg(unix)]
fn invalid_invariants_keep_the_source_error_envelope_without_solver_discovery() {
    use std::os::unix::fs::PermissionsExt;
    let fixture = Fixture::new();
    let marker = fixture.0.join("invoked");
    let solver = fixture.file(
        "solver",
        &format!(
            "#!/bin/sh\nprintf invoked > '{}'\nexit 99\n",
            marker.display()
        ),
    );
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    for (source, message, code) in [
        (
            "fn main()->i64 {while(false) invariant 1; {}42}".to_owned(),
            "must have type bool",
            1,
        ),
        (
            "fn main()->i64 {42} fn unused()->unit {while(false) invariant unknown; {}}".to_owned(),
            "undefined invariant name",
            1,
        ),
        (
            "fn main()->i64 {while(false) invariant true {}42}".to_owned(),
            "; after invariant clause",
            1,
        ),
        (
            format!(
                "fn main()->i64 {{while(false) invariant {}==0; {{}}42}}",
                "9".repeat(4097)
            ),
            "4096 decimal digits",
            3,
        ),
    ] {
        let path = fixture.file("main.apl", &source);
        let (output, report) = verify(&path, &solver, 30_000);
        status(&output, &report, code, "error");
        assert!(report["semantic_revision"].is_null(), "{report}");
        assert!(report.get("verification_revision").is_none(), "{report}");
        assert_eq!(report["type_checked"], false);
        assert!(report["compiler"].is_null());
        assert!(report["solver"].is_null());
        assert!(report["obligations"].as_array().unwrap().is_empty());
        assert!(
            report["message"].as_str().unwrap().contains(message),
            "{report}"
        );
        assert!(!marker.exists(), "ill-typed annotation started a solver");
    }
}

#[cfg(unix)]
fn fake(fixture: &Fixture, mode: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = fixture.file(
        "solver.py",
        &format!(
            r#"#!/usr/bin/python3
import sys,time,subprocess,os
mode={mode:?}
if sys.argv[1:]==['-version']:
 print('Z3 version 5.3.3 - controlled protocol substitute');sys.exit(0)
for line in sys.stdin:
 if line.startswith('(check-sat'):
  if mode=='hang':time.sleep(60)
  elif mode=='huge':print('x'*1048577,flush=True)
  elif mode=='extra':print('unsat\nsat',flush=True)
  elif mode=='crash':print('unsat',flush=True);sys.exit(9)
  elif mode=='stderr':print('unexpected',file=sys.stderr,flush=True);print('unsat',flush=True)
  elif mode=='model':print('sat',flush=True)
  else:print('unknown',flush=True)
 elif line.startswith('(get-value'):
  print('((p0 true))',flush=True)
 elif line.startswith('(exit'):
  if mode=='fifo':os.unlink(sys.argv[0]);os.mkfifo(sys.argv[0])
  if mode=='descendant':subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'])
  break
"#
        ),
    );
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    path
}
#[test]
#[cfg(unix)]
fn solver_protocol_rejects_errors_crashes_extra_output_and_malformed_models() {
    let fixture = Fixture::new();
    let source = fixture.file("main.apl", "fn f(x:i64)->i64{x}");
    for mode in ["extra", "crash", "stderr", "huge", "model"] {
        let executable = fake(&fixture, mode);
        let (o, r) = verify(&source, &executable, 10_000);
        status(&o, &r, 4, "error");
    }
    let executable = fake(&fixture, "unknown");
    let (o, r) = verify(&source, &executable, 10_000);
    status(&o, &r, 6, "unknown");
}
#[test]
#[cfg(unix)]
fn state_solver_failures_retain_revision_and_attempted_model_manifest() {
    let fixture = Fixture::new();
    let source = fixture.file("main.apl", "fn f(x:i64)->i64{let mut y=x;y}");
    let (output, report) = verify(&source, &fixture.0.join("missing"), 30_000);
    assert_eq!(output.status.code(), Some(4));
    assert_eq!(report["schema"], "apl-verify-v1");
    assert_eq!(report["verification_revision"], "apl-state-verify-v1");
    assert_eq!(report["expanded_nodes"], 0);
    assert!(report["solver"].is_null());
    assert!(report["obligations"].as_array().unwrap().is_empty());
    for (mode, code) in [("model", 4), ("unknown", 6)] {
        let (output, report) = verify(&source, &fake(&fixture, mode), 10_000);
        assert_eq!(output.status.code(), Some(code), "{report}");
        assert_eq!(report["schema"], "apl-verify-v1");
        assert_eq!(report["verification_revision"], "apl-state-verify-v1");
        assert!(report["expanded_nodes"].as_u64().unwrap() > 0);
        let obligations = report["obligations"].as_array().unwrap();
        assert!(!obligations.is_empty());
        for obligation in obligations {
            assert_eq!(
                obligation["model_symbols"],
                serde_json::json!([
                    {"symbol":"p0","type":"i64","origin":{"kind":"parameter","index":0}}
                ])
            );
            assert_eq!(obligation["query_sha256"].as_str().unwrap().len(), 64);
            assert_eq!(obligation["query_complete"], mode == "unknown");
        }
    }
}

#[test]
#[cfg(unix)]
fn deadline_bounds_hanging_solvers_and_descendant_held_pipes() {
    let fixture = Fixture::new();
    let source = fixture.file("main.apl", "fn f()->i64{42}");
    for mode in ["hang", "descendant"] {
        let executable = fake(&fixture, mode);
        let start = Instant::now();
        let (o, r) = verify(&source, &executable, 5000);
        status(&o, &r, 6, "unknown");
        assert!(
            !r["obligations"].as_array().unwrap().is_empty(),
            "deadline test did not reach a query: {r}"
        );
        assert!(start.elapsed() < Duration::from_secs(10), "{r}");
    }
}

#[test]
fn acyclic_expansion_limits_stop_before_host_stack_or_unbounded_formulas() {
    let fixture = Fixture::new();
    let mut source = String::new();
    for i in 0..260 {
        source.push_str(&format!("fn f{i}()->i64{{f{}()}}\n", i + 1));
    }
    source.push_str("fn f260()->i64{42}");
    let (output, report) = fixture.verify(&source);
    status(&output, &report, 6, "unknown");
    assert!(report["message"].as_str().unwrap().contains("depth"));
    let mut source = String::from("fn f0()->i64{0}\n");
    for i in 1..20 {
        source.push_str(&format!("fn f{i}()->i64{{f{}()+f{}()}}\n", i - 1, i - 1));
    }
    let (output, report) = fixture.verify(&source);
    status(&output, &report, 6, "unknown");
    assert!(!report["obligations"].as_array().unwrap().is_empty());
}

#[test]
#[cfg(unix)]
fn replacing_solver_with_fifo_cannot_block_final_identity_check() {
    use nix::{
        sys::signal::{Signal, killpg},
        unistd::Pid,
    };
    use std::{os::unix::process::CommandExt, process::Stdio, thread};
    let fixture = Fixture::new();
    let source = fixture.file("main.apl", "fn f()->i64{42}");
    let executable = fake(&fixture, "fifo");
    let mut child = Command::new(env!("CARGO_BIN_EXE_anl"))
        .arg("verify")
        .arg(source)
        .arg("--solver")
        .arg(executable)
        .arg("--timeout-ms")
        .arg("5000")
        .arg("--json")
        .process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(8);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline {
            let _ = killpg(Pid::from_raw(child.id() as i32), Signal::SIGKILL);
            let _ = child.wait();
            panic!("verification blocked opening a replaced solver FIFO");
        }
        thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    status(&output, &report, 4, "error");
    assert!(
        report["message"]
            .as_str()
            .unwrap()
            .contains("not a regular file"),
        "{report}"
    );
}

#[test]
#[cfg(target_os = "linux")]
fn non_utf8_source_paths_have_lossless_json_identity_without_panicking() {
    use std::{ffi::OsString, os::unix::ffi::OsStringExt};
    let fixture = Fixture::new();
    let path = fixture
        .0
        .join(OsString::from_vec(b"case-\xff.apl".to_vec()));
    fs::write(&path, "fn main()->i64{42}").unwrap();
    let (output, report) = verify(&path, &solver(), 30_000);
    status(&output, &report, 0, "verified");
    assert!(
        report["sources"][0]["path_bytes_hex"]
            .as_str()
            .unwrap()
            .ends_with("636173652dff2e61706c")
    );
}
