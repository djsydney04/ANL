//! Invariant-loop behavior against explicit runtime and mathematical oracles.
use anl::eval::{self, Value as Scalar};
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
            "apl-loop-verify-{}-{}",
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
    std::env::var_os("ANL_TEST_SOLVER")
        .or_else(|| std::env::var_os("APL_TEST_SOLVER"))
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let local = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join(".tools/z3-5.3.3-arm64-osx-13.3/bin/z3");
            if local.is_file() { local } else { "z3".into() }
        })
}
fn verify(source: &Path, timeout: u64) -> (Output, Value) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_anl"));
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
            panic!("loop verification exceeded its process deadline");
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
    assert_eq!(report["verification_revision"], "apl-loop-verify-v1");
    assert_eq!(report["semantic_revision"], "local-state-2026-11-17");
}
fn evaluates(source: &str, expected: i64) {
    let program = anl::compile(source).unwrap();
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100_000),
        Ok(Scalar::Integer(expected)),
        "{source}"
    );
}

#[test]
fn counters_guard_writes_nested_heads_and_argument_snapshots_follow_runtime() {
    let source = r#"
fn count(n:i64)->i64 requires 0<=n && n<=100;ensures(r)r==n;
{let mut i=0;while(i<n) invariant 0<=i && i<=n; {i=i+1;}i}
fn final_guard()->i64 ensures(r)r==312;
{let mut x=0;let mut y=10;let old=y;while({x=x+1;x<=2}) invariant 0<=x && x<=2; invariant y==old+x; {y=y+1;} x*100+y}
fn nested()->i64 ensures(r)r==9;
{let mut x=7;let saved=x;let mut i=0;while(i<2) invariant x==saved;invariant 0<=i && i<=2;
 {let mut j=0;while(j<2) invariant x==saved;invariant 0<=i && i<2;invariant 0<=j && j<=2;{j=j+1;}i=i+1;}x+i}
fn pair(a:i64,b:i64)->i64 requires 0<=a && a<=20;requires 0<=b && b<=20;{let mut own=b;own=own+1;a*10+own}
fn arguments()->i64 ensures(r)r==287;
{let mut x=1;let answer=pair({while(x<2) invariant 1<=x && x<=2;{x=x+1;}x},{x=x+5;x});answer*10+x}
"#;
    for (call, expected) in [
        ("count(0)", 0),
        ("count(1)", 1),
        ("count(100)", 100),
        ("final_guard()", 312),
        ("nested()", 9),
        ("arguments()", 287),
    ] {
        evaluates(&format!("{source}fn main()->i64{{{call}}}"), expected);
    }
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 0, "verified");
    assert_eq!(report["scope"]["termination_proved"], false);
    assert_eq!(report["scope"]["native_correctness"], false);
    assert_eq!(report["source_loop_metadata_complete"], true);
}

#[test]
fn divergence_keeps_prefix_traps_and_never_requires_a_normal_return() {
    let source = r#"
fn safe()->i64 ensures(r)false;{while(true) invariant true;{}0}
fn after()->i64{while(true) invariant true;{}1/0}
fn before()->i64{1/0;while(true) invariant true;{}0}
fn guard_before()->i64{while({1/0;while(true) invariant true;{}false}) invariant true;{}0}
fn guard_safe()->i64{while({while(true) invariant true;{}false}) invariant true;{}1/0}
fn overflow()->i64{let mut x=9223372036854775806;while(true) invariant true;{x=x+1;}x}
"#;
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 5, "failed");
    for name in ["safe", "after", "guard_safe"] {
        assert!(
            report["obligations"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|q| q["function"] == name)
                .all(|q| q["status"] == "verified"),
            "{name}: {report}"
        );
    }
    for name in ["before", "guard_before", "overflow"] {
        assert!(
            report["obligations"]
                .as_array()
                .unwrap()
                .iter()
                .any(|q| q["function"] == name
                    && q["kind"] == "body_safe"
                    && q["status"] == "failed"),
            "{name}: {report}"
        );
    }
    let overflow = report["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["function"] == "overflow" && q["kind"] == "body_safe")
        .unwrap();
    assert_eq!(overflow["model"]["replayed"], false);
    assert!(
        overflow["model"]["assignments"]
            .as_array()
            .unwrap()
            .iter()
            .any(|a| a["origin"]["kind"] == "loop_head" && a["value"] == "9223372036854775807")
    );
}

#[test]
fn invariant_clauses_and_entry_contracts_are_independent_obligations() {
    let source = r#"
fn initial()->i64{while(false) invariant false;invariant 1/0==0;{}0}
fn preserve()->i64{let mut x=1;while(true) invariant x!=0;invariant 1/x==1;{x=0;}0}
fn vacuous(x:i64)->i64 requires x>0;requires x<0;ensures(r)false;{while(true) invariant true;{}0}
fn undefined(x:i64)->i64 requires 1/x==0;ensures(r)false;{while(true) invariant true;{}0}
fn unit_input(u:unit)->i64 ensures(r)false;{while(true) invariant true;{}0}
fn unreachable()->i64 ensures(r)r==42;{if false{while(false) invariant false;{}0}else{42}}
"#;
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 5, "failed");
    for (name, kind, count) in [
        ("initial", "loop_invariant_initialized", 2),
        ("preserve", "loop_invariant_preserved", 2),
        ("vacuous", "precondition_satisfiable", 1),
        ("undefined", "precondition_defined", 1),
    ] {
        assert_eq!(
            report["obligations"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|q| q["function"] == name && q["kind"] == kind && q["status"] == "failed")
                .count(),
            count,
            "{report}"
        );
    }
    let unit = report["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["function"] == "unit_input" && q["kind"] == "precondition_satisfiable")
        .unwrap();
    assert_eq!(unit["model_symbols"], json!([]));
    assert_eq!(unit["model"], json!({"replayed":false,"assignments":[]}));
    assert!(
        report["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|q| q["function"] == "unreachable")
            .all(|q| q["status"] == "verified")
    );
}

#[test]
fn untouched_mutable_cells_need_inner_invariants() {
    let (output,report)=Fixture::new().verify("fn f()->i64 ensures(r)r==7;{let mut x=7;let saved=x;let mut i=0;while(i<1) invariant x==saved;invariant 0<=i && i<=1;{while(false) invariant 0<=i && i<1;{}i=i+1;}x}");
    status(&output, &report, 5, "failed");
    assert!(
        report["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|q| q["kind"] == "loop_invariant_preserved" && q["status"] == "failed")
    );
    assert!(
        report["loop_occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .all(|o| o["head_symbols"].as_array().unwrap().len() == 2)
    );
}

#[test]
fn binding_provenance_is_function_local_and_occurrences_are_fresh() {
    let source = r#"
fn first()->i64 ensures(r)r==1;{let mut x=0;while(x<1) invariant 0<=x && x<=1;{x=x+1;}x}
fn second()->i64 ensures(r)r==2;{let mut x=1;{let x=true;while(false) invariant x;{}};x=1;9;while(x<2) invariant 1<=x && x<=2;{x=x+1;}x}
fn main()->i64 ensures(r)r==6;{first()+second()+first()+second()}
"#;
    evaluates(source, 6);
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 0, "verified");
    let mut names = std::collections::BTreeSet::new();
    let mut occurrences = std::collections::BTreeSet::new();
    for occurrence in report["loop_occurrences"].as_array().unwrap() {
        assert!(occurrences.insert(occurrence["id"].as_u64().unwrap()));
        let function = occurrence["source_function_id"].as_u64().unwrap() as usize;
        for head in occurrence["head_symbols"].as_array().unwrap() {
            assert!(names.insert(head["symbol"].as_str().unwrap()));
            let binding = head["binding_id"].as_u64().unwrap() as usize;
            assert_eq!(
                report["functions"][function]["bindings"][binding]["name"],
                "x"
            );
            assert_eq!(
                report["functions"][function]["bindings"][binding]["mutable"],
                true
            );
        }
    }
    assert_eq!(occurrences.len(), 9);
    assert_eq!(names.len(), 9); // Shadowed immutable x retains the outer mutable cell too.
    for function in 0..3 {
        let mut ids = Vec::new();
        for query in report["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|q| q["function_id"] == function)
        {
            for check in query["checks"].as_array().unwrap() {
                ids.push(check["id"].as_u64().unwrap());
            }
        }
        ids.sort_unstable();
        assert_eq!(ids, (0..ids.len() as u64).collect::<Vec<_>>());
    }
}

#[test]
fn complete_parameters_and_only_dependent_heads_appear_in_models() {
    let source = "fn f(unused:bool,u:unit)->i64 ensures(r)r==99;{let mut x=0;let old=x;while(false) invariant x==old;{}let saved=x;while(false) invariant x==saved;{}x}";
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 5, "failed");
    let initial: Vec<_> = report["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|q| q["kind"] == "loop_invariant_initialized")
        .collect();
    assert_eq!(
        initial[0]["model_symbols"],
        json!([{"symbol":"p0","type":"bool","origin":{"kind":"parameter","index":0}}])
    );
    assert_eq!(initial[1]["model_symbols"].as_array().unwrap().len(), 2);
    assert_eq!(initial[1]["model_symbols"][1]["symbol"], "h0");
    let post = report["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["kind"] == "postcondition")
        .unwrap();
    assert_eq!(post["model_symbols"].as_array().unwrap().len(), 3);
    for assignment in post["model"]["assignments"]
        .as_array()
        .unwrap()
        .iter()
        .skip(1)
    {
        assert_eq!(assignment["origin"]["kind"], "loop_head");
        assert_eq!(assignment["within_machine_range"], true);
        assert!(assignment.get("parameter").is_none());
    }
}

#[test]
fn recursion_inside_guards_bodies_and_arguments_rejects_before_tools() {
    let fixture = Fixture::new();
    for source in [
        "fn f()->bool{while(f()) invariant true;{}false}",
        "fn f()->unit{while(false) invariant true;{f();}}",
        "fn id(x:bool)->bool{x}fn f()->bool{while(id(f())) invariant true;{}false}",
        "fn main()->i64{42}fn unused()->unit{while(false) invariant true;{unused();}}",
    ] {
        let path = fixture.file("recursive.apl", source);
        let output = Command::new(env!("CARGO_BIN_EXE_anl"))
            .arg("verify")
            .arg(path)
            .args(["--solver", "/no-such-apl-solver", "--json"])
            .output()
            .unwrap();
        let report: Value = serde_json::from_slice(&output.stdout).unwrap();
        status(&output, &report, 7, "unsupported");
        assert!(report["message"].as_str().unwrap().contains("recursive"));
        assert!(report["compiler"].is_null());
        assert!(report["solver"].is_null());
        assert_eq!(report["obligations"], json!([]));
    }
}

#[test]
fn the_head_limit_is_shared_across_functions_and_retains_prior_evidence() {
    let fixture = Fixture::new();
    let mut source = String::from("fn prior()->unit{()}\n");
    let cells = (0..64)
        .map(|i| format!("let mut x{i}=0;"))
        .collect::<String>();
    for i in 0..65 {
        source.push_str(&format!(
            "fn f{i}()->unit{{{cells}while(false) invariant true;{{}}}}\n"
        ));
    }
    let path = fixture.file("heads.apl", &source);
    let (output, report) = verify(&path, 30_000);
    status(&output, &report, 6, "unknown");
    assert!(
        report["message"].as_str().unwrap().contains("4096 symbols"),
        "{}",
        report["message"]
    );
    assert_eq!(
        report["loop_occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .map(|o| o["head_symbols"].as_array().unwrap().len())
            .sum::<usize>(),
        4096
    );
    let queries = report["obligations"].as_array().unwrap();
    assert!(queries.len() > 2);
    assert!(
        queries
            .iter()
            .all(|q| q["query_complete"] == true && q["status"] == "verified")
    );
    assert_eq!(queries[0]["function"], "prior");
}

#[test]
fn unit_heavy_heads_allocate_no_symbols_and_inline_work_is_attempt_wide() {
    let fixture = Fixture::new();
    let params = (0..2000)
        .map(|i| format!("p{i}:unit"))
        .collect::<Vec<_>>()
        .join(",");
    let args = vec!["()"; 2000].join(",");
    let source = format!(
        "fn leaf({params})->unit{{let mut u=();{} }}fn caller()->unit{{leaf({args})}}",
        "while(false) invariant true;{}".repeat(45)
    );
    let path = fixture.file("work.apl", &source);
    let (output, report) = verify(&path, 30_000);
    status(&output, &report, 6, "unknown");
    assert!(
        report["message"]
            .as_str()
            .unwrap()
            .contains("symbolic work"),
        "{}",
        report["message"]
    );
    assert!(
        report["loop_occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .all(|o| o["head_symbols"] == json!([]))
    );
    assert!(
        !report["obligations"].as_array().unwrap().is_empty(),
        "expected completed leaf evidence before caller expansion"
    );
}

#[test]
fn mixed_head_types_preserve_immutable_snapshots_and_omit_unit_symbols() {
    let source = "fn mixed(p:bool)->i64 ensures(r)r==42;{let mut i=0;let mut b=p;let mut u=();let frozen=i;while(i<1) invariant 0<=i && i<=1;invariant b==p;invariant u==();{i=i+1;}if b==p && frozen==0 && u==(){42}else{0}}";
    evaluates(&format!("{source}fn main()->i64{{mixed(false)}}"), 42);
    evaluates(&format!("{source}fn main()->i64{{mixed(true)}}"), 42);
    let (output, report) = Fixture::new().verify(source);
    status(&output, &report, 0, "verified");
    let heads = report["loop_occurrences"][0]["head_symbols"]
        .as_array()
        .unwrap();
    assert_eq!(heads.len(), 2);
    assert_eq!(heads[0]["type"], "bool");
    assert_eq!(heads[1]["type"], "i64");
}

#[test]
fn formula_and_total_transcript_byte_limits_retain_earlier_queries() {
    let fixture = Fixture::new();
    for (clauses, reason) in [
        (
            format!("invariant {}>0;", "9".repeat(4096)).repeat(100),
            "1048576 bytes",
        ),
        ("invariant true;".repeat(200), "16777216 query bytes"),
    ] {
        let path = fixture.file(
            "bytes.apl",
            &format!("fn prior()->unit{{()}}fn many()->unit{{while(false) {clauses}{{}}}}"),
        );
        let (output, report) = verify(&path, 30_000);
        status(&output, &report, 6, "unknown");
        assert!(
            report["message"].as_str().unwrap().contains(reason),
            "{}",
            report["message"]
        );
        let obligations = report["obligations"].as_array().unwrap();
        assert!(obligations.len() >= 2);
        assert!(
            obligations
                .iter()
                .all(|q| q["status"] == "verified" && q["query_complete"] == true)
        );
        assert_eq!(obligations[0]["function"], "prior");
    }
}

#[test]
#[cfg(unix)]
fn attempted_queries_are_retained_when_the_attempt_wide_query_limit_is_hit() {
    use std::os::unix::fs::PermissionsExt;
    let fixture = Fixture::new();
    let mut source = String::from("fn first()->unit{while(false) invariant true;{}}");
    for i in 0..511 {
        source.push_str(&format!("fn f{i}()->unit{{()}}"));
    }
    let path = fixture.file("queries.apl", &source);
    let solver=fixture.file("unknown-solver","#!/bin/sh\nif [ \"$1\" = '-version' ]; then echo 'Z3 version 5.3.3 - controlled query-limit substitute'; exit 0; fi\nwhile IFS= read -r line; do\ncase \"$line\" in '(check-sat)') echo unknown;; '(exit)') exit 0;; esac\ndone\n");
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_anl"))
        .arg("verify")
        .arg(path)
        .arg("--solver")
        .arg(solver)
        // This count-limit case launches 1024 real solver processes. Allow scheduling
        // headroom so the query budget, rather than the deadline, stops the attempt.
        .args(["--json", "--timeout-ms", "120000"])
        .output()
        .unwrap();
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    status(&output, &report, 6, "unknown");
    assert!(
        report["message"].as_str().unwrap().contains("1024 queries"),
        "{}",
        report["message"]
    );
    let queries = report["obligations"].as_array().unwrap();
    assert_eq!(queries.len(), 1024);
    assert!(
        queries
            .iter()
            .all(|q| q["query_complete"] == true && q["solver_status"] == "unknown")
    );
}
