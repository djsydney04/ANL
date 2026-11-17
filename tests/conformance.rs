//! Independent source-to-result conformance cases derived from the M1 contract.
//! Every case runs the shipped CLI, including parsing, checking, and evaluation.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

struct Source(PathBuf);

impl Source {
    fn new(bytes: impl AsRef<[u8]>) -> Self {
        let id = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!("apl-conformance-{}-{id}", std::process::id()));
        fs::create_dir(&dir).expect("create isolated fixture directory");
        let path = dir.join("case.apl");
        fs::write(&path, bytes).expect("write source fixture");
        Self(path)
    }

    fn run(&self, command: &str, extra: &[&str]) -> Output {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_apl"));
        cmd.arg(command).arg(&self.0).args(extra);
        run_bounded(cmd)
    }
}

impl Drop for Source {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(self.0.parent().expect("fixture parent"));
    }
}

fn run_bounded(mut command: Command) -> Output {
    let debug = format!("{command:?}");
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start apl CLI");
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if child.try_wait().expect("poll apl CLI").is_some() {
            return child.wait_with_output().expect("collect apl CLI output");
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let output = child.wait_with_output().expect("collect timed-out CLI");
            panic!("CLI exceeded ten-second test limit: {debug}\n{output:?}");
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

fn assert_status(output: &Output, code: i32, context: &str) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "{context}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn eval(source: &str, expected: i64) {
    let output = Source::new(source).run("eval", &[]);
    assert_status(&output, 0, source);
    assert_eq!(
        output.stdout,
        format!("{expected}\n").as_bytes(),
        "{source}"
    );
    assert!(output.stderr.is_empty(), "{source}: {output:?}");
}

fn expression(source: &str, expected: i64) {
    eval(&format!("fn main() -> i64 {{ {source} }}"), expected);
}

fn predicate(source: &str, expected: bool) {
    expression(
        &format!("if {source} {{ 1 }} else {{ 0 }}"),
        i64::from(expected),
    );
}

fn reject(source: &str) {
    let output = Source::new(source).run("check", &[]);
    assert_status(&output, 1, source);
    assert!(
        output.stdout.is_empty(),
        "invalid source emitted a value: {source}"
    );
    assert!(!output.stderr.is_empty(), "missing diagnostic: {source}");
    assert!(!String::from_utf8_lossy(&output.stderr).contains("panicked"));
}

fn trap(source: &str, kind: &str) {
    let output = Source::new(source).run("eval", &[]);
    assert_status(&output, 2, source);
    assert!(output.stdout.is_empty(), "trap emitted a successful value");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(kind),
        "expected {kind}: {source}\n{output:?}"
    );
}

#[test]
fn integer_literals_and_arithmetic_preserve_full_i64_values() {
    for (source, expected) in [
        ("0", 0),
        ("00042", 42),
        ("9223372036854775807", i64::MAX),
        ("-9223372036854775808", i64::MIN),
        ("-9223372036854775808 + 1", -9223372036854775807),
        ("9223372036854775807 - 1", 9223372036854775806),
        ("-9223372036854775808 * 1", i64::MIN),
        ("-9223372036854775808 / 1", i64::MIN),
        ("-9223372036854775808 % 1", 0),
        ("9223372036854775807 + -9223372036854775808", -1),
        ("-(-9223372036854775807)", i64::MAX),
        ("7 + 4 * 3", 19),
        ("(7 + 4) * 3", 33),
        ("10 - 3 - 2", 5),
        ("12 / 3 / 2", 2),
        ("-2 * -3 + 4", 10),
        ("--4", 4),
    ] {
        expression(source, expected);
    }
}

#[test]
fn signed_division_truncates_toward_zero_and_remainder_follows_dividend() {
    for (source, expected) in [
        ("7 / 3", 2),
        ("-7 / 3", -2),
        ("7 / -3", -2),
        ("-7 / -3", 2),
        ("7 % 3", 1),
        ("-7 % 3", -1),
        ("7 % -3", 1),
        ("-7 % -3", -1),
        ("2 / 3", 0),
        ("-2 / 3", 0),
        ("2 / -3", 0),
        ("-2 / -3", 0),
        ("2 % 3", 2),
        ("-2 % 3", -2),
        ("2 % -3", 2),
        ("-2 % -3", -2),
        ("-9223372036854775808 / 3", -3074457345618258602),
        ("-9223372036854775808 % 3", -2),
        ("9223372036854775807 / -3", -3074457345618258602),
        ("9223372036854775807 % -3", 1),
        ("0 / -9223372036854775808", 0),
        ("0 % -9223372036854775808", 0),
    ] {
        expression(source, expected);
    }
}

#[test]
fn every_checked_arithmetic_overflow_is_a_named_trap() {
    for source in [
        "9223372036854775807 + 1",
        "-9223372036854775808 + -1",
        "-9223372036854775808 - 1",
        "9223372036854775807 - -1",
        "9223372036854775807 * 2",
        "-9223372036854775808 * -1",
        "-(-9223372036854775808)",
        "--9223372036854775808",
        "-9223372036854775808 / -1",
        "-9223372036854775808 % -1",
    ] {
        trap(
            &format!("fn main() -> i64 {{ {source} }}"),
            "arithmetic_overflow",
        );
    }
    for source in ["1 / 0", "0 / 0", "-1 / 0", "1 % 0", "0 % 0", "-1 % 0"] {
        trap(
            &format!("fn main() -> i64 {{ {source} }}"),
            "division_by_zero",
        );
    }
}

#[test]
fn comparison_equality_and_boolean_operators_have_scalar_semantics() {
    for (source, expected) in [
        ("-2 < -1", true),
        ("2 < 2", false),
        ("2 <= 2", true),
        ("3 <= 2", false),
        ("2 > -1", true),
        ("2 > 2", false),
        ("2 >= 2", true),
        ("-1 >= 2", false),
        ("7 == 7", true),
        ("7 == 8", false),
        ("7 != 8", true),
        ("7 != 7", false),
        ("true == true", true),
        ("true != false", true),
        ("() == ()", true),
        ("() != ()", false),
        ("!false", true),
        ("!!true", true),
        ("!true", false),
        ("true && true", true),
        ("true && false", false),
        ("false && true", false),
        ("false && false", false),
        ("true || true", true),
        ("true || false", true),
        ("false || true", true),
        ("false || false", false),
        ("true || false && false", true),
        ("(true || false) && false", false),
        ("1 < 2 == true", true),
        ("(1 < 2) == true", true),
        ("(1 < 2) == (3 > 2)", true),
        ("-9223372036854775808 < 9223372036854775807", true),
    ] {
        predicate(source, expected);
    }
}

#[test]
fn branches_and_short_circuit_operators_skip_trapping_expressions() {
    expression("if true { 7 } else { 1 / 0 }", 7);
    expression("if false { 9223372036854775807 + 1 } else { 9 }", 9);
    predicate("false && (1 / 0 == 0)", false);
    predicate("true || (9223372036854775807 + 1 == 0)", true);
    trap(
        "fn main() -> i64 { if true && (1 / 0 == 0) { 1 } else { 0 } }",
        "division_by_zero",
    );
    trap(
        "fn main() -> i64 { if false || (1 / 0 == 0) { 1 } else { 0 } }",
        "division_by_zero",
    );
}

#[test]
fn operand_argument_and_statement_order_preserve_first_trap() {
    for source in [
        "fn main() -> i64 { (1 / 0) + (9223372036854775807 + 1) }",
        "fn choose(a: i64, b: i64) -> i64 { b } fn main() -> i64 { choose(1 / 0, 9223372036854775807 + 1) }",
        "fn main() -> i64 { 1 / 0; 9223372036854775807 + 1 }",
        "fn main() -> i64 { let x = 1 / 0; 9223372036854775807 + x }",
    ] {
        trap(source, "division_by_zero");
    }
    for source in [
        "fn main() -> i64 { (9223372036854775807 + 1) + (1 / 0) }",
        "fn choose(a: i64, b: i64) -> i64 { a } fn main() -> i64 { choose(9223372036854775807 + 1, 1 / 0) }",
        "fn main() -> i64 { 9223372036854775807 + 1; 1 / 0 }",
    ] {
        trap(source, "arithmetic_overflow");
    }
}

#[test]
fn block_scopes_old_environment_and_discard_bindings_preserve_names() {
    for (source, expected) in [
        ("let x = 7; 0; x", 7),
        ("let x = 7; let y = 11; 0; (); true; x + y", 18),
        (
            "let x = 7; let y = { let x = x + 1; 0; x }; 0; x * 10 + y",
            78,
        ),
        ("let x = 7; { let x = 99; x }; x", 7),
        (
            "let x = 7; let y = { let x = 3; { let z = x + 1; z }; x }; x + y",
            10,
        ),
        (
            "let x: i64 = 8; let yes: bool = true; let nothing: unit = (); if yes { x } else { 0 }",
            8,
        ),
    ] {
        expression(source, expected);
    }
    eval(
        "fn add(a: i64, b: i64) -> i64 { 0; let c = a + b; (); a * 100 + b * 10 + c } fn main() -> i64 { add(2, 3) }",
        235,
    );
    eval(
        "fn read(x: i64) -> i64 { x } fn main() -> i64 { let x = 99; read(7) + x }",
        106,
    );
}

#[test]
fn unit_functions_and_empty_blocks_are_real_values() {
    eval(
        "fn nothing() -> unit {} fn main() -> i64 { let x: unit = nothing(); if x == () { 7 } else { 0 } }",
        7,
    );
    eval(
        "fn consume(x: unit) -> unit { x; } fn main() -> i64 { consume({}); consume(()); 8 }",
        8,
    );
    eval(
        "fn unit_branch(x: bool) -> unit { if x { () } else {} } fn main() -> i64 { unit_branch(false); 9 }",
        9,
    );
}

#[test]
fn forward_zero_argument_and_recursive_functions_use_declared_signatures() {
    eval(
        "fn main() -> i64 { answer() } fn answer() -> i64 { 42 }",
        42,
    );
    eval(
        "fn fact(n: i64) -> i64 { if n == 0 { 1 } else { n * fact(n - 1) } } fn main() -> i64 { fact(10) }",
        3628800,
    );
    eval(
        "fn even(n: i64) -> bool { if n == 0 { true } else { odd(n - 1) } } fn odd(n: i64) -> bool { if n == 0 { false } else { even(n - 1) } } fn main() -> i64 { if even(20) && odd(19) { 42 } else { 0 } }",
        42,
    );
}

#[test]
fn library_check_has_no_executable_entry_requirement() {
    for source in [
        "",
        "fn helper(x: i64) -> i64 { x + 1 }",
        "fn main(x: bool) -> unit { x; }",
    ] {
        let output = Source::new(source).run("check", &[]);
        assert_status(&output, 0, source);
        assert!(output.stderr.is_empty(), "{output:?}");
        let output = Source::new(source).run("eval", &[]);
        assert_status(&output, 1, source);
        assert!(output.stdout.is_empty());
    }
    for source in ["fn main() -> bool { true }", "fn main() -> unit { () }"] {
        let output = Source::new(source).run("eval", &[]);
        assert_status(&output, 1, source);
    }
}

#[test]
fn whole_program_checking_rejects_unreachable_type_and_name_errors() {
    for source in [
        "fn broken() -> i64 { true } fn main() -> i64 { 7 }",
        "fn broken() -> i64 { missing } fn main() -> i64 { 7 }",
        "fn main() -> i64 { if true { 7 } else { false } }",
        "fn main() -> i64 { if true { 7 } else { missing } }",
        "fn main() -> i64 { if false && missing { 7 } else { 0 } }",
        "fn main() -> i64 { if true || (1 + false == 0) { 7 } else { 0 } }",
    ] {
        reject(source);
        let output = Source::new(source).run("eval", &[]);
        assert_status(&output, 1, source);
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn wrong_scalar_operator_annotation_and_call_types_are_rejected() {
    for source in [
        "fn main() -> i64 { true + 1 }",
        "fn main() -> i64 { -true }",
        "fn main() -> i64 { if !1 { 1 } else { 0 } }",
        "fn main() -> i64 { if 1 && true { 1 } else { 0 } }",
        "fn main() -> i64 { if true || 1 { 1 } else { 0 } }",
        "fn main() -> i64 { if true < false { 1 } else { 0 } }",
        "fn main() -> i64 { if 1 == true { 1 } else { 0 } }",
        "fn main() -> i64 { if () != false { 1 } else { 0 } }",
        "fn main() -> i64 { if 1 { 1 } else { 0 } }",
        "fn main() -> i64 { let x: bool = 1; 0 }",
        "fn main() -> i64 { let x: i64 = (); x }",
        "fn f(x: i64) -> i64 { x } fn main() -> i64 { f(true) }",
        "fn f(x: i64) -> i64 { x } fn main() -> i64 { f() }",
        "fn f() -> i64 { 1 } fn main() -> i64 { f(2) }",
        "fn f() -> i64 { 1 } fn main() -> i64 { let x = f; 0 }",
        "fn main() -> i64 { 1; }",
    ] {
        reject(source);
    }
}

#[test]
fn duplicate_declarations_and_invalid_name_resolution_are_rejected() {
    for source in [
        "fn f() -> i64 { 1 } fn f() -> i64 { 2 }",
        "fn main() -> i64 { 1 } fn main() -> i64 { 2 }",
        "fn f(x: i64, x: i64) -> i64 { x }",
        "fn main() -> i64 { let x = 1; let x = 2; x }",
        "fn main() -> i64 { let x = x; x }",
        "fn main() -> i64 { { let x = 1; x }; x }",
        "fn main() -> i64 { missing() }",
        "fn f() -> i64 { 1 } fn main() -> i64 { let f = 2; f() }",
        "fn f() -> i64 { 1 } fn call(f: i64) -> i64 { f() }",
    ] {
        reject(source);
    }
}

#[test]
fn lexer_and_parser_reject_malformed_or_unsupported_source() {
    for source in [
        "fn main() -> i64 { @ }",
        "fn main() -> i64 { 1",
        "fn main() -> i64 { 1 } junk",
        "fn main() -> i64 { let x = 1 x }",
        "fn main() -> i64 { if true { 1 } }",
        "fn main() -> i64 { 9223372036854775808 }",
        "fn main() -> i64 { -9223372036854775809 }",
        "fn main() -> i64 { -(9223372036854775808) }",
        "fn main() -> i64 { 9999999999999999999999999999999999999999 }",
        "fn main() -> i64 { 0xff }",
        "fn main() -> i64 { 1_000 }",
        "fn main() -> i64 { 1i64 }",
        "fn main() -> i64 { /* comment */ 1 }",
        "fn café() -> i64 { 1 }",
        "fn let() -> i64 { 1 }",
        "fn main() -> i64 { let true = 1; true }",
        "fn f(x: i64,) -> i64 { x }",
        "fn f(x: i64) -> i64 { x } fn main() -> i64 { f(1,) }",
        "fn main() -> i64 { if 1 < 2 < 3 { 1 } else { 0 } }",
        "fn main() -> i64 { if true == false == false { 1 } else { 0 } }",
        "fn main() -> i64 { let mut x: i64; x }",
        "fn main() -> i64 { return 1; }",
        "fn main() -> i64 { while true {} 1 }",
        "fn main() -> i64 { let x = 1; x = 2; x }",
    ] {
        reject(source);
    }
}

#[test]
fn unicode_comments_crlf_and_ascii_identifier_boundaries_are_supported() {
    eval(
        "// λ 日本語 🌱\r\nfn main() -> i64 {\r\n let _value2 = 42; // café\r\n _value2\r\n}",
        42,
    );
    eval(
        "fn true_value() -> i64 { 42 } fn main() -> i64 { true_value() }// no newline",
        42,
    );
}

#[test]
fn invalid_utf8_is_a_source_error_instead_of_a_host_failure() {
    let output = Source::new(b"fn main() -> i64 { 1 }\xff").run("check", &[]);
    assert_status(&output, 1, "invalid UTF-8 source");
    assert!(output.stdout.is_empty());
    assert!(!output.stderr.is_empty());
}

#[test]
fn diagnostic_identifies_the_source_position() {
    let source = Source::new("fn main() -> i64 {\n  missing\n}\n");
    let output = source.run("check", &[]);
    assert_status(&output, 1, "undefined name diagnostic");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("case.apl:2:3"),
        "expected filename and 1-based line/column: {stderr}"
    );
    assert!(
        stderr.contains("missing"),
        "expected undefined identifier: {stderr}"
    );
}

#[test]
fn finite_fuel_and_depth_bounds_return_resource_outcomes() {
    let source = Source::new("fn forever() -> i64 { forever() } fn main() -> i64 { forever() }");
    for fuel in ["0", "20", "1000000000"] {
        let output = source.run("eval", &["--fuel", fuel]);
        assert_status(&output, 3, "bounded recursive evaluation");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        assert!(!String::from_utf8_lossy(&output.stderr).contains("panicked"));
    }
}

#[test]
fn fuel_counts_evaluated_core_expressions_and_skips_unselected_branches() {
    // A literal costs one expression. Binary addition costs its root and two operands.
    for (body, sufficient, insufficient, expected) in [
        ("7", "1", "0", 7),
        ("2 + 3", "3", "2", 5),
        ("if true { 7 } else { 1 / 0 }", "3", "2", 7),
    ] {
        let source = Source::new(format!("fn main() -> i64 {{ {body} }}"));
        let output = source.run("eval", &["--fuel", sufficient]);
        assert_status(&output, 0, body);
        assert_eq!(output.stdout, format!("{expected}\n").as_bytes());
        let output = source.run("eval", &["--fuel", insufficient]);
        assert_status(&output, 3, body);
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn deep_and_oversized_source_fail_with_a_bounded_resource_diagnostic() {
    let deep = format!(
        "fn main() -> i64 {{ {}0{} }}",
        "(".repeat(2000),
        ")".repeat(2000)
    );
    let long_chain = format!("fn main() -> i64 {{ 0{} }}", " + 1".repeat(2000));
    let oversized = format!("//{}\nfn main() -> i64 {{ 0 }}", "x".repeat(1024 * 1024));
    for source in [deep, long_chain, oversized] {
        let output = Source::new(source).run("check", &[]);
        assert_status(&output, 3, "front-end resource bound");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        assert!(!String::from_utf8_lossy(&output.stderr).contains("panicked"));
    }
}

#[test]
fn invocation_and_infrastructure_errors_are_distinct_from_source_errors() {
    let source = Source::new("fn main() -> i64 { 7 }");
    for arguments in [vec![], vec!["unknown"], vec!["eval"], vec!["check"]] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_apl"));
        command.args(arguments);
        assert_status(&run_bounded(command), 4, "bad invocation");
    }
    for arguments in [
        vec!["--fuel"],
        vec!["--fuel", "-1"],
        vec!["--fuel", "1.5"],
        vec!["--fuel", "1000000001"],
        vec!["--fuel", "no"],
        vec!["--unknown"],
    ] {
        let output = source.run("eval", &arguments);
        assert_status(&output, 4, "bad eval option");
    }
    let missing = source.0.with_file_name("does-not-exist.apl");
    let mut command = Command::new(env!("CARGO_BIN_EXE_apl"));
    command.arg("check").arg(missing);
    assert_status(&run_bounded(command), 4, "missing input file");
    let mut command = Command::new(env!("CARGO_BIN_EXE_apl"));
    command.arg("--version");
    let output = run_bounded(command);
    assert_status(&output, 0, "version query");
    assert!(String::from_utf8_lossy(&output.stdout).starts_with("apl "));
}

#[test]
fn documented_examples_execute_to_their_independent_expected_values() {
    for (name, expected) in [
        ("factorial.apl", 3628800),
        ("gcd.apl", 21),
        ("sum-primes.apl", 328),
        ("scopes.apl", 78),
    ] {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(name);
        let mut command = Command::new(env!("CARGO_BIN_EXE_apl"));
        command.arg("eval").arg(path);
        let output = run_bounded(command);
        assert_status(&output, 0, name);
        assert_eq!(output.stdout, format!("{expected}\n").as_bytes(), "{name}");
        assert!(output.stderr.is_empty());
    }
}

fn integer(value: &str) -> serde_json::Value {
    serde_json::json!({"tag": "integer", "ty": "i64", "value": value})
}

fn core_program(body: serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "schema": "apl-core-v0", "semantic_revision": "m1-2026-11-16",
        "functions": [{"id": 0, "name": "main", "params": [], "result": "i64", "body": body}],
        "entry": 0
    })
}

fn core_expression(body: serde_json::Value) -> serde_json::Value {
    serde_json::json!({"schema": "apl-expr-v0", "semantic_revision": "m1-2026-11-16", "expression": body})
}

fn core_outcome(raw: &str, extra: &[&str], code: i32, expected: serde_json::Value) {
    let output = Source::new(raw).run("eval-core", extra);
    assert_status(&output, code, raw);
    let actual: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("expected outcome JSON: {error}; {output:?}"));
    assert_eq!(actual, expected, "{raw}");
}

#[test]
fn core_import_rechecks_scalar_values_and_reports_exact_outcomes() {
    use serde_json::json;
    for (body, expected) in [
        (
            integer("-9223372036854775808"),
            json!({"outcome":"value","type":"i64","value":"-9223372036854775808"}),
        ),
        (
            json!({"tag":"boolean","ty":"bool","value":true}),
            json!({"outcome":"value","type":"bool","value":true}),
        ),
        (
            json!({"tag":"unit","ty":"unit"}),
            json!({"outcome":"value","type":"unit","value":null}),
        ),
    ] {
        core_outcome(&core_expression(body).to_string(), &[], 0, expected);
    }
    for (op, left, right, kind) in [
        ("div", "1", "0", "division_by_zero"),
        ("rem", "-9223372036854775808", "-1", "arithmetic_overflow"),
    ] {
        let body =
            json!({"tag":"binary","ty":"i64","op":op,"left":integer(left),"right":integer(right)});
        core_outcome(
            &core_program(body).to_string(),
            &[],
            2,
            json!({"outcome":"trap","trap":kind}),
        );
    }
    core_outcome(
        &core_program(integer("7")).to_string(),
        &["--fuel", "0"],
        3,
        json!({"outcome":"resource_limit"}),
    );
}

#[test]
fn core_import_rejects_schema_shape_numeric_and_type_forgeries() {
    use serde_json::json;
    let valid = core_program(integer("7"));
    let mut cases = Vec::new();
    for (field, value) in [
        ("schema", json!("apl-core-v1")),
        ("semantic_revision", json!("future")),
        ("entry", json!(-1)),
        ("entry", json!(1)),
        ("entry", json!(0.0)),
        ("entry", json!("0")),
        ("extra", json!(true)),
    ] {
        let mut changed = valid.clone();
        changed[field] = value;
        cases.push(changed);
    }
    let mut missing_revision = valid.clone();
    missing_revision
        .as_object_mut()
        .unwrap()
        .remove("semantic_revision");
    cases.push(missing_revision);
    for value in [
        "-0",
        "+1",
        "01",
        "-01",
        "",
        " 1",
        "1 ",
        "1.0",
        "1e0",
        "9223372036854775808",
        "-9223372036854775809",
    ] {
        cases.push(core_program(integer(value)));
    }
    for body in [
        json!({"tag":"integer","ty":"bool","value":"7"}),
        json!({"tag":"integer","ty":"i64","value":7}),
        json!({"tag":"integer","ty":"i64","value":"7","unchecked":true}),
        json!({"tag":"integer","value":"7"}),
        json!({"tag":"mystery","ty":"i64"}),
        json!({"tag":"local","ty":"i64","index":0}),
        json!({"tag":"local","ty":"i64","index":-1}),
        json!({"tag":"call","ty":"i64","function":1,"arguments":[]}),
        json!({"tag":"call","ty":"i64","function":0,"arguments":[integer("1")]}),
        json!({"tag":"binary","ty":"i64","op":"pow","left":integer("2"),"right":integer("3")}),
        json!({"tag":"binary","ty":"i64","op":"add","left":integer("2"),"right":{"tag":"boolean","ty":"bool","value":true}}),
    ] {
        cases.push(core_program(body));
    }
    for (field, value) in [
        ("id", json!(1)),
        ("id", json!(0.0)),
        ("name", json!("fn")),
        ("name", json!("café")),
        ("result", json!("bool")),
        ("params", json!(["i64"])),
        ("unexpected", json!(0)),
    ] {
        let mut changed = valid.clone();
        changed["functions"][0][field] = value;
        cases.push(changed);
    }
    let mut duplicate_name = valid.clone();
    let mut second = duplicate_name["functions"][0].clone();
    second["id"] = json!(1);
    duplicate_name["functions"]
        .as_array_mut()
        .unwrap()
        .push(second);
    cases.push(duplicate_name);
    for case in cases {
        core_outcome(&case.to_string(), &[], 1, json!({"outcome":"invalid_ir"}));
    }
}

#[test]
fn core_import_rejects_duplicate_keys_and_noninteger_index_representations() {
    use serde_json::json;
    let valid = core_program(integer("7")).to_string();
    let duplicate_top = valid.replacen("\"entry\":0", "\"entry\":0,\"entry\":0", 1);
    let duplicate_nested = valid.replacen("\"value\":\"7\"", "\"value\":\"7\",\"value\":\"8\"", 1);
    let exponent_id = valid.replacen("\"id\":0", "\"id\":0e0", 1);
    let exponent_entry = valid.replacen("\"entry\":0", "\"entry\":0e0", 1);
    let local = core_program(json!({"tag":"let","ty":"i64","value":integer("7"),"body":{"tag":"local","ty":"i64","index":0}})).to_string();
    let exponent_local = local.replacen("\"index\":0", "\"index\":0e0", 1);
    let fractional_local = local.replacen("\"index\":0", "\"index\":0.0", 1);
    for raw in [
        duplicate_top,
        duplicate_nested,
        exponent_id,
        exponent_entry,
        exponent_local,
        fractional_local,
        "{broken".to_owned(),
    ] {
        core_outcome(&raw, &[], 1, json!({"outcome":"invalid_ir"}));
    }
}

#[test]
fn core_import_checks_unselected_branches_unused_functions_and_call_signatures() {
    use serde_json::json;
    let invalid_branch = json!({"tag":"if","ty":"i64","condition":{"tag":"boolean","ty":"bool","value":true},"then":integer("7"),"else":{"tag":"local","ty":"i64","index":0}});
    core_outcome(
        &core_program(invalid_branch).to_string(),
        &[],
        1,
        json!({"outcome":"invalid_ir"}),
    );
    let mut bad_unused = core_program(integer("7"));
    bad_unused["functions"].as_array_mut().unwrap().push(json!({"id":1,"name":"unused","params":[],"result":"i64","body":{"tag":"boolean","ty":"bool","value":false}}));
    core_outcome(
        &bad_unused.to_string(),
        &[],
        1,
        json!({"outcome":"invalid_ir"}),
    );
    let mut bad_call = core_program(
        json!({"tag":"call","ty":"i64","function":1,"arguments":[{"tag":"boolean","ty":"bool","value":true}]}),
    );
    bad_call["functions"].as_array_mut().unwrap().push(json!({"id":1,"name":"identity","params":["i64"],"result":"i64","body":{"tag":"local","ty":"i64","index":0}}));
    core_outcome(
        &bad_call.to_string(),
        &[],
        1,
        json!({"outcome":"invalid_ir"}),
    );
    core_outcome(
        &core_expression(json!({"tag":"call","ty":"i64","function":0,"arguments":[]})).to_string(),
        &[],
        1,
        json!({"outcome":"invalid_ir"}),
    );
}

#[test]
fn exported_discard_binding_has_independently_expected_de_bruijn_index() {
    use serde_json::json;
    let source = Source::new("fn main() -> i64 { let x = 7; 0; x }");
    let output = source.run("dump-core", &[]);
    assert_status(&output, 0, "export discarded binding");
    let exported: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("valid exported JSON");
    let expected = core_program(json!({
        "tag":"let","ty":"i64","value":integer("7"),
        "body":{"tag":"let","ty":"i64","value":integer("0"),
                "body":{"tag":"local","ty":"i64","index":1}}
    }));
    assert_eq!(exported, expected);
    core_outcome(
        &exported.to_string(),
        &[],
        0,
        json!({"outcome":"value","type":"i64","value":"7"}),
    );
}
