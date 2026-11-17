//! Execute real host binaries and compare independent scalar expectations and the
//! reference evaluator. These checks are evidence, not a compiler-correctness proof.
use apl::{
    codegen, core,
    eval::{self, EvalError, Value},
};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "apl-native-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn source(&self, source: &str) -> PathBuf {
        let path = self.0.join("program.apl");
        fs::write(&path, source).unwrap();
        path
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn bounded(mut command: Command) -> Output {
    let context = format!("{command:?}");
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start command");
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if child.try_wait().unwrap().is_some() {
            return child.wait_with_output().unwrap();
        }
        if Instant::now() > deadline {
            let _ = child.kill();
            panic!(
                "command exceeded twenty seconds: {context}\n{:?}",
                child.wait_with_output()
            );
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}
fn cli(command: &str, source: &Path) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_apl"));
    cmd.arg(command).arg(source);
    cmd
}
fn status(output: &Output, expected: i32) {
    assert_eq!(output.status.code(), Some(expected), "{output:?}");
}
fn compile_c(fixture: &Fixture, c: &str, optimization: &str, sanitizer: bool) -> PathBuf {
    let source = fixture.0.join("generated.c");
    let binary = fixture.0.join("native");
    fs::write(&source, c).unwrap();
    let mut cmd = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
    cmd.args(["-std=c11", "-pedantic-errors", optimization]);
    if sanitizer {
        cmd.args(["-fsanitize=undefined", "-fno-sanitize-recover=all"]);
    }
    let output = bounded({
        cmd.arg(source).arg("-o").arg(&binary);
        cmd
    });
    status(&output, 0);
    binary
}
fn assert_native(source: &str, expected: Result<i64, &str>, sanitizer: bool) {
    let fixture = Fixture::new();
    let program = apl::compile(source).unwrap();
    let entry = program.entry().unwrap();
    let c = codegen::emit_c(&program, entry).unwrap();
    let reference = eval::evaluate(&program, entry, 10_000_000);
    if program.has_local_state() {
        let wire = core::export(&program, entry).unwrap();
        assert_eq!(wire["schema"], "apl-core-v1");
        let imported = core::import(&wire.to_string()).unwrap();
        assert_eq!(
            core::outcome(&eval::evaluate(
                &imported.program,
                imported.entry,
                10_000_000
            )),
            core::outcome(&reference),
            "imported state semantics differ: {source}"
        );
    }
    match (expected, reference) {
        (Ok(want), Ok(Value::Integer(got))) => assert_eq!(got, want, "{source}"),
        (Err(want), Err(EvalError::Trap { kind, .. })) => {
            assert_eq!(kind.as_str(), want, "{source}")
        }
        (_, actual) => panic!("reference mismatch for {source}: {actual:?}"),
    }
    for optimization in ["-O0", "-O2"] {
        let binary = compile_c(&fixture, &c, optimization, sanitizer);
        let output = bounded(Command::new(binary));
        match expected {
            Ok(value) => {
                status(&output, 0);
                assert_eq!(
                    output.stdout,
                    format!("{value}\n").as_bytes(),
                    "{source} {optimization}"
                );
                assert!(
                    output.stderr.is_empty(),
                    "{source} {optimization}: {output:?}"
                );
            }
            Err(tag) => {
                status(&output, 2);
                assert!(
                    output.stdout.is_empty(),
                    "{source} {optimization}: {output:?}"
                );
                assert_eq!(
                    output.stderr,
                    format!("{tag}\n").as_bytes(),
                    "{source} {optimization}"
                );
            }
        }
    }
}
fn expression(expr: &str, expected: Result<i64, &str>, sanitizer: bool) {
    assert_native(&format!("fn main()->i64 {{ {expr} }}"), expected, sanitizer);
}

#[test]
fn portable_checked_arithmetic_matches_reference_at_both_optimization_levels() {
    for (expr, want) in [
        ("9223372036854775807", i64::MAX),
        ("-9223372036854775808", i64::MIN),
        ("9223372036854775807 + -9223372036854775808", -1),
        ("-9223372036854775808 - -1", -9223372036854775807),
        ("9223372036854775807 - 1", 9223372036854775806),
        ("-9223372036854775808 * 1", i64::MIN),
        ("0 * -9223372036854775808", 0),
        ("-9223372036854775808 * 0", 0),
        ("-3037000499 * -3037000499", 9223372030926249001),
        ("-4611686018427387904 * 2", i64::MIN),
        ("2 * -4611686018427387904", i64::MIN),
        ("-9223372036854775808 / 1", i64::MIN),
        ("-9223372036854775808 % 1", 0),
        ("-9223372036854775808 / 3", -3074457345618258602),
        ("-9223372036854775808 % 3", -2),
        ("7 / -3", -2),
        ("-7 % 3", -1),
        ("-7 / -3", 2),
        ("7 % -3", 1),
        ("-7 % -3", -1),
        ("0 / -9223372036854775808", 0),
        ("-(-9223372036854775807)", i64::MAX),
    ] {
        expression(expr, Ok(want), false);
    }
    for expr in [
        "9223372036854775807 + 1",
        "-9223372036854775808 + -1",
        "-9223372036854775808 - 1",
        "9223372036854775807 - -1",
        "9223372036854775807 * 2",
        "2 * -9223372036854775808",
        "-9223372036854775808 * 2",
        "-3037000500 * -3037000500",
        "-9223372036854775808 * -1",
        "-1 * -9223372036854775808",
        "-(-9223372036854775808)",
        "-9223372036854775808 / -1",
        "-9223372036854775808 % -1",
    ] {
        expression(expr, Err("arithmetic_overflow"), false);
    }
    for expr in ["1 / 0", "0 / 0", "-1 / 0", "1 % 0", "0 % 0", "-1 % 0"] {
        expression(expr, Err("division_by_zero"), false);
    }
}

#[test]
fn control_flow_calls_scopes_and_scalar_abi_match_reference() {
    assert_native(
        "fn main()->i64 { combine(8, true, make_unit()) } fn make_unit()->unit { () } fn combine(n:i64, b:bool, u:unit)->i64 { if b && u == () { n * 5 + 2 } else { 0 } }",
        Ok(42),
        false,
    );
    assert_native(
        "fn main()->i64 { if even(12) && !odd(12) { 42 } else { 0 } } fn even(n:i64)->bool { if n == 0 { true } else { odd(n - 1) } } fn odd(n:i64)->bool { if n == 0 { false } else { even(n - 1) } }",
        Ok(42),
        false,
    );
    assert_native(
        "fn main()->i64 { let x=40; { let x=8; x + 1 }; 1; let y=if true { let x=1; x + 1 } else { 1 / 0 }; x+y }",
        Ok(42),
        false,
    );
    for expr in [
        "if false && (1 / 0 == 1) { 0 } else { 42 }",
        "if true || (9223372036854775807 + 1 == 0) { 42 } else { 0 }",
        "if (if false { 1 / 0 == 0 } else { true }) { 42 } else { 1 / 0 }",
        "if !false && 1 < 2 && 2 <= 2 && 3 > 2 && 3 >= 3 && true != false && () == () { 42 } else { 0 }",
        "if () != () || (true == false) || (2 < 1) { 0 } else { 42 }",
    ] {
        expression(expr, Ok(42), false);
    }
}

#[test]
fn mutable_scopes_loop_back_edges_and_argument_order_match_core_and_native() {
    for (source, expected) in [
        ("fn main()->i64 { let mut x=1; { x=x+2; }; x }", 3),
        (
            "fn main()->i64 { let mut x=1; let old=x; x=3; old*10+x }",
            13,
        ),
        (
            "fn main()->i64 { let mut x=1; let a={x=3;x}+{x=x+4;x}; a*10+x }",
            107,
        ),
        (
            "fn main()->i64 { let mut x=0; while ({x=x+1;x<4}) {} x }",
            4,
        ),
        (
            "fn main()->i64 { let mut x=0; while ({x=x+1;x<10}) {x=x+2;} x }",
            10,
        ),
        (
            "fn main()->i64 { let mut x=1; let a=pack({x=x+1;x},{x=x*3;x},{x=x+1;x}); a*10+x } fn pack(a:i64,b:i64,c:i64)->i64 {100*a+10*b+c}",
            2677,
        ),
        (
            "fn main()->i64 {let mut x=7;let r=change(x,x);r*10+x} fn change(a:i64,b:i64)->i64 {let mut a=a;a=99;a+b}",
            1067,
        ),
        (
            "fn main()->i64 {let mut x=1;x={let mut y=9;x=x+2;let z=y;x+z};x}",
            12,
        ),
        (
            "fn main()->i64 {let mut i=0;let mut sum=0;while (i<10) {let mut fresh=0;fresh=fresh+1;sum=sum+fresh;i=i+1;}sum}",
            10,
        ),
        (
            "fn main()->i64 {let mut x=0; false && {x=1;true};true || {x=2;false};x}",
            0,
        ),
        (
            "fn main()->i64 {let mut x=0;{x=1;true} && {x=x+2;true};{x=x+3;false} || {x=x+4;true};x}",
            10,
        ),
        (
            "fn main()->i64 {let mut x=1;{let x=9;x};while (false) {x=2;}x}",
            1,
        ),
        (
            "fn main()->i64 {let mut i=0;let mut n=0;while (i<3) {let mut j=0;while (j<2) {n=n+1;j=j+1;}i=i+1;}n}",
            6,
        ),
        (
            "fn main()->i64 {let mut b=false;let mut u=();b=true;u=();if b && u==() {42}else{0}}",
            42,
        ),
        (
            "fn main()->i64 {let mut x=0;while (x<300000) {x=x+1;}x}",
            300000,
        ),
    ] {
        assert_native(source, Ok(expected), false);
    }
}

#[test]
fn stateful_conditions_bodies_and_assignment_rhs_preserve_first_traps() {
    for (source, tag) in [
        (
            "fn main()->i64 {let mut x=0;while ({x=x+1;1/0==0}) {} 9223372036854775807+1}",
            "division_by_zero",
        ),
        (
            "fn main()->i64 {let mut x=0;while (x<1) {x=x+1;1/0;}9223372036854775807+1}",
            "division_by_zero",
        ),
        (
            "fn main()->i64 {let mut x=0;x={x=x+1;9223372036854775807+1};1/0}",
            "arithmetic_overflow",
        ),
        (
            "fn main()->i64 {let mut x=9223372036854775807;while (true) {x=x+1;}0}",
            "arithmetic_overflow",
        ),
    ] {
        assert_native(source, Err(tag), false);
    }
}

#[test]
fn first_trap_and_discard_effects_are_preserved() {
    for (source, tag) in [
        (
            "fn main()->i64 { (1 / 0) + (9223372036854775807 + 1) }",
            "division_by_zero",
        ),
        (
            "fn main()->i64 { (9223372036854775807 + 1) + (1 / 0) }",
            "arithmetic_overflow",
        ),
        (
            "fn choose(a:i64,b:i64)->i64 { b } fn main()->i64 { choose(1 / 0, 9223372036854775807 + 1) }",
            "division_by_zero",
        ),
        (
            "fn choose(a:i64,b:i64)->i64 { b } fn main()->i64 { choose(9223372036854775807 + 1, 1 / 0) }",
            "arithmetic_overflow",
        ),
        (
            "fn make_unit()->unit { 1 / 0; } fn main()->i64 { make_unit(); 42 }",
            "division_by_zero",
        ),
        (
            "fn main()->i64 { 9223372036854775807 + 1; 42 }",
            "arithmetic_overflow",
        ),
        (
            "fn main()->i64 { if true && (1 / 0 == 0) { 42 } else { 0 } }",
            "division_by_zero",
        ),
        (
            "fn main()->i64 { if false || (1 / 0 == 0) { 42 } else { 0 } }",
            "division_by_zero",
        ),
    ] {
        assert_native(source, Err(tag), false);
    }
}

#[test]
fn build_and_run_execute_a_host_machine_code_binary() {
    let fixture = Fixture::new();
    let source = fixture.source("fn main()->i64 { 9223372036854775807 }");
    let binary = fixture.0.join("native output ; $literal");
    let output = bounded({
        let mut cmd = cli("build", &source);
        cmd.arg("-o").arg(&binary);
        cmd
    });
    status(&output, 0);
    assert!(output.stdout.is_empty());
    let bytes = fs::read(&binary).unwrap();
    #[cfg(target_os = "macos")]
    assert_eq!(
        &bytes[..4],
        &[0xcf, 0xfa, 0xed, 0xfe],
        "expected a 64-bit Mach-O native image"
    );
    #[cfg(target_os = "linux")]
    assert_eq!(&bytes[..4], b"\x7fELF", "expected an ELF native image");
    let output = bounded(Command::new(binary));
    status(&output, 0);
    assert_eq!(output.stdout, b"9223372036854775807\n");
    let output = bounded(cli("run", &source));
    status(&output, 0);
    assert_eq!(output.stdout, b"9223372036854775807\n");
    status(&bounded(cli("build", &source)), 0);
    assert!(source.with_extension("").is_file());
    fs::write(&source, "fn main()->i64 { 1 / 0 }").unwrap();
    let output = bounded(cli("run", &source));
    status(&output, 2);
    assert_eq!(output.stderr, b"division_by_zero\n");
    let c = bounded(cli("emit-c", &source));
    status(&c, 0);
    let binary = compile_c(
        &fixture,
        std::str::from_utf8(&c.stdout).unwrap(),
        "-O0",
        false,
    );
    status(&bounded(Command::new(binary)), 2);
    assert!(fs::read_dir(&fixture.0).unwrap().all(|p| {
        !p.unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".apl-native-")
    }));
}

#[test]
fn rejected_source_and_build_failures_preserve_output_and_source() {
    let fixture = Fixture::new();
    let original = "fn main()->i64 { 42 }";
    let source = fixture.source(original);
    let binary = fixture.0.join("native");
    fs::write(&binary, b"previous artifact").unwrap();
    let mut missing = cli("build", &source);
    missing
        .arg("-o")
        .arg(&binary)
        .env("CC", fixture.0.join("missing cc"));
    let output = bounded(missing);
    status(&output, 4);
    assert!(String::from_utf8_lossy(&output.stderr).contains("cannot execute C compiler"));
    assert_eq!(fs::read(&binary).unwrap(), b"previous artifact");
    let mut failure = cli("build", &source);
    failure.arg("-o").arg(&binary).env("CC", "false");
    status(&bounded(failure), 4);
    assert_eq!(fs::read(&binary).unwrap(), b"previous artifact");
    let mut collision = cli("build", &source);
    collision.arg("-o").arg(&source);
    status(&bounded(collision), 4);
    assert_eq!(fs::read_to_string(&source).unwrap(), original);
    fs::write(&source, "fn main()->i64 { true }").unwrap();
    status(
        &bounded({
            let mut cmd = cli("build", &source);
            cmd.arg("-o").arg(&binary);
            cmd
        }),
        1,
    );
    assert_eq!(fs::read(&binary).unwrap(), b"previous artifact");
    assert!(fs::read_dir(&fixture.0).unwrap().all(|p| {
        !p.unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".apl-native-")
    }));
}

#[cfg(unix)]
#[test]
fn output_aliases_cannot_replace_source() {
    let fixture = Fixture::new();
    let original = "fn main()->i64 { 42 }";
    let source = fixture.source(original);
    let symlink = fixture.0.join("symlink");
    let hardlink = fixture.0.join("hardlink");
    std::os::unix::fs::symlink(&source, &symlink).unwrap();
    fs::hard_link(&source, &hardlink).unwrap();
    for alias in [symlink, hardlink] {
        let mut cmd = cli("build", &source);
        cmd.arg("-o").arg(&alias);
        let output = bounded(cmd);
        status(&output, 4);
        assert!(String::from_utf8_lossy(&output.stderr).contains("overwrite the source"));
        assert_eq!(fs::read_to_string(&source).unwrap(), original);
        assert_eq!(fs::read_to_string(&alias).unwrap(), original);
    }
}

#[test]
fn native_stream_failures_return_infrastructure_status() {
    let fixture = Fixture::new();
    for source in ["fn main()->i64 { 42 }", "fn main()->i64 { 1 / 0 }"] {
        let program = apl::compile(source).unwrap();
        let c = codegen::emit_c(&program, program.entry().unwrap()).unwrap();
        let binary = compile_c(&fixture, &c, "-O2", false);
        let (reader, writer) = std::io::pipe().unwrap();
        drop(reader);
        let mut command = Command::new(binary);
        if source.contains("1 / 0") {
            command.stderr(Stdio::from(writer));
        } else {
            command.stdout(Stdio::from(writer));
        }
        status(&command.output().unwrap(), 4);
    }
}

#[test]
fn emitted_c_checked_helpers_are_clean_under_undefined_behavior_sanitizer() {
    let probe = Fixture::new();
    let probe_source = probe.0.join("probe.c");
    let probe_binary = probe.0.join("probe");
    fs::write(&probe_source, "int main(void) { return 0; }\n").unwrap();
    let mut cmd = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
    cmd.arg("-fsanitize=undefined")
        .arg(&probe_source)
        .arg("-o")
        .arg(&probe_binary);
    let output = bounded(cmd);
    if !output.status.success() {
        eprintln!(
            "undefined-behavior sanitizer unavailable: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        return;
    }
    status(&bounded(Command::new(probe_binary)), 0);
    for (expr, expected) in [
        ("-9223372036854775808 + 1", Ok(-9223372036854775807)),
        ("9223372036854775807 - -1", Err("arithmetic_overflow")),
        ("-9223372036854775808 * -1", Err("arithmetic_overflow")),
        ("-9223372036854775808 * 1", Ok(i64::MIN)),
        ("2 * -4611686018427387904", Ok(i64::MIN)),
        ("-3037000500 * -3037000500", Err("arithmetic_overflow")),
        ("-(-9223372036854775808)", Err("arithmetic_overflow")),
        ("-9223372036854775808 / -1", Err("arithmetic_overflow")),
        ("-9223372036854775808 % -1", Err("arithmetic_overflow")),
        ("-9223372036854775808 % 0", Err("division_by_zero")),
    ] {
        expression(expr, expected, true);
    }
}
