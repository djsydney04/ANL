//! Filesystem, interface, source-location, and native-publication module contracts.
use apl::{
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
            "apl-modules-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn file(&self, name: &str, text: impl AsRef<[u8]>) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }
    fn main(&self, text: &str) -> PathBuf {
        self.file("main.apl", text)
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
            panic!("module command timed out: {:?}", child.wait_with_output());
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}
fn cli(command: &str, path: &Path) -> Command {
    let mut process = Command::new(env!("CARGO_BIN_EXE_apl"));
    process.arg(command).arg(path);
    process
}
fn succeeds(output: Output, stdout: &[u8]) {
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(output.stdout, stdout);
    assert!(output.stderr.is_empty(), "{output:?}");
}
fn value(path: &Path, expected: i64) -> apl::types::Program {
    let program = apl::compile_file(path).unwrap();
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100_000),
        Ok(Value::Integer(expected))
    );
    program
}

#[test]
fn documented_library_executes_through_checker_interpreter_and_native_cli() {
    let main = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/modules/main.apl");
    value(&main, 42);
    succeeds(bounded(cli("check", &main)), b"");
    succeeds(bounded(cli("eval", &main)), b"42\n");
    succeeds(bounded(cli("run", &main)), b"42\n");
    let project = Project::new();
    let binary = project.0.join("modular executable");
    let mut build = cli("build", &main);
    build.arg("-o").arg(&binary);
    succeeds(bounded(build), b"");
    succeeds(bounded(Command::new(&binary)), b"42\n");
    let emitted = bounded(cli("emit-c", &main));
    assert_eq!(emitted.status.code(), Some(0), "{emitted:?}");
    let c = project.file("modules.c", &emitted.stdout);
    let mut cc = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
    cc.args(["-std=c11", "-pedantic-errors", "-O0"])
        .arg(c)
        .arg("-o")
        .arg(&binary);
    succeeds(bounded(cc), b"");
    succeeds(bounded(Command::new(&binary)), b"42\n");
}

#[test]
fn same_named_functions_and_user_mangling_lookalikes_stay_distinct_in_core() {
    let project = Project::new();
    let main = project.main("mod a; mod b; fn __apl_m1_value()->i64{2} fn main()->i64{a::value()+b::value()+__apl_m1_value()}");
    project.file("a.apl", "pub fn value()->i64{15} pub fn main()->i64{999}");
    project.file("b.apl", "pub fn value()->i64{25}");
    let program = value(&main, 42);
    let json = core::export(&program, program.entry().unwrap());
    assert_eq!(
        json,
        core::export(&apl::compile_file(&main).unwrap(), program.entry().unwrap())
    );
    let imported = core::import(&json.to_string()).unwrap();
    assert_eq!(
        eval::evaluate(&imported.program, imported.entry, 1000),
        Ok(Value::Integer(42))
    );
    project.main("mod a;");
    assert!(apl::compile_file(&main).unwrap().entry().is_err());
}

#[test]
fn contextual_words_preserve_old_identifiers_and_pure_compile_never_loads_modules() {
    let program = apl::compile("fn mod(pub:i64)->i64{pub+1} fn pub(mod:i64)->i64{mod+1} fn main()->i64{let mod=40; pub(mod)+1}").unwrap();
    assert_eq!(
        eval::evaluate(&program, program.entry().unwrap(), 100),
        Ok(Value::Integer(42))
    );
    let error = apl::compile("mod absent; fn main()->i64{42}").unwrap_err();
    assert!(error.message.contains("compile_file"));
    assert!(!error.infrastructure);
    let project = Project::new();
    let main = project.main("mod pub; fn main()->i64{pub::mod(41)}");
    project.file("pub.apl", "pub fn mod(pub:i64)->i64{pub+1}");
    value(&main, 42);
}

#[test]
fn private_access_and_argument_mismatches_report_both_actual_files() {
    let project = Project::new();
    let main = project.main("mod math;\nfn main()->i64{math::hidden()}");
    let math = project.file(
        "math.apl",
        "\n\nfn hidden()->i64{42}\npub fn double(x:i64)->i64{x+x}",
    );
    let error = apl::compile_file(&main).unwrap_err();
    let rendered = error.render("wrong.apl", "");
    assert!(error.message.contains("private"), "{rendered}");
    assert!(
        rendered.contains(&format!("{}:2:", main.display())),
        "{rendered}"
    );
    assert!(
        rendered.contains(&format!("{}:3:", math.display())),
        "{rendered}"
    );
    project.main("mod math;\nfn main()->i64{math::double(true)}");
    let rendered = apl::compile_file(&main)
        .unwrap_err()
        .render("wrong.apl", "");
    assert!(rendered.contains("expected i64, found bool"), "{rendered}");
    assert!(
        rendered.contains(&format!("{}:2:", main.display())),
        "{rendered}"
    );
    assert!(
        rendered.contains(&format!("{}:4:", math.display())),
        "{rendered}"
    );
}

#[test]
fn unused_imported_bodies_and_lexical_namespaces_are_checked() {
    let project = Project::new();
    let main = project.main("mod math; fn helper()->i64{42} fn main()->i64{42}");
    let math = project.file("math.apl", "\nfn unused()->i64{true}");
    let rendered = apl::compile_file(&main).unwrap_err().render("wrong", "");
    assert!(
        rendered.contains(&format!("{}:2:", math.display())),
        "{rendered}"
    );
    assert!(rendered.contains("expected i64, found bool"));
    project.file("math.apl", "pub fn unused()->i64{helper()}");
    assert!(
        apl::compile_file(&main)
            .unwrap_err()
            .message
            .contains("undefined function `helper`")
    );
    project.file("math.apl", "pub fn unused()->i64{42}");
    project.main("mod math; fn main()->i64{unused()}");
    assert!(
        apl::compile_file(&main)
            .unwrap_err()
            .message
            .contains("undefined function `unused`")
    );
}

#[test]
fn intermediate_visibility_is_enforced_and_local_namespace_calls_remain_usable() {
    let project = Project::new();
    let main = project.main("mod math; fn main()->i64{math::constants::seed()}");
    project.file(
        "math.apl",
        "mod constants; pub fn value()->i64{constants::seed()}",
    );
    project.file("constants.apl", "pub fn seed()->i64{42}");
    assert!(
        apl::compile_file(&main)
            .unwrap_err()
            .message
            .contains("module `constants` is private")
    );
    project.main("mod math; fn main()->i64{let math=1; math::value()}");
    value(&main, 42);
    project.file("math.apl", "pub mod constants;");
    project.main("mod math; fn main()->i64{math::constants::seed()}");
    value(&main, 42);
}

#[test]
fn shared_diamond_dependencies_have_one_identity() {
    let project = Project::new();
    let main = project.main("mod a; mod b; fn main()->i64{a::answer()+b::answer()}");
    project.file("a.apl", "mod shared; pub fn answer()->i64{shared::value()}");
    project.file("b.apl", "mod shared; pub fn answer()->i64{shared::value()}");
    project.file("shared.apl", "pub fn value()->i64{21}");
    let program = value(&main, 42);
    let json = core::export(&program, program.entry().unwrap());
    assert_eq!(json["functions"].as_array().unwrap().len(), 4);
}

#[test]
fn duplicates_cycles_unknown_paths_and_missing_files_are_actionable() {
    let project = Project::new();
    let main = project.main("mod a; mod a; fn main()->i64{42}");
    project.file("a.apl", "pub fn answer()->i64{42}");
    assert!(
        apl::compile_file(&main)
            .unwrap_err()
            .message
            .contains("duplicate name `a`")
    );
    project.main("mod a; fn a()->i64{42}");
    assert!(
        apl::compile_file(&main)
            .unwrap_err()
            .message
            .contains("duplicate name `a`")
    );
    project.main("mod a; fn main()->i64{a::missing()}");
    assert!(
        apl::compile_file(&main)
            .unwrap_err()
            .message
            .contains("undefined function `a::missing`")
    );
    project.file("a.apl", "mod main;");
    let error = apl::compile_file(&main).unwrap_err();
    assert!(error.message.contains("module import cycle:"));
    assert!(error.message.contains("main.apl") && error.message.contains("a.apl"));
    project.main("mod missing; fn main()->i64{42}");
    let output = bounded(cli("check", &main));
    assert_eq!(output.status.code(), Some(4));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("main.apl:1:1") && stderr.contains("missing.apl"),
        "{stderr}"
    );
    fs::create_dir(project.0.join("missing.apl")).unwrap();
    let output = bounded(cli("check", &main));
    assert_eq!(output.status.code(), Some(4));
    assert!(String::from_utf8_lossy(&output.stderr).contains("not a regular file"));
}

#[test]
fn imported_invalid_utf8_and_runtime_traps_use_imported_source_locations() {
    let project = Project::new();
    let main = project.main("mod math; fn main()->i64{math::fail()}");
    let math = project.file("math.apl", b"// valid\n\xff");
    let rendered = apl::compile_file(&main).unwrap_err().render("wrong", "");
    assert!(
        rendered.contains(&format!("{}:2:1", math.display())),
        "{rendered}"
    );
    project.file("math.apl", "\n\npub fn fail()->i64{1 / 0}");
    let output = bounded(cli("eval", &main));
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains(&format!("{}:3:", math.display())),
        "{stderr}"
    );
    assert!(stderr.contains("division_by_zero"));
    let output = bounded(cli("run", &main));
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(output.stderr, b"division_by_zero\n");

    let program = apl::compile_file(&main).unwrap();
    project.file("math.apl", "// source changed after compilation");
    let Err(eval::EvalError::Trap { kind, span }) =
        eval::evaluate(&program, program.entry().unwrap(), 100)
    else {
        panic!("expected imported arithmetic trap")
    };
    let rendered = program
        .source_diagnostic(apl::diagnostic::Diagnostic::new(span, kind.as_str()))
        .render("wrong", "");
    assert!(
        rendered.contains(&format!("{}:3:", math.display())),
        "{rendered}"
    );
    let missing = apl::diagnostic::Diagnostic::new(
        apl::diagnostic::Span {
            source_id: usize::MAX,
            start: usize::MAX,
            end: usize::MAX,
        },
        "missing metadata",
    );
    assert!(missing.render("fallback", "é").starts_with("fallback:1:2:"));
}

#[test]
fn import_depth_file_count_source_bytes_paths_and_diagnostics_are_bounded() {
    let project = Project::new();
    let main = project.main("mod m0; fn main()->i64{42}");
    for i in 0..32 {
        project.file(&format!("m{i}.apl"), format!("mod m{};", i + 1));
    }
    project.file("m32.apl", "");
    let error = apl::compile_file(&main).unwrap_err();
    assert!(error.resource_limit && error.message.contains("depth"));
    let imports = (0..128)
        .map(|i| {
            project.file(&format!("m{i}.apl"), "");
            format!("mod m{i};")
        })
        .collect::<String>();
    project.main(&imports);
    let error = apl::compile_file(&main).unwrap_err();
    assert!(error.resource_limit && error.message.contains("128"));
    project.main("mod large;");
    project.file("large.apl", " ".repeat(apl::MAX_SOURCE_BYTES + 1));
    assert!(apl::compile_file(&main).unwrap_err().resource_limit);
    project.main(&(0..8).map(|i| format!("mod m{i};")).collect::<String>());
    for i in 0..8 {
        project.file(&format!("m{i}.apl"), " ".repeat(apl::MAX_SOURCE_BYTES));
    }
    let error = apl::compile_file(&main).unwrap_err();
    assert!(error.resource_limit && error.message.contains("8388608"));
    let error =
        apl::compile(&format!("fn main()->i64{{{}()}}", "a::".repeat(33) + "f")).unwrap_err();
    assert!(error.resource_limit && error.message.contains("segments"));
    let error = apl::compile(&format!("fn main()->i64{{{}()}}", "x".repeat(20_000))).unwrap_err();
    assert!(error.message.len() <= 8192);
    assert!(error.render("case", "").len() <= 8192);
}

#[cfg(unix)]
#[test]
fn symlinks_use_canonical_import_directories_and_hardlink_modules_are_ambiguous() {
    let project = Project::new();
    let real = project.0.join("real");
    fs::create_dir(&real).unwrap();
    fs::write(
        real.join("main.apl"),
        "mod math; fn main()->i64{math::answer()}",
    )
    .unwrap();
    fs::write(real.join("math.apl"), "pub fn answer()->i64{42}").unwrap();
    let alias = project.0.join("alias.apl");
    std::os::unix::fs::symlink(real.join("main.apl"), &alias).unwrap();
    value(&alias, 42);
    let main = project.main("mod a; mod b; fn main()->i64{42}");
    let a = project.file("a.apl", "pub fn value()->i64{42}");
    fs::hard_link(a, project.0.join("b.apl")).unwrap();
    assert!(
        apl::compile_file(main)
            .unwrap_err()
            .message
            .contains("ambiguous module identity")
    );
}

#[cfg(unix)]
#[test]
fn native_outputs_cannot_replace_any_transitive_source_or_alias() {
    let project = Project::new();
    let main = project.main("mod math; fn main()->i64{math::answer()}");
    project.file(
        "math.apl",
        "mod shared; pub fn answer()->i64{shared::value()}",
    );
    let original = "pub fn value()->i64{42}";
    let shared = project.file("shared.apl", original);
    let symbolic = project.0.join("symbolic");
    let hard = project.0.join("hard");
    std::os::unix::fs::symlink(&shared, &symbolic).unwrap();
    fs::hard_link(&shared, &hard).unwrap();
    for destination in [&shared, &symbolic, &hard] {
        let mut command = cli("build", &main);
        command.arg("-o").arg(destination);
        let output = bounded(command);
        assert_eq!(output.status.code(), Some(4), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("overwrite the source"));
        assert_eq!(fs::read_to_string(destination).unwrap(), original);
        assert_eq!(fs::read_to_string(&shared).unwrap(), original);
    }
    // Passing another source path cannot disable retained input protection.
    let program = value(&main, 42);
    let unrelated = project.file("unrelated.apl", "fn main()->i64{0}");
    assert!(
        apl::codegen::build(&program, program.entry().unwrap(), &unrelated, &hard)
            .unwrap_err()
            .contains("overwrite the source")
    );
}

#[cfg(unix)]
#[test]
fn native_publication_rechecks_transitive_inputs_after_the_external_compiler() {
    use std::os::unix::fs::PermissionsExt;
    let project = Project::new();
    let main = project.main("mod math; fn main()->i64{math::answer()}");
    project.file(
        "math.apl",
        "mod shared; pub fn answer()->i64{shared::value()}",
    );
    let original = "pub fn value()->i64{42}";
    let shared = project.file("shared.apl", original);
    let output = project.0.join("output");
    let cc = project.file("cc-wrapper", "#!/bin/sh\n\"$APL_TEST_CC\" \"$@\" || exit $?\nln -f \"$APL_TEST_INPUT\" \"$APL_TEST_OUTPUT\"\n");
    fs::set_permissions(&cc, fs::Permissions::from_mode(0o700)).unwrap();
    let mut command = cli("build", &main);
    command
        .arg("-o")
        .arg(&output)
        .env("CC", cc)
        .env(
            "APL_TEST_CC",
            std::env::var_os("CC").unwrap_or_else(|| "cc".into()),
        )
        .env("APL_TEST_INPUT", &shared)
        .env("APL_TEST_OUTPUT", &output);
    let result = bounded(command);
    assert_eq!(result.status.code(), Some(4), "{result:?}");
    assert!(String::from_utf8_lossy(&result.stderr).contains("overwrite the source"));
    assert_eq!(fs::read_to_string(&shared).unwrap(), original);
    assert_eq!(fs::read_to_string(&output).unwrap(), original);
}
