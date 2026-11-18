use anl::{
    DEFAULT_FUEL, MAX_FUEL, MAX_SOURCE_BYTES, codegen,
    core::{self, ImportError},
    diagnostic::{Diagnostic, Span},
    eval::{self, EvalError},
};
use std::{
    env,
    ffi::OsString,
    fs::File,
    io::{self, Read, Write},
    path::Path,
    process::ExitCode,
};

const HELP: &str = "ANL 0.1 checker, evaluator, and native compiler\n\nUsage:\n  anl check FILE\n  anl eval FILE [--fuel N]\n  anl build FILE [-o PATH]\n  anl run FILE\n  anl emit-c FILE\n  anl dump-core FILE\n  anl emit-boot FILE --out PATH [--target rv64-virt-sbi-v1]\n  anl eval-core FILE [--fuel N]\n  anl verify FILE [--solver PATH] [--timeout-ms N] [--json]\n  anl --version\n\nSource commands accept --target hosted|rv64-virt-sbi-v1.\nBoot source supports check, dump-core and emit-boot source bundles.\nBuild, execution and verification return unsupported (7) after static checking. Boot build requires\n--toolchain LOCK and -o PATH; no lock or external tool is used yet.\n\nSources prefer .anl; explicit legacy .apl roots retain .apl imports.\n\nBuild uses the host C11 compiler (CC or cc) at -O2. The default output\nis FILE without its extension, or FILE.out when it has no extension.\nRun builds a temporary native executable and executes it without fuel.\nEmit-c writes the validated C11 translation unit to stdout.\n\nInterpreter fuel defaults to 100000; N is decimal in 0..1000000000.\nEach evaluated core expression consumes one unit before execution.\nUnselected branches consume no fuel. Callee bodies count normally.\nEvaluation nesting is limited to 256; source/IR depth is limited to 128.\nSee spec/core-format.md and docs/native-compilation.md for details.\n\nExit codes: 0 success, 1 source/IR error, 2 defined runtime trap,\n3 resource limit, 4 invocation or infrastructure error.\nVerify additionally uses 5 failed, 6 unknown, and 7 unsupported or empty.\n";

enum CliError {
    Message(String),
    StderrUnavailable,
    ResourceLimit(&'static str),
}
impl From<String> for CliError {
    fn from(message: String) -> Self {
        Self::Message(message)
    }
}
impl From<&str> for CliError {
    fn from(message: &str) -> Self {
        Self::Message(message.into())
    }
}

impl From<anl::bounded::OutputError> for CliError {
    fn from(error: anl::bounded::OutputError) -> Self {
        match error {
            anl::bounded::OutputError::ResourceLimit(reason) => Self::ResourceLimit(reason),
            anl::bounded::OutputError::Infrastructure(reason) => Self::Message(reason),
        }
    }
}
fn main() -> ExitCode {
    match run(env::args_os().skip(1).collect()) {
        Ok(code) => ExitCode::from(code),
        Err(CliError::Message(message)) => {
            let _ = diagnostic(format_args!("anl: {message}"));
            ExitCode::from(4)
        }
        Err(CliError::StderrUnavailable) => ExitCode::from(4),
        Err(CliError::ResourceLimit(reason)) => ExitCode::from(
            if diagnostic(format_args!("anl: resource_limit: {reason}")).is_ok() {
                3
            } else {
                4
            },
        ),
    }
}
// Rust's standard streams suppress EBADF. Owned duplicates preserve write
// failures for read-only stdout/stderr instead of reporting silent success.
fn write_stdout(write: impl FnOnce(&mut File) -> io::Result<()>) -> Result<(), CliError> {
    let mut stdout = nix::unistd::dup(io::stdout())
        .map(File::from)
        .map_err(|error| CliError::Message(format!("cannot write stdout: {error}")))?;
    write(&mut stdout)
        .and_then(|()| stdout.flush())
        .map_err(|error| CliError::Message(format!("cannot write stdout: {error}")))
}
fn output(text: impl std::fmt::Display) -> Result<(), CliError> {
    write_stdout(|stdout| writeln!(stdout, "{text}"))
}
fn diagnostic(text: impl std::fmt::Display) -> Result<(), CliError> {
    let mut stderr = nix::unistd::dup(io::stderr())
        .map(File::from)
        .map_err(|_| CliError::StderrUnavailable)?;
    writeln!(stderr, "{text}")
        .and_then(|()| stderr.flush())
        .map_err(|_| CliError::StderrUnavailable)
}
fn run(args: Vec<OsString>) -> Result<u8, CliError> {
    if args.len() == 1 && args[0] == "--version" {
        output(concat!("anl ", env!("CARGO_PKG_VERSION")))?;
        return Ok(0);
    }
    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        output(HELP.trim_end())?;
        return Ok(0);
    }
    if args.first().is_some_and(|arg| arg == "verify") {
        return verify_command(&args[1..]);
    }
    let usage = "invalid invocation; use anl --help";
    let command = args.first().and_then(|arg| arg.to_str()).ok_or(usage)?;
    if !matches!(
        command,
        "check" | "eval" | "dump-core" | "eval-core" | "build" | "run" | "emit-c" | "emit-boot"
    ) || args.len() < 2
    {
        return Err(usage.into());
    }
    let mut fuel = DEFAULT_FUEL;
    let mut fuel_seen = false;
    let mut target = anl::TargetSelection::Auto;
    let mut target_seen = false;
    let mut destination_arg = None;
    let mut toolchain = None;
    let mut out = None;
    let mut i = 2;
    while i < args.len() {
        let value = args.get(i + 1).ok_or(usage)?;
        match args[i].to_str() {
            Some("--fuel") if matches!(command, "eval" | "eval-core") && !fuel_seen => {
                let text = value
                    .to_str()
                    .ok_or("fuel must be decimal in 0..1000000000")?;
                if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
                    return Err("fuel must be decimal in 0..1000000000".into());
                }
                fuel = text
                    .parse::<u64>()
                    .ok()
                    .filter(|n| *n <= MAX_FUEL)
                    .ok_or("fuel must be decimal in 0..1000000000")?;
                fuel_seen = true;
            }
            Some("--target") if command != "eval-core" && !target_seen => {
                target = parse_target(value)?;
                target_seen = true;
            }
            Some("-o") if command == "build" && destination_arg.is_none() => {
                destination_arg = Some(value)
            }
            Some("--toolchain") if command == "build" && toolchain.is_none() => {
                toolchain = Some(value)
            }
            Some("--out") if command == "emit-boot" && out.is_none() => out = Some(value),
            _ => return Err(usage.into()),
        }
        i += 2;
    }
    let path = Path::new(&args[1]);
    let filename = path.to_string_lossy();
    let source = if command == "eval-core" {
        let file = File::open(path).map_err(|error| format!("cannot read {filename}: {error}"))?;
        let mut bytes = Vec::new();
        file.take(MAX_SOURCE_BYTES as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("cannot read {filename}: {error}"))?;
        if bytes.len() > MAX_SOURCE_BYTES {
            output("{\"outcome\":\"resource_limit\"}")?;
            diagnostic(format_args!(
                "{filename}:1:1: resource_limit: input exceeds 1048576 bytes"
            ))?;
            return Ok(3);
        }
        match String::from_utf8(bytes) {
            Ok(text) => text,
            Err(error) => {
                output("{\"outcome\":\"invalid_ir\"}")?;
                let offset = error.utf8_error().valid_up_to();
                let valid = std::str::from_utf8(&error.as_bytes()[..offset]).unwrap_or("");
                diagnostic(
                    Diagnostic::new(
                        Span {
                            source_id: 0,
                            start: offset,
                            end: offset,
                        },
                        "input is not valid UTF-8",
                    )
                    .render(&filename, valid),
                )?;
                return Ok(1);
            }
        }
    } else {
        String::new()
    };
    if command == "eval-core" {
        let is_boot = serde_json::from_str::<serde_json::Value>(&source)
            .ok()
            .is_some_and(|v| {
                v.get("schema").and_then(serde_json::Value::as_str) == Some(anl::boot::SCHEMA)
            });
        if is_boot {
            match anl::boot::import_core(&source) {
                Ok(_) => {
                    output("{\"outcome\":\"unsupported_boot_operation\"}")?;
                    return Ok(7);
                }
                Err(error) => {
                    let (code, tag) = match &error {
                        ImportError::Invalid(_) => (1, "invalid_ir"),
                        ImportError::ResourceLimit(_) => (3, "resource_limit"),
                    };
                    output(serde_json::json!({"outcome":tag}))?;
                    diagnostic(format_args!("{filename}: {tag}: {error}"))?;
                    return Ok(code);
                }
            }
        }
        let artifact = match core::import(&source) {
            Ok(artifact) => artifact,
            Err(error) => {
                let (code, tag) = match &error {
                    ImportError::Invalid(_) => (1, "invalid_ir"),
                    ImportError::ResourceLimit(_) => (3, "resource_limit"),
                };
                output(serde_json::json!({"outcome":tag}))?;
                diagnostic(format_args!("{filename}: {tag}: {error}"))?;
                return Ok(code);
            }
        };
        let result = evaluate(&artifact.program, artifact.entry, fuel)?;
        output(core::outcome(&result))?;
        return report_execution(result, &filename, &source, None);
    }
    let checked = match anl::compile_target_file(path, target) {
        Ok(program) => program,
        Err(anl::TargetCompileError::Conflict(message)) => return Err(message.into()),
        Err(anl::TargetCompileError::Source(error)) => {
            diagnostic(error.render(&filename, &source))?;
            return Ok(if error.infrastructure {
                4
            } else if error.resource_limit {
                3
            } else {
                1
            });
        }
    };
    if command == "emit-boot" && out.is_none() {
        return Err("emit-boot requires --out PATH".into());
    }
    let program = match checked {
        anl::CheckedSource::Boot(program) => {
            if command == "check" {
                return Ok(0);
            }
            if command == "dump-core" {
                let text = anl::boot::export_core(&program)?;
                write_stdout(|stdout| stdout.write_all(text.as_bytes()))?;
                return Ok(0);
            }
            if command == "emit-boot" {
                let pair = anl::boot::lower(program)?;
                anl::boot::emit(&pair)?.publish(out.as_ref().expect("required boot output"))?;
                return Ok(0);
            }
            if command == "build" && (toolchain.is_none() || destination_arg.is_none()) {
                return Err("boot build requires --toolchain LOCK and -o PATH".into());
            }
            let state = if matches!(command, "emit-boot" | "build") {
                "implemented"
            } else {
                "supported"
            };
            diagnostic(format_args!(
                "unsupported_boot_operation: {command} is not {state} for rv64-virt-sbi-v1"
            ))?;
            return Ok(7);
        }
        anl::CheckedSource::Hosted(program) => program.into_program(),
    };
    if toolchain.is_some() {
        return Err("--toolchain is unavailable for hosted builds".into());
    }
    if command == "emit-boot" {
        diagnostic("unsupported_boot_operation: emit-boot requires rv64-virt-sbi-v1 source")?;
        return Ok(7);
    }
    if command == "check" {
        return Ok(0);
    }
    let entry = match program.entry() {
        Ok(entry) => entry,
        Err(error) => {
            diagnostic(error.render(&filename, &source))?;
            return Ok(1);
        }
    };
    if command == "dump-core" {
        output(core::export(&program, entry)?)?;
        return Ok(0);
    }
    if command == "emit-c" {
        let c = codegen::emit_c(&program, entry)?;
        if program.has_memory()
            || program.has_flat_products()
            || program.effective_revision() == anl::types::IrRevision::WordsV4
        {
            write_stdout(|stdout| stdout.write_all(c.as_bytes()))?;
        } else {
            output(c)?;
        }
        return Ok(0);
    }
    if command == "build" {
        let default = if path.extension().is_some() {
            path.with_extension("")
        } else {
            let mut name = path.as_os_str().to_os_string();
            name.push(".out");
            name.into()
        };
        let destination = destination_arg.map(Path::new).unwrap_or(&default);
        #[cfg(feature = "memory-evidence")]
        if let Some(evidence) = anl::memory_evidence::EvidenceOptions::from_environment(&program)? {
            codegen::build_evidence(&program, entry, path, destination, &evidence)?;
            return Ok(0);
        }
        codegen::build(&program, entry, path, destination)?;
        return Ok(0);
    }
    if command == "run" {
        #[cfg(feature = "memory-evidence")]
        if let Some(evidence) = anl::memory_evidence::EvidenceOptions::from_environment(&program)? {
            return codegen::run_evidence(&program, entry, path, &evidence).map_err(CliError::from);
        }
        return codegen::run(&program, entry, path).map_err(CliError::from);
    }
    let result = evaluate(&program, entry, fuel)?;
    if let Ok(value) = &result {
        output(value)?;
    }
    report_execution(result, &filename, &source, Some(&program))
}
fn evaluate(
    program: &anl::types::Program,
    entry: usize,
    fuel: u64,
) -> Result<Result<eval::Value, EvalError>, CliError> {
    #[cfg(feature = "memory-evidence")]
    if let Some(options) = anl::memory_evidence::EvidenceOptions::from_environment(program)? {
        return Ok(eval::evaluate_evidence(program, entry, fuel, &options));
    }
    Ok(eval::evaluate(program, entry, fuel))
}
fn report_execution(
    result: Result<eval::Value, EvalError>,
    filename: &str,
    source: &str,
    program: Option<&anl::types::Program>,
) -> Result<u8, CliError> {
    let render = |error: Diagnostic| {
        let error = if let Some(program) = program {
            program.source_diagnostic(error)
        } else {
            error
        };
        error.render(filename, source)
    };
    Ok(match result {
        Ok(_) => 0,
        Err(EvalError::Trap { kind, span }) => {
            diagnostic(render(Diagnostic::new(span, kind.as_str())))?;
            2
        }
        Err(EvalError::ResourceLimit { reason, span }) => {
            diagnostic(render(Diagnostic::resource(span, reason)))?;
            3
        }
        Err(EvalError::Infrastructure(reason)) => {
            diagnostic(format_args!("{filename}: infrastructure: {reason}"))?;
            4
        }
        Err(EvalError::InvalidIr) => {
            diagnostic(format_args!(
                "{filename}: invalid_ir: evaluator invariant failed"
            ))?;
            1
        }
    })
}

fn parse_target(value: &OsString) -> Result<anl::TargetSelection, CliError> {
    match value.to_str() {
        Some("hosted") => Ok(anl::TargetSelection::Hosted),
        Some("rv64-virt-sbi-v1") => Ok(anl::TargetSelection::Rv64VirtSbiV1),
        _ => Err("target must be hosted or rv64-virt-sbi-v1".into()),
    }
}
fn boot_verification(json: bool) -> Result<u8, CliError> {
    if json {
        output(serde_json::json!({
            "schema":"anl-boot-verify-v1", "semantic_revision":"anl-boot-rv64-virt-v1",
            "verification_revision":"anl-boot-unsupported-v1", "status":"unsupported",
            "reason":"unsupported_boot_operation", "trust":"not_established",
            "scope":{"functions":"all_loaded", "arithmetic_safety":false, "partial_correctness":false,
                "termination_proved":false, "native_correctness":false, "hardware_correctness":false,
                "model_proof":null, "fragment":"boot_unsupported"},
            "type_checked":true, "tested":false, "dynamic_checks":false, "contracts_erased":true,
            "compiler":null, "solver":null, "limits":{}, "obligations":[],
            "message":"Contract verification is not implemented for the boot profile; static checking does not establish hardware or native correctness."
        }))?;
    } else {
        output(
            "unsupported_boot_operation: contract verification is not implemented for rv64-virt-sbi-v1; trust=not_established",
        )?;
    }
    Ok(7)
}

fn verify_command(args: &[OsString]) -> Result<u8, CliError> {
    let usage = "usage: anl verify FILE [--solver PATH] [--timeout-ms N] [--json]";
    let path = args.first().ok_or(usage)?;
    let mut options = anl::verify::VerifyOptions::default();
    let mut json = false;
    let mut target = anl::TargetSelection::Auto;
    let mut target_seen = false;
    let mut solver_seen = false;
    let mut timeout_seen = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].to_str() {
            Some("--target") if !target_seen => {
                target = parse_target(args.get(i + 1).ok_or(usage)?)?;
                target_seen = true;
                i += 2;
            }
            Some("--json") if !json => {
                json = true;
                i += 1;
            }
            Some("--solver") if !solver_seen => {
                options.solver = args.get(i + 1).ok_or(usage)?.into();
                solver_seen = true;
                i += 2;
            }
            Some("--timeout-ms") if !timeout_seen => {
                let n = args.get(i + 1).and_then(|s| s.to_str()).ok_or(usage)?;
                if n.is_empty() || !n.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(usage.into());
                }
                options.timeout_ms = n
                    .parse()
                    .ok()
                    .filter(|n| (1..=600_000).contains(n))
                    .ok_or(usage)?;
                timeout_seen = true;
                i += 2;
            }
            _ => return Err(usage.into()),
        }
    }
    let report = match anl::compile_target_file(Path::new(path), target) {
        Ok(anl::CheckedSource::Boot(_)) => return boot_verification(json),
        Ok(anl::CheckedSource::Hosted(program)) => match program.verify(&options) {
            Ok(report) => report,
            Err(error) => {
                diagnostic(error.render(&path.to_string_lossy(), ""))?;
                anl::verify::VerificationReport::source_error(&error)
            }
        },
        Err(anl::TargetCompileError::Conflict(message)) => return Err(message.into()),
        Err(anl::TargetCompileError::Source(error)) => {
            diagnostic(error.render(&path.to_string_lossy(), ""))?;
            anl::verify::VerificationReport::source_error(&error)
        }
    };
    if json {
        output(report.json())?;
    } else {
        output(report.human())?;
    }
    Ok(report.exit_code())
}
