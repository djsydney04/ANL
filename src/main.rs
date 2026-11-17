use apl::{
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

const HELP: &str = "APL 0.1 scalar checker, evaluator, and native compiler\n\nUsage:\n  apl check FILE\n  apl eval FILE [--fuel N]\n  apl build FILE [-o PATH]\n  apl run FILE\n  apl emit-c FILE\n  apl dump-core FILE\n  apl eval-core FILE [--fuel N]\n  apl verify FILE [--solver PATH] [--timeout-ms N] [--json]\n  apl --version\n\nBuild uses the host C11 compiler (CC or cc) at -O2. The default output\nis FILE without its extension, or FILE.out when it has no extension.\nRun builds a temporary native executable and executes it without fuel.\nEmit-c writes the validated C11 translation unit to stdout.\n\nInterpreter fuel defaults to 100000; N is decimal in 0..1000000000.\nEach evaluated core expression consumes one unit before execution.\nUnselected branches consume no fuel. Callee bodies count normally.\nEvaluation nesting is limited to 256; source/IR depth is limited to 128.\nSee spec/core-format.md and docs/native-compilation.md for details.\n\nExit codes: 0 success, 1 source/IR error, 2 arithmetic trap,\n3 resource limit, 4 invocation or infrastructure error.\nVerify additionally uses 5 failed, 6 unknown, and 7 unsupported or empty.\n";

enum CliError {
    Message(String),
    StderrUnavailable,
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

fn main() -> ExitCode {
    match run(env::args_os().skip(1).collect()) {
        Ok(code) => ExitCode::from(code),
        Err(CliError::Message(message)) => {
            let _ = diagnostic(format_args!("apl: {message}"));
            ExitCode::from(4)
        }
        Err(CliError::StderrUnavailable) => ExitCode::from(4),
    }
}
fn output(text: impl std::fmt::Display) -> Result<(), CliError> {
    writeln!(io::stdout().lock(), "{text}")
        .map_err(|error| CliError::Message(format!("cannot write stdout: {error}")))
}
fn diagnostic(text: impl std::fmt::Display) -> Result<(), CliError> {
    writeln!(io::stderr().lock(), "{text}").map_err(|_| CliError::StderrUnavailable)
}
fn run(args: Vec<OsString>) -> Result<u8, CliError> {
    if args.len() == 1 && args[0] == "--version" {
        output(concat!("apl ", env!("CARGO_PKG_VERSION")))?;
        return Ok(0);
    }
    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        output(HELP.trim_end())?;
        return Ok(0);
    }
    if args.first().is_some_and(|arg| arg == "verify") {
        return verify_command(&args[1..]);
    }
    let usage = "invalid invocation; use apl --help";
    let command = args.first().and_then(|arg| arg.to_str()).ok_or(usage)?;
    if !matches!(
        command,
        "check" | "eval" | "dump-core" | "eval-core" | "build" | "run" | "emit-c"
    ) || args.len() < 2
    {
        return Err(usage.into());
    }
    let fuel = match args.len() {
        2 => DEFAULT_FUEL,
        4 if command == "build" && args[2] == "-o" => DEFAULT_FUEL,
        4 if matches!(command, "eval" | "eval-core") && args[2] == "--fuel" => {
            let text = args[3]
                .to_str()
                .ok_or("fuel must be decimal in 0..1000000000")?;
            if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
                return Err("fuel must be decimal in 0..1000000000".into());
            }
            text.parse::<u64>()
                .ok()
                .filter(|fuel| *fuel <= MAX_FUEL)
                .ok_or("fuel must be decimal in 0..1000000000")?
        }
        _ => return Err(usage.into()),
    };
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
        let result = eval::evaluate(&artifact.program, artifact.entry, fuel);
        output(core::outcome(&result))?;
        return report_execution(result, &filename, &source, None);
    }
    let program = match apl::compile_file(path) {
        Ok(program) => program,
        Err(error) => {
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
        output(core::export(&program, entry))?;
        return Ok(0);
    }
    if command == "emit-c" {
        output(codegen::emit_c(&program, entry)?)?;
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
        let destination = if args.len() == 4 {
            Path::new(&args[3])
        } else {
            &default
        };
        codegen::build(&program, entry, path, destination)?;
        return Ok(0);
    }
    if command == "run" {
        return codegen::run(&program, entry, path).map_err(CliError::from);
    }
    let result = eval::evaluate(&program, entry, fuel);
    if let Ok(value) = &result {
        output(value)?;
    }
    report_execution(result, &filename, &source, Some(&program))
}
fn report_execution(
    result: Result<eval::Value, EvalError>,
    filename: &str,
    source: &str,
    program: Option<&apl::types::Program>,
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
        Err(EvalError::InvalidIr) => {
            diagnostic(format_args!(
                "{filename}: invalid_ir: evaluator invariant failed"
            ))?;
            1
        }
    })
}

fn verify_command(args: &[OsString]) -> Result<u8, CliError> {
    let usage = "usage: apl verify FILE [--solver PATH] [--timeout-ms N] [--json]";
    let path = args.first().ok_or(usage)?;
    let mut options = apl::verify::VerifyOptions::default();
    let mut json = false;
    let mut solver_seen = false;
    let mut timeout_seen = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].to_str() {
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
    let report = match apl::verify::verify_file(Path::new(path), &options) {
        Ok(report) => report,
        Err(error) => {
            diagnostic(error.render(&path.to_string_lossy(), ""))?;
            apl::verify::VerificationReport::source_error(&error)
        }
    };
    if json {
        output(report.json())?;
    } else {
        output(report.human())?;
    }
    Ok(report.exit_code())
}
