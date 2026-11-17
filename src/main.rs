use apl::{
    DEFAULT_FUEL, MAX_FUEL, MAX_SOURCE_BYTES,
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

const HELP: &str = "APL 0.1 scalar-core checker and reference evaluator\n\nUsage:\n  apl check FILE\n  apl eval FILE [--fuel N]\n  apl dump-core FILE\n  apl eval-core FILE [--fuel N]\n  apl --version\n\nFuel defaults to 100000; N is decimal in 0..1000000000.\nEach evaluated core expression consumes one unit before execution.\nUnselected branches consume no fuel. Callee bodies count normally.\nEvaluation nesting is limited to 256; source/IR depth is limited to 128.\nSee spec/core-format.md for the full interchange and resource protocol.\n\nExit codes: 0 success, 1 source/IR error, 2 arithmetic trap,\n3 resource limit, 4 invocation or infrastructure error.\n";

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
    let usage = "invalid invocation; use apl --help";
    let command = args.first().and_then(|arg| arg.to_str()).ok_or(usage)?;
    if !matches!(command, "check" | "eval" | "dump-core" | "eval-core") || args.len() < 2 {
        return Err(usage.into());
    }
    let fuel = match args.len() {
        2 => DEFAULT_FUEL,
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
    let file = File::open(path).map_err(|error| format!("cannot read {filename}: {error}"))?;
    let mut bytes = Vec::new();
    file.take(MAX_SOURCE_BYTES as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {filename}: {error}"))?;
    if bytes.len() > MAX_SOURCE_BYTES {
        if command == "eval-core" {
            output("{\"outcome\":\"resource_limit\"}")?;
        }
        diagnostic(format_args!(
            "{filename}:1:1: resource_limit: input exceeds 1048576 bytes"
        ))?;
        return Ok(3);
    }
    let source = match String::from_utf8(bytes) {
        Ok(text) => text,
        Err(error) => {
            if command == "eval-core" {
                output("{\"outcome\":\"invalid_ir\"}")?;
            }
            let offset = error.utf8_error().valid_up_to();
            let valid = std::str::from_utf8(&error.as_bytes()[..offset]).unwrap_or("");
            diagnostic(
                Diagnostic::new(
                    Span {
                        start: offset,
                        end: offset,
                    },
                    "input is not valid UTF-8",
                )
                .render(&filename, valid),
            )?;
            return Ok(1);
        }
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
        return report_execution(result, &filename, &source);
    }
    let program = match apl::compile(&source) {
        Ok(program) => program,
        Err(error) => {
            diagnostic(error.render(&filename, &source))?;
            return Ok(if error.resource_limit { 3 } else { 1 });
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
    let result = eval::evaluate(&program, entry, fuel);
    if let Ok(value) = &result {
        output(value)?;
    }
    report_execution(result, &filename, &source)
}
fn report_execution(
    result: Result<eval::Value, EvalError>,
    filename: &str,
    source: &str,
) -> Result<u8, CliError> {
    Ok(match result {
        Ok(_) => 0,
        Err(EvalError::Trap { kind, span }) => {
            diagnostic(Diagnostic::new(span, kind.as_str()).render(filename, source))?;
            2
        }
        Err(EvalError::ResourceLimit { reason, span }) => {
            diagnostic(Diagnostic::resource(span, reason).render(filename, source))?;
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
