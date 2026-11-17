//! Validated scalar MIR to portable C11 and a host-native executable.
use crate::{
    mir::{self, Block, Operation},
    types::{BinaryOp, Program, Type, UnaryOp},
};
use std::{
    env,
    ffi::OsString,
    fs, io,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

/// Lower and validate a checked program, then emit a complete C11 translation unit.
/// `entry` must name a nullary function returning `i64`.
pub fn emit_c(program: &Program, entry: usize) -> Result<String, String> {
    let program = mir::lower(program, entry).map_err(|error| error.to_string())?;
    let mut text = String::from(RUNTIME);
    for (id, function) in program.functions.iter().enumerate() {
        text.push_str(&signature(id, function));
        text.push_str(";\n");
    }
    for (id, function) in program.functions.iter().enumerate() {
        text.push_str(&signature(id, function));
        text.push_str(" {\n");
        emit_block(&function.body, &mut text, 1);
        text.push_str(&format!(
            "    return t{};\n}}\n",
            function.body.yield_value.id
        ));
    }
    text.push_str(&format!(
        r#"
int main(void) {{
#ifdef SIGPIPE
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) return 4;
#endif
    int64_t result = apl_f{}();
    if (printf("%" PRId64 "\n", result) < 0 || fflush(stdout) == EOF) {{
        (void)fputs("apl: cannot write stdout\n", stderr);
        return 4;
    }}
    return 0;
}}
"#,
        program.entry
    ));
    Ok(text)
}

fn c_type(ty: Type) -> &'static str {
    match ty {
        Type::I64 => "int64_t",
        Type::Bool => "bool",
        Type::Unit => "unsigned char",
    }
}
fn signature(id: usize, function: &mir::Function) -> String {
    let params = if function.params.is_empty() {
        "void".into()
    } else {
        function
            .params
            .iter()
            .map(|p| format!("{} t{}", c_type(p.ty), p.id))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!("static {} apl_f{id}({params})", c_type(function.result))
}
fn emit_block(block: &Block, text: &mut String, indent: usize) {
    let padding = "    ".repeat(indent);
    for instruction in &block.instructions {
        let target = instruction.destination;
        if let Operation::Branch {
            condition,
            then_block,
            else_block,
        } = &instruction.kind
        {
            text.push_str(&format!(
                "{padding}{} t{};\n{padding}if (t{}) {{\n",
                c_type(target.ty),
                target.id,
                condition.id
            ));
            emit_block(then_block, text, indent + 1);
            text.push_str(&format!(
                "{padding}    t{} = t{};\n{padding}}} else {{\n",
                target.id, then_block.yield_value.id
            ));
            emit_block(else_block, text, indent + 1);
            text.push_str(&format!(
                "{padding}    t{} = t{};\n{padding}}}\n",
                target.id, else_block.yield_value.id
            ));
            continue;
        }
        let value = match &instruction.kind {
            Operation::Integer(n) if *n == i64::MIN => "INT64_MIN".into(),
            Operation::Integer(n) if *n < 0 => format!("(-INT64_C({}))", -n),
            Operation::Integer(n) => format!("INT64_C({n})"),
            Operation::Boolean(b) => b.to_string(),
            Operation::Unit => "0".into(),
            Operation::Unary(UnaryOp::Neg, input) => format!("apl_neg(t{})", input.id),
            Operation::Unary(UnaryOp::Not, input) => format!("!t{}", input.id),
            Operation::Binary(op, left, right) => {
                let symbol = match op {
                    BinaryOp::Lt => Some("<"),
                    BinaryOp::Le => Some("<="),
                    BinaryOp::Gt => Some(">"),
                    BinaryOp::Ge => Some(">="),
                    BinaryOp::Eq => Some("=="),
                    BinaryOp::Ne => Some("!="),
                    _ => None,
                };
                if let Some(symbol) = symbol {
                    format!("t{} {symbol} t{}", left.id, right.id)
                } else {
                    format!("apl_{}(t{}, t{})", op.as_str(), left.id, right.id)
                }
            }
            Operation::Call(id, args) => format!(
                "apl_f{id}({})",
                args.iter()
                    .map(|arg| format!("t{}", arg.id))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Operation::Branch { .. } => unreachable!("branch emitted above"),
        };
        text.push_str(&format!(
            "{padding}{} t{} = {value};\n",
            c_type(target.ty),
            target.id
        ));
    }
}

/// Compile with the host C toolchain and publish only a successfully linked binary.
/// `CC`, when present, is one executable path, never a shell command or flag list.
pub fn build(program: &Program, entry: usize, source: &Path, output: &Path) -> Result<(), String> {
    protect_sources(program, source, output)?;
    let c = emit_c(program, entry)?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let parent = parent.canonicalize().map_err(|error| {
        format!(
            "cannot access output directory {}: {error}",
            parent.display()
        )
    })?;
    let filename = output.file_name().ok_or("output must name a file")?;
    let destination = parent.join(filename);
    let staging = TempDir::new(&parent)?;
    let c_path = staging.0.join("program.c");
    let binary = staging.0.join("program");
    fs::write(&c_path, c).map_err(|error| format!("cannot write generated C: {error}"))?;
    let cc = env::var_os("CC").unwrap_or_else(|| OsString::from("cc"));
    let result = Command::new(&cc)
        .args(["-std=c11", "-O2", "-x", "c"])
        .arg(&c_path).arg("-o").arg(&binary).output()
        .map_err(|error| format!("cannot execute C compiler {}: {error}; install a C11 toolchain or set CC to its executable path", Path::new(&cc).display()))?;
    if !result.status.success() {
        return Err(format!(
            "C compiler {} failed ({}):\n{}{}",
            Path::new(&cc).display(),
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    if !binary.is_file() {
        return Err("C compiler reported success without producing an executable".into());
    }
    // Recheck after the external compiler completes before replacing an output.
    protect_sources(program, source, &destination)?;
    fs::rename(&binary, &destination).map_err(|error| {
        format!(
            "cannot publish executable {}: {error}",
            destination.display()
        )
    })?;
    Ok(())
}

/// Build in an isolated temporary directory, run with inherited I/O, and clean up.
pub fn run(program: &Program, entry: usize, source: &Path) -> Result<u8, String> {
    let directory = TempDir::new(&env::temp_dir())?;
    let binary = directory.0.join("program");
    build(program, entry, source, &binary)?;
    let status = Command::new(&binary)
        .status()
        .map_err(|error| format!("cannot run native executable: {error}"))?;
    status.code().and_then(|code| u8::try_from(code).ok())
        .ok_or_else(|| format!("native executable terminated by the host ({status}); native execution has no interpreter fuel or stack limit"))
}

fn protect_sources(program: &Program, source: &Path, output: &Path) -> Result<(), String> {
    protect_source(source, output)?;
    for input in program.sources.iter() {
        protect_source(&input.path, output)?;
        #[cfg(unix)]
        if let Ok(metadata) = fs::metadata(output) {
            use std::os::unix::fs::MetadataExt;
            if input.identity == (metadata.dev(), metadata.ino()) {
                return Err("output would overwrite the source input".into());
            }
        }
    }
    Ok(())
}

fn protect_source(source: &Path, output: &Path) -> Result<(), String> {
    let canonical_source = source
        .canonicalize()
        .map_err(|error| format!("cannot resolve source {}: {error}", source.display()))?;
    let output_metadata = match fs::metadata(output) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => {
            return Err(format!(
                "cannot inspect output {}: {error}",
                output.display()
            ));
        }
    };
    if !output_metadata.is_file() {
        return Err(format!("output {} is not a regular file", output.display()));
    }
    let canonical_output = output
        .canonicalize()
        .map_err(|error| format!("cannot resolve output {}: {error}", output.display()))?;
    let mut same = canonical_source == canonical_output;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let source_metadata = fs::metadata(&canonical_source)
            .map_err(|error| format!("cannot inspect source: {error}"))?;
        same |= source_metadata.dev() == output_metadata.dev()
            && source_metadata.ino() == output_metadata.ino();
    }
    if same {
        return Err("output would overwrite the source input".into());
    }
    Ok(())
}

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
struct TempDir(PathBuf);
impl TempDir {
    fn new(parent: &Path) -> Result<Self, String> {
        for _ in 0..256 {
            let id = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let path = parent.join(format!(".apl-native-{}-{id}", std::process::id()));
            let mut builder = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(format!(
                        "cannot create native build directory {}: {error}",
                        parent.display()
                    ));
                }
            }
        }
        Err("cannot allocate a unique native build directory".into())
    }
}
impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const RUNTIME: &str = r#"/* Generated by APL. Scalar internal ABI; not a stable foreign interface. */
#include <stdbool.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

static _Noreturn void apl_trap(const char *tag) {
    if (fputs(tag, stderr) == EOF || fputc('\n', stderr) == EOF || fflush(stderr) == EOF) exit(4);
    exit(2);
}
static int64_t apl_add(int64_t a, int64_t b) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) apl_trap("arithmetic_overflow");
    return a + b;
}
static int64_t apl_sub(int64_t a, int64_t b) {
    if ((b > 0 && a < INT64_MIN + b) || (b < 0 && a > INT64_MAX + b)) apl_trap("arithmetic_overflow");
    return a - b;
}
static int64_t apl_mul(int64_t a, int64_t b) {
    if (a > 0) {
        if ((b > 0 && a > INT64_MAX / b) || (b < 0 && b < INT64_MIN / a)) apl_trap("arithmetic_overflow");
    } else if (a < 0) {
        if ((b > 0 && a < INT64_MIN / b) || (b < 0 && a < INT64_MAX / b)) apl_trap("arithmetic_overflow");
    }
    return a * b;
}
static int64_t apl_neg(int64_t a) {
    if (a == INT64_MIN) apl_trap("arithmetic_overflow");
    return -a;
}
static int64_t apl_div(int64_t a, int64_t b) {
    if (b == 0) apl_trap("division_by_zero");
    if (a == INT64_MIN && b == -1) apl_trap("arithmetic_overflow");
    return a / b;
}
static int64_t apl_rem(int64_t a, int64_t b) {
    if (b == 0) apl_trap("division_by_zero");
    if (a == INT64_MIN && b == -1) apl_trap("arithmetic_overflow");
    return a % b;
}
"#;
