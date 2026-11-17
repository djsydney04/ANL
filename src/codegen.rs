//! Validated MIR to portable C11 and a host-native executable.
use crate::{
    bounded::{Buffer, OutputError},
    mir::{self, Block, Operation},
    types::{BinaryOp, Program, TupleShape, Type, UnaryOp},
};
use std::{
    borrow::Cow,
    collections::BTreeSet,
    env,
    ffi::OsString,
    fmt::{self, Write},
    fs, io,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

pub const MAX_PRODUCT_C_BYTES: usize = 67_108_864;
/// Lower and validate a checked program, then emit a complete C11 translation unit.
/// Product output is bounded before publication or invocation of the host compiler.
pub fn emit_c(program: &Program, entry: usize) -> Result<String, OutputError> {
    emit_c_with_limit(program, entry, MAX_PRODUCT_C_BYTES)
}
fn emit_c_with_limit(source: &Program, entry: usize, limit: usize) -> Result<String, OutputError> {
    let products = source.has_flat_products();
    let program = mir::lower(source, entry).map_err(|error| error.to_string())?;
    let mut text = Buffer::new(
        products.then_some(limit),
        "emitted v2 C exceeds 67108864 bytes",
    );
    // Each typed expression lowers once, without callee expansion. Tuple width bounds
    // each added construction/projection/comparison to at most eight field operations.
    let result = emit_translation_unit(&program, &mut text);
    if result.is_err() && !text.exhausted() {
        return Err(OutputError::Infrastructure("C formatting failed".into()));
    }
    text.finish()
}
fn emit_translation_unit(program: &mir::Program, text: &mut Buffer) -> fmt::Result {
    text.write_str(RUNTIME)?;
    let mut shapes = BTreeSet::new();
    fn add(ty: Type, shapes: &mut BTreeSet<TupleShape>) {
        if let Type::Tuple(shape) = ty {
            shapes.insert(shape);
        }
    }
    fn scan(block: &Block, shapes: &mut BTreeSet<TupleShape>) {
        for instruction in &block.instructions {
            add(instruction.destination.ty, shapes);
            match &instruction.kind {
                Operation::Branch {
                    then_block,
                    else_block,
                    ..
                } => {
                    scan(then_block, shapes);
                    scan(else_block, shapes);
                }
                Operation::MutableScope { slot, body, .. } => {
                    add(slot.ty, shapes);
                    scan(body, shapes);
                }
                Operation::While { condition, body } => {
                    scan(condition, shapes);
                    scan(body, shapes);
                }
                _ => {}
            }
        }
    }
    for function in &program.functions {
        add(function.result, &mut shapes);
        for param in &function.params {
            add(param.ty, &mut shapes);
        }
        scan(&function.body, &mut shapes);
    }
    for shape in shapes {
        text.write_str("typedef struct {")?;
        for (i, field) in shape.fields().iter().enumerate() {
            write!(text, " {} f{i};", c_type(field.as_type()))?;
        }
        writeln!(text, " }} {};", c_type(Type::Tuple(shape)))?;
    }
    for (id, function) in program.functions.iter().enumerate() {
        signature(id, function, text)?;
        text.write_str(";\n")?;
    }
    for (id, function) in program.functions.iter().enumerate() {
        signature(id, function, text)?;
        text.write_str(" {\n")?;
        emit_block(&function.body, text, 1)?;
        writeln!(text, "    return t{};\n}}", function.body.yield_value.id)?;
    }
    write!(
        text,
        r#"
int main(void) {{
#ifdef SIGPIPE
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) return 4;
#endif
    int64_t result = apl_f{}();
    if (printf("%" PRId64 "\n", result) < 0 || fflush(stdout) == EOF) {{
        (void)fputs("anl: cannot write stdout\n", stderr);
        return 4;
    }}
    return 0;
}}
"#,
        program.entry
    )
}
fn c_type(ty: Type) -> Cow<'static, str> {
    match ty {
        Type::I64 => "int64_t".into(),
        Type::Bool => "bool".into(),
        Type::Unit => "unsigned char".into(),
        Type::Tuple(shape) => {
            let mut name = String::from("apl_tuple_");
            for field in shape.fields() {
                name.push(match field {
                    crate::types::ScalarType::I64 => 'i',
                    crate::types::ScalarType::Bool => 'b',
                    crate::types::ScalarType::Unit => 'u',
                });
            }
            name.into()
        }
    }
}
fn signature(id: usize, function: &mir::Function, text: &mut Buffer) -> fmt::Result {
    write!(text, "static {} apl_f{id}(", c_type(function.result))?;
    if function.params.is_empty() {
        text.write_str("void")?;
    }
    for (i, param) in function.params.iter().enumerate() {
        if i > 0 {
            text.write_str(", ")?;
        }
        write!(text, "{} t{}", c_type(param.ty), param.id)?;
    }
    text.write_str(")")
}
fn emit_block(block: &Block, text: &mut Buffer, indent: usize) -> fmt::Result {
    let padding = "    ".repeat(indent);
    for instruction in &block.instructions {
        let target = instruction.destination;
        match &instruction.kind {
            Operation::Branch {
                condition,
                then_block,
                else_block,
            } => {
                write!(
                    text,
                    "{padding}{} t{};\n{padding}if (t{}) {{\n",
                    c_type(target.ty),
                    target.id,
                    condition.id
                )?;
                emit_block(then_block, text, indent + 1)?;
                write!(
                    text,
                    "{padding}    t{} = t{};\n{padding}}} else {{\n",
                    target.id, then_block.yield_value.id
                )?;
                emit_block(else_block, text, indent + 1)?;
                write!(
                    text,
                    "{padding}    t{} = t{};\n{padding}}}\n",
                    target.id, else_block.yield_value.id
                )?;
                continue;
            }
            Operation::MutableScope {
                slot,
                initial,
                body,
            } => {
                write!(
                    text,
                    "{padding}{} t{};\n{padding}{{\n{padding}    {} s{} = t{};\n",
                    c_type(target.ty),
                    target.id,
                    c_type(slot.ty),
                    slot.id,
                    initial.id
                )?;
                emit_block(body, text, indent + 1)?;
                write!(
                    text,
                    "{padding}    t{} = t{};\n{padding}}}\n",
                    target.id, body.yield_value.id
                )?;
                continue;
            }
            Operation::While { condition, body } => {
                writeln!(text, "{padding}for (;;) {{")?;
                emit_block(condition, text, indent + 1)?;
                write!(
                    text,
                    "{padding}    if (!t{}) break;\n{padding}    {{\n",
                    condition.yield_value.id
                )?;
                emit_block(body, text, indent + 2)?;
                write!(text, "{padding}    }}\n{padding}}}\n")?;
            }
            Operation::Store(slot, value) => {
                writeln!(text, "{padding}s{} = t{};", slot.id, value.id)?;
            }
            _ => {}
        }
        write!(text, "{padding}{} t{} = ", c_type(target.ty), target.id)?;
        match &instruction.kind {
            Operation::Tuple(fields) => {
                text.write_str("{")?;
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        text.write_str(", ")?;
                    }
                    write!(text, ".f{i} = t{}", field.id)?;
                }
                text.write_str("}")?;
            }
            Operation::Project(value, index) => {
                write!(text, "t{}.f{index}", value.id)?;
            }
            Operation::Integer(n) if *n == i64::MIN => text.write_str("INT64_MIN")?,
            Operation::Integer(n) if *n < 0 => write!(text, "(-INT64_C({}))", -n)?,
            Operation::Integer(n) => write!(text, "INT64_C({n})")?,
            Operation::Boolean(b) => write!(text, "{b}")?,
            Operation::Unit => text.write_str("0")?,
            Operation::Unary(UnaryOp::Neg, input) => write!(text, "apl_neg(t{})", input.id)?,
            Operation::Unary(UnaryOp::Not, input) => write!(text, "!t{}", input.id)?,
            Operation::Binary(op, left, right) => {
                if let Type::Tuple(shape) = left.ty {
                    if *op == BinaryOp::Ne {
                        text.write_str("!")?;
                    }
                    text.write_str("(")?;
                    for i in 0..shape.fields().len() {
                        if i > 0 {
                            text.write_str(" && ")?;
                        }
                        write!(text, "t{}.f{i} == t{}.f{i}", left.id, right.id)?;
                    }
                    text.write_str(")")?;
                } else {
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
                        write!(text, "t{} {symbol} t{}", left.id, right.id)?;
                    } else {
                        write!(text, "apl_{}(t{}, t{})", op.as_str(), left.id, right.id)?;
                    }
                }
            }
            Operation::Call(id, args) => {
                write!(text, "apl_f{id}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        text.write_str(", ")?;
                    }
                    write!(text, "t{}", arg.id)?;
                }
                text.write_str(")")?;
            }
            Operation::Load(slot) => write!(text, "s{}", slot.id)?,
            Operation::Store(..) | Operation::While { .. } => text.write_str("0")?,
            Operation::Branch { .. } | Operation::MutableScope { .. } => {
                unreachable!("structured result emitted above")
            }
        }
        text.write_str(";\n")?;
    }
    Ok(())
}

/// Compile with the host C toolchain and publish only a successfully linked binary.
/// `CC`, when present, is one executable path, never a shell command or flag list.
pub fn build(
    program: &Program,
    entry: usize,
    source: &Path,
    output: &Path,
) -> Result<(), OutputError> {
    build_with_limit(program, entry, source, output, MAX_PRODUCT_C_BYTES)
}
fn build_with_limit(
    program: &Program,
    entry: usize,
    source: &Path,
    output: &Path,
    limit: usize,
) -> Result<(), OutputError> {
    protect_sources(program, source, output)?;
    let c = emit_c_with_limit(program, entry, limit)?;
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
        )
        .into());
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
pub fn run(program: &Program, entry: usize, source: &Path) -> Result<u8, OutputError> {
    let directory = TempDir::new(&env::temp_dir())?;
    let binary = directory.0.join("program");
    build(program, entry, source, &binary)?;
    let status = Command::new(&binary)
        .status()
        .map_err(|error| format!("cannot run native executable: {error}"))?;
    status.code().and_then(|code| u8::try_from(code).ok())
        .ok_or_else(|| format!("native executable terminated by the host ({status}); native execution has no interpreter fuel or stack limit").into())
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

const RUNTIME: &str = r#"/* Generated by ANL. Scalar internal ABI; not a stable foreign interface. */
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

#[cfg(test)]
mod product_output_tests {
    use super::*;
    #[test]
    fn resource_failure_preserves_destination_before_native_staging() {
        let directory = TempDir::new(&std::env::temp_dir()).unwrap();
        let source = directory.0.join("input.apl");
        let output = directory.0.join("existing");
        fs::write(&source, "fn main()->i64{(42,).0}").unwrap();
        fs::write(&output, b"retain existing destination").unwrap();
        let program = crate::compile_file(&source).unwrap();
        let error =
            build_with_limit(&program, program.entry().unwrap(), &source, &output, 1).unwrap_err();
        assert!(matches!(error, OutputError::ResourceLimit(_)));
        assert_eq!(fs::read(&output).unwrap(), b"retain existing destination");
        assert_eq!(fs::read_dir(&directory.0).unwrap().count(), 2);
    }
    #[test]
    fn exact_complete_translation_unit_bounds_precede_publication() {
        let program =
            crate::compile("fn tuple()->(i64,bool,unit){(42,true,())} fn main()->i64{tuple().0}")
                .unwrap();
        let expected = emit_c(&program, program.entry().unwrap()).unwrap();
        for limit in [expected.len() - 1, expected.len(), expected.len() + 1] {
            let emitted = emit_c_with_limit(&program, program.entry().unwrap(), limit);
            if limit < expected.len() {
                assert!(matches!(emitted, Err(OutputError::ResourceLimit(_))));
            } else {
                assert_eq!(emitted.unwrap(), expected);
            }
        }
    }
}
