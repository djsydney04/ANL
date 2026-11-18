//! Validated MIR to portable C11 and a host-native executable.
mod helpers;
use crate::{
    bounded::{Buffer, OutputError},
    mir::{self, Block, MemoryOperation, Operation},
    types::{BinaryOp, IrRevision, Program, TupleShape, Type, UnaryOp},
    word::{ConvertMode, WordWidth},
};
use helpers::Helper;
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
    let products = source.has_flat_products()
        || source.has_memory()
        || source.effective_revision() == IrRevision::WordsV4;
    let program = mir::lower(source, entry).map_err(|error| error.to_string())?;
    emit_lowered(&program, products.then_some(limit))
}
pub(crate) fn emit_lowered(
    program: &mir::Program,
    limit: Option<usize>,
) -> Result<String, OutputError> {
    let mut text = Buffer::new(limit, "emitted v2 C exceeds 67108864 bytes");
    // Each typed expression lowers once, without callee expansion. Tuple width bounds
    // each added construction/projection/comparison to at most eight field operations.
    let result = emit_translation_unit(program, &mut text);
    if result.is_err() && !text.exhausted() {
        return Err(OutputError::Infrastructure("C formatting failed".into()));
    }
    text.finish()
}
fn emit_translation_unit(program: &mir::Program, text: &mut Buffer) -> fmt::Result {
    let memory = program.has_memory();
    if memory {
        text.write_str("#include \"runtime.h\"\n")?;
    }
    if memory {
        text.write_str(&RUNTIME_HEADER.replace(
            "static _Noreturn void apl_trap(const char *tag) {\n",
            "static _Noreturn void apl_trap(const char *tag) {\n    anl_memory_trap(tag);\n",
        ))?;
    } else {
        text.write_str(RUNTIME_HEADER)?;
    }
    for helper in helpers::SIGNED {
        helper.emit(false, text)?;
    }
    if program.revision == IrRevision::WordsV4 {
        emit_word_profile(
            program.allocation_profile.expect("checked word profile"),
            text,
        )?;
        text.write_str("\n")?;
        for helper in helpers::WORD {
            helper.emit(false, text)?;
        }
    }
    emit_shapes(&program.functions, text)?;
    for (id, function) in program.functions.iter().enumerate() {
        signature(id, function, text)?;
        text.write_str(";\n")?;
    }
    for (id, function) in program.functions.iter().enumerate() {
        signature(id, function, text)?;
        text.write_str(" {\n")?;
        emit_block(
            &function.body,
            text,
            1,
            id,
            program.allocation_profile,
            &mut BodyEmission::hosted(),
        )?;
        writeln!(text, "    return t{};\n}}", function.body.yield_value.id)?;
    }
    let begin = if memory {
        "    anl_memory_begin();\n"
    } else {
        ""
    };
    let finish = if memory {
        "    anl_memory_value(result);\n"
    } else {
        ""
    };
    write!(
        text,
        r#"
int main(void) {{
#ifdef SIGPIPE
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) return 4;
#endif
{begin}    int64_t result = apl_f{}();
{finish}    if (printf("%" PRId64 "\n", result) < 0 || fflush(stdout) == EOF) {{
        (void)fputs("anl: cannot write stdout\n", stderr);
        return 4;
    }}
    return 0;
}}
"#,
        program.entry
    )
}
pub(crate) fn emit_shapes(functions: &[mir::Function], text: &mut Buffer) -> fmt::Result {
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
                Operation::Memory(memory) => match memory.as_ref() {
                    MemoryOperation::HeapScope {
                        initial,
                        success,
                        failure,
                        ..
                    } => {
                        scan(initial, shapes);
                        scan(success, shapes);
                        scan(failure, shapes);
                    }
                    MemoryOperation::Write { value, .. } => scan(value, shapes),
                    _ => {}
                },
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
    for function in functions {
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
    Ok(())
}
pub(crate) fn c_type(ty: Type) -> Cow<'static, str> {
    match ty {
        Type::I64 => "int64_t".into(),
        Type::Word(width) => format!("uint{}_t", width.bits()).into(),
        Type::Bool => "bool".into(),
        Type::Unit => "unsigned char".into(),
        Type::Tuple(shape) => {
            let mut name = String::from("apl_tuple_");
            for field in shape.fields() {
                name.push(match field {
                    crate::types::ScalarType::I64 => 'i',
                    crate::types::ScalarType::Bool => 'b',
                    crate::types::ScalarType::Unit => 'u',
                    crate::types::ScalarType::Word(WordWidth::U8) => 'c',
                    crate::types::ScalarType::Word(WordWidth::U16) => 's',
                    crate::types::ScalarType::Word(WordWidth::U32) => 'w',
                    crate::types::ScalarType::Word(WordWidth::U64) => 'q',
                });
            }
            name.into()
        }
    }
}
fn signature(id: usize, function: &mir::Function, text: &mut Buffer) -> fmt::Result {
    write!(text, "static {} apl_f{id}(", c_type(function.result))?;
    if function.params.is_empty() && function.view.is_none() {
        text.write_str("void")?;
    }
    if let Some((_, resource)) = function.view {
        write!(text, "anl_buffer r{resource}")?;
    }
    for (i, param) in function.params.iter().enumerate() {
        if i > 0 || function.view.is_some() {
            text.write_str(", ")?;
        }
        write!(text, "{} t{}", c_type(param.ty), param.id)?;
    }
    text.write_str(")")
}
pub(crate) fn emit_boot_helpers(functions: &[mir::Function], text: &mut Buffer) -> fmt::Result {
    fn scan(block: &Block, used: &mut BTreeSet<Helper>) -> fmt::Result {
        for instruction in &block.instructions {
            let helper = match &instruction.kind {
                Operation::Unary(UnaryOp::Neg, _) => Some(Helper::Neg),
                Operation::Unary(UnaryOp::BitNot, _) => Some(Helper::WordNot),
                Operation::Binary(op, left, _) => match (op, left.ty) {
                    (BinaryOp::Add, Type::I64) => Some(Helper::Add),
                    (BinaryOp::Sub, Type::I64) => Some(Helper::Sub),
                    (BinaryOp::Mul, Type::I64) => Some(Helper::Mul),
                    (BinaryOp::Div, Type::I64) => Some(Helper::Div),
                    (BinaryOp::Rem, Type::I64) => Some(Helper::Rem),
                    (BinaryOp::Add, Type::Word(_)) => Some(Helper::WordAdd),
                    (BinaryOp::Sub, Type::Word(_)) => Some(Helper::WordSub),
                    (BinaryOp::Mul, Type::Word(_)) => Some(Helper::WordMul),
                    (BinaryOp::Div, Type::Word(_)) => Some(Helper::WordDiv),
                    (BinaryOp::Rem, Type::Word(_)) => Some(Helper::WordRem),
                    (BinaryOp::WrapAdd, _) => Some(Helper::WordWrapAdd),
                    (BinaryOp::WrapSub, _) => Some(Helper::WordWrapSub),
                    (BinaryOp::WrapMul, _) => Some(Helper::WordWrapMul),
                    (BinaryOp::BitAnd, _) => Some(Helper::WordBitAnd),
                    (BinaryOp::BitXor, _) => Some(Helper::WordBitXor),
                    (BinaryOp::BitOr, _) => Some(Helper::WordBitOr),
                    (BinaryOp::Shl, _) => Some(Helper::WordShl),
                    (BinaryOp::Shr, _) => Some(Helper::WordShr),
                    _ => None,
                },
                Operation::Convert {
                    mode,
                    target,
                    operand,
                } => match (mode, target, operand.ty) {
                    (ConvertMode::Checked, Type::I64, Type::Word(_)) => Some(Helper::WordToI64),
                    (ConvertMode::Checked, Type::Word(_), Type::I64) => Some(Helper::WordCastI64),
                    (ConvertMode::Checked, Type::Word(_), Type::Word(_)) => {
                        Some(Helper::WordCastWord)
                    }
                    (ConvertMode::Truncate, Type::Word(_), Type::I64) => {
                        Some(Helper::WordTruncateI64)
                    }
                    (ConvertMode::Truncate, Type::Word(_), Type::Word(_)) => {
                        Some(Helper::WordTruncateWord)
                    }
                    _ => None,
                },
                Operation::MutableScope { body, .. } => {
                    scan(body, used)?;
                    None
                }
                Operation::Branch {
                    then_block,
                    else_block,
                    ..
                } => {
                    scan(then_block, used)?;
                    scan(else_block, used)?;
                    None
                }
                Operation::While { condition, body } => {
                    scan(condition, used)?;
                    scan(body, used)?;
                    None
                }
                Operation::Memory(_) => return Err(fmt::Error),
                _ => None,
            };
            if let Some(helper) = helper {
                used.insert(helper);
            }
        }
        Ok(())
    }
    let mut used = BTreeSet::new();
    for function in functions {
        scan(&function.body, &mut used)?;
    }
    for helper in used {
        helper.emit(true, text)?;
    }
    Ok(())
}
pub(crate) struct BodyEmission {
    pub(crate) boot: bool,
    pub(crate) ranges: Vec<(usize, std::ops::Range<usize>)>,
}
impl BodyEmission {
    fn hosted() -> Self {
        Self {
            boot: false,
            ranges: Vec::new(),
        }
    }
    pub(crate) fn boot() -> Self {
        Self {
            boot: true,
            ranges: Vec::new(),
        }
    }
}
pub(crate) fn emit_block(
    block: &Block,
    text: &mut Buffer,
    indent: usize,
    function: usize,
    profile: Option<crate::memory::AllocationProfile>,
    emission: &mut BodyEmission,
) -> fmt::Result {
    for instruction in &block.instructions {
        let target = instruction.destination;
        let row = emission.ranges.len();
        if emission.boot {
            emission.ranges.push((target.id, text.len()..text.len()));
        }
        emit_instruction(instruction, text, indent, function, profile, emission)?;
        if emission.boot {
            emission.ranges[row].1.end = text.len();
        }
    }
    Ok(())
}
fn emit_instruction(
    instruction: &mir::Instruction,
    text: &mut Buffer,
    indent: usize,
    function: usize,
    profile: Option<crate::memory::AllocationProfile>,
    emission: &mut BodyEmission,
) -> fmt::Result {
    let padding = "    ".repeat(indent);
    let target = instruction.destination;
    match &instruction.kind {
        Operation::Memory(memory) => {
            if emission.boot {
                return Err(fmt::Error);
            }
            emit_memory(
                memory,
                target,
                text,
                indent,
                function,
                profile.expect("checked memory profile"),
                emission,
            )?;
            return Ok(());
        }
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
            emit_block(then_block, text, indent + 1, function, profile, emission)?;
            write!(
                text,
                "{padding}    t{} = t{};\n{padding}}} else {{\n",
                target.id, then_block.yield_value.id
            )?;
            emit_block(else_block, text, indent + 1, function, profile, emission)?;
            write!(
                text,
                "{padding}    t{} = t{};\n{padding}}}\n",
                target.id, else_block.yield_value.id
            )?;
            return Ok(());
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
            emit_block(body, text, indent + 1, function, profile, emission)?;
            write!(
                text,
                "{padding}    t{} = t{};\n{padding}}}\n",
                target.id, body.yield_value.id
            )?;
            return Ok(());
        }
        Operation::While { condition, body } => {
            writeln!(text, "{padding}for (;;) {{")?;
            emit_block(condition, text, indent + 1, function, profile, emission)?;
            write!(
                text,
                "{padding}    if (!t{}) break;\n{padding}    {{\n",
                condition.yield_value.id
            )?;
            emit_block(body, text, indent + 2, function, profile, emission)?;
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
        Operation::Word(value) => write!(text, "UINT64_C({})", value.value())?,
        Operation::Convert {
            mode,
            target,
            operand,
        } => {
            emit_conversion(*mode, *target, *operand, text)?;
        }
        Operation::Boolean(b) => write!(text, "{b}")?,
        Operation::Unit => text.write_str("0")?,
        Operation::Unary(UnaryOp::Neg, input) => write!(text, "apl_neg(t{})", input.id)?,
        Operation::Unary(UnaryOp::Not, input) => write!(text, "!t{}", input.id)?,
        Operation::Unary(UnaryOp::BitNot, input) => {
            let Type::Word(width) = input.ty else {
                unreachable!("checked word complement")
            };
            write!(
                text,
                "apl_word_not((uint64_t)t{}, UINT64_C({}))",
                input.id,
                width.max()
            )?;
        }
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
                } else if let Type::Word(width) = left.ty {
                    if matches!(op, BinaryOp::Shl | BinaryOp::Shr) {
                        write!(
                            text,
                            "apl_word_{}((uint64_t)t{}, t{}, {}, UINT64_C({}))",
                            op.as_str(),
                            left.id,
                            right.id,
                            width.bits(),
                            width.max()
                        )?;
                    } else {
                        write!(
                            text,
                            "apl_word_{}((uint64_t)t{}, (uint64_t)t{}, UINT64_C({}))",
                            op.as_str(),
                            left.id,
                            right.id,
                            width.max()
                        )?;
                    }
                } else {
                    write!(text, "apl_{}(t{}, t{})", op.as_str(), left.id, right.id)?;
                }
            }
        }
        Operation::Call(id, args) => {
            write!(
                text,
                "{}{id}(",
                if emission.boot { "anl_boot_f" } else { "apl_f" }
            )?;
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
        Operation::Memory(_) | Operation::Branch { .. } | Operation::MutableScope { .. } => {
            unreachable!("structured result emitted above")
        }
    }
    text.write_str(";\n")?;
    Ok(())
}

fn emit_conversion(
    mode: ConvertMode,
    target: Type,
    operand: mir::Temp,
    text: &mut Buffer,
) -> fmt::Result {
    match (mode, target, operand.ty) {
        (ConvertMode::Checked, Type::I64, Type::I64) => write!(text, "t{}", operand.id),
        (ConvertMode::Checked, Type::I64, Type::Word(_)) => {
            write!(text, "apl_word_to_i64((uint64_t)t{})", operand.id)
        }
        (mode, Type::Word(width), source @ (Type::I64 | Type::Word(_))) => {
            let operation = match mode {
                ConvertMode::Checked => "cast",
                ConvertMode::Truncate => "truncate",
            };
            let (source_kind, carrier) = if source == Type::I64 {
                ("i64", "")
            } else {
                ("word", "(uint64_t)")
            };
            write!(
                text,
                "apl_word_{operation}_{source_kind}({carrier}t{}, UINT64_C({}))",
                operand.id,
                width.max()
            )
        }
        _ => unreachable!("checked integer conversion"),
    }
}

fn emit_word_profile(profile: crate::memory::AllocationProfile, text: &mut Buffer) -> fmt::Result {
    let size_max = ((1u128 << profile.size_bits) - 1) as u64;
    let ptrdiff_max = ((1u128 << (profile.ptrdiff_bits - 1)) - 1) as u64;
    write!(
        text,
        r#"
#include <stddef.h>
#include <limits.h>
_Static_assert(CHAR_BIT == 8 && sizeof(int64_t) == 8, "ANL byte profile mismatch");
_Static_assert(_Alignof(int64_t) == {align}, "ANL i64 alignment mismatch");
_Static_assert(SIZE_MAX == UINT64_C({size_max}), "ANL size profile mismatch");
_Static_assert(PTRDIFF_MAX == INT64_C({ptrdiff_max}), "ANL ptrdiff profile mismatch");
_Static_assert(sizeof(uint8_t) == 1 && UINT8_MAX == UINT64_C(255), "ANL u8 width mismatch");
_Static_assert(sizeof(uint16_t) == 2 && UINT16_MAX == UINT64_C(65535), "ANL u16 width mismatch");
_Static_assert(sizeof(uint32_t) == 4 && UINT32_MAX == UINT64_C(4294967295), "ANL u32 width mismatch");
_Static_assert(sizeof(uint64_t) == 8 && UINT64_MAX == UINT64_C(18446744073709551615), "ANL u64 width mismatch");
"#,
        align = profile.i64_align
    )
}

fn emit_memory(
    m: &MemoryOperation,
    target: mir::Temp,
    text: &mut Buffer,
    indent: usize,
    function: usize,
    profile: crate::memory::AllocationProfile,
    emission: &mut BodyEmission,
) -> fmt::Result {
    let p = "    ".repeat(indent);
    let t = target.id;
    match m {
        MemoryOperation::HeapScope {
            site,
            owner,
            length,
            initial,
            success,
            failure,
        } => {
            writeln!(
                text,
                "{p}{} t{t};\n{p}{{\n{p}    if (t{} < 0) apl_trap(\"invalid_length\");",
                c_type(target.ty),
                length.id
            )?;
            emit_block(initial, text, indent + 1, function, Some(profile), emission)?;
            writeln!(
                text,
                "{p}    anl_buffer r{owner} = {{NULL, t{}}};\n{p}    bool ok{t} = false;\n{p}    if ((uint64_t)t{} <= UINT64_C({})) {{",
                length.id,
                length.id,
                profile.max_cells()
            )?;
            writeln!(
                text,
                "{p}        if (r{owner}.length == 0) {{ anl_memory_empty_open(UINT64_C({function}), UINT64_C({site})); ok{t} = true; }} else {{"
            )?;
            writeln!(
                text,
                "{p}            r{owner}.data = anl_memory_request(r{owner}.length, UINT64_C({function}), UINT64_C({site}));\n{p}            ok{t} = r{owner}.data != NULL;\n{p}            if (ok{t}) for (int64_t i{t} = 0; i{t} < r{owner}.length; ++i{t}) r{owner}.data[(size_t)i{t}] = t{};\n{p}        }}\n{p}    }}\n{p}    if (ok{t}) {{",
                initial.yield_value.id
            )?;
            emit_block(success, text, indent + 2, function, Some(profile), emission)?;
            writeln!(
                text,
                "{p}        t{t} = t{};\n{p}        if (r{owner}.length == 0) anl_memory_empty_close(UINT64_C({function}), UINT64_C({site})); else anl_memory_release(r{owner}.data, UINT64_C({function}), UINT64_C({site}));\n{p}    }} else {{",
                success.yield_value.id
            )?;
            emit_block(failure, text, indent + 2, function, Some(profile), emission)?;
            writeln!(
                text,
                "{p}        t{t} = t{};\n{p}    }}\n{p}}}",
                failure.yield_value.id
            )
        }
        MemoryOperation::Length { resource } => {
            writeln!(text, "{p}int64_t t{t} = r{resource}.length;")
        }
        MemoryOperation::Read { resource, index } => {
            writeln!(
                text,
                "{p}if (t{} < 0 || t{} >= r{resource}.length) apl_trap(\"index_out_of_bounds\");\n{p}int64_t t{t} = r{resource}.data[(size_t)t{}];",
                index.id, index.id, index.id
            )
        }
        MemoryOperation::Write {
            resource,
            index,
            value,
        } => {
            writeln!(
                text,
                "{p}if (t{} < 0 || t{} >= r{resource}.length) apl_trap(\"index_out_of_bounds\");\n{p}{{",
                index.id, index.id
            )?;
            emit_block(value, text, indent + 1, function, Some(profile), emission)?;
            writeln!(
                text,
                "{p}    int64_t write{t} = t{};\n{p}    r{resource}.data[(size_t)t{}] = write{t};\n{p}}}\n{p}unsigned char t{t} = 0;",
                value.yield_value.id, index.id
            )
        }
        MemoryOperation::CallView {
            function,
            resource,
            arguments,
            ..
        } => {
            write!(
                text,
                "{p}{} t{t} = apl_f{function}(r{resource}",
                c_type(target.ty)
            )?;
            for a in arguments {
                write!(text, ", t{}", a.id)?;
            }
            writeln!(text, ");")
        }
    }
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
    build_with_options(
        program,
        entry,
        source,
        output,
        limit,
        &BuildOptions::default(),
    )
}
#[derive(Default)]
struct BuildOptions<'a> {
    #[cfg(feature = "memory-evidence")]
    evidence: Option<&'a crate::memory_evidence::EvidenceOptions>,
    marker: std::marker::PhantomData<&'a ()>,
}
impl BuildOptions<'_> {
    fn protect(&self, _path: &Path) -> Result<(), String> {
        #[cfg(feature = "memory-evidence")]
        if let Some(e) = self.evidence {
            e.protect_destination(_path)?;
        }
        Ok(())
    }
    fn active(&self) -> bool {
        #[cfg(feature = "memory-evidence")]
        {
            self.evidence.is_some()
        }
        #[cfg(not(feature = "memory-evidence"))]
        {
            false
        }
    }
}
#[cfg(feature = "memory-evidence")]
pub fn build_evidence(
    program: &Program,
    entry: usize,
    source: &Path,
    output: &Path,
    evidence: &crate::memory_evidence::EvidenceOptions,
) -> Result<(), OutputError> {
    evidence.check_program(program)?;
    build_with_options(
        program,
        entry,
        source,
        output,
        MAX_PRODUCT_C_BYTES,
        &BuildOptions {
            evidence: Some(evidence),
            marker: std::marker::PhantomData,
        },
    )
}
fn build_with_options(
    program: &Program,
    entry: usize,
    source: &Path,
    output: &Path,
    limit: usize,
    options: &BuildOptions<'_>,
) -> Result<(), OutputError> {
    protect_sources(program, source, output)?;
    options.protect(output)?;
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
    let result = if program.has_memory() {
        let profile = program.allocation_profile.expect("checked memory profile");
        let (header, runtime) = crate::memory::runtime_sources(profile);
        #[cfg(feature = "memory-evidence")]
        if let Some(e) = options.evidence {
            fs::write(staging.0.join("evidence.h"), e.native_config()?)
                .map_err(|error| error.to_string())?;
        }
        fs::write(staging.0.join("runtime.h"), header).map_err(|e| e.to_string())?;
        let runtime_path = staging.0.join("runtime.c");
        fs::write(&runtime_path, runtime).map_err(|e| e.to_string())?;
        let program_object = staging.0.join("program.o");
        let runtime_object = staging.0.join("runtime.o");
        for (input, object) in [(&c_path, &program_object), (&runtime_path, &runtime_object)] {
            let mut command = Command::new(&cc);
            command.args(["-std=c11", "-O2", "-fno-lto", "-x", "c", "-c"]);
            if options.active() {
                command.arg("-DANL_MEMORY_EVIDENCE=1");
            }
            let result = command
                .arg(input)
                .arg("-o")
                .arg(object)
                .output()
                .map_err(|e| format!("cannot execute C compiler: {e}"))?;
            if !result.status.success() || !object.is_file() {
                return Err(format!(
                    "C compilation failed ({}):\n{}{}",
                    result.status,
                    String::from_utf8_lossy(&result.stdout),
                    String::from_utf8_lossy(&result.stderr)
                )
                .into());
            }
        }
        Command::new(&cc)
            .arg("-fno-lto")
            .arg(&program_object)
            .arg(&runtime_object)
            .arg("-o")
            .arg(&binary)
            .output()
            .map_err(|e| format!("cannot link C objects: {e}"))?
    } else {
        Command::new(&cc)
        .args(["-std=c11", "-O2", "-x", "c"])
        .arg(&c_path).arg("-o").arg(&binary).output()
        .map_err(|error| format!("cannot execute C compiler {}: {error}; install a C11 toolchain or set CC to its executable path", Path::new(&cc).display()))?
    };
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
    options.protect(&destination)?;
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
    run_binary(&binary)
}
#[cfg(feature = "memory-evidence")]
pub fn run_evidence(
    program: &Program,
    entry: usize,
    source: &Path,
    evidence: &crate::memory_evidence::EvidenceOptions,
) -> Result<u8, OutputError> {
    let directory = TempDir::new(&env::temp_dir())?;
    let binary = directory.0.join("program");
    build_evidence(program, entry, source, &binary, evidence)?;
    run_binary(&binary)
}
fn run_binary(binary: &Path) -> Result<u8, OutputError> {
    let status = Command::new(binary)
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
pub(crate) struct TempDir(pub(crate) PathBuf);
impl TempDir {
    pub(crate) fn new(parent: &Path) -> Result<Self, String> {
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

const RUNTIME_HEADER: &str = r#"/* Generated by ANL. Scalar internal ABI; not a stable foreign interface. */
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
