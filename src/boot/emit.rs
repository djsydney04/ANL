mod setup;
use super::{BlockChild, CheckedPair, CoreEdge, Operation, Origin, Profile, templates};
use crate::{
    bounded::{Buffer, OutputError},
    codegen,
    diagnostic::Span,
    types::Type,
};
use serde_json::{Value, json};
pub use setup::{
    SetupAbi, SetupEmissionView, SetupFunction, SetupOperation, SetupPrimitive,
    SetupProfileUnsupported, SetupReturn, SetupRole,
};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fmt::{self, Write},
    ops::Range,
    path::Path,
};

const MAX_ASSEMBLY: usize = 1_048_576;
const MAX_LINKER: usize = 65_536;
const MAX_MANIFEST: usize = 1_048_576;

/// Complete checked compiler artifacts. This contains no linked image or runtime result.
pub struct Bundle {
    pub(super) files: [(&'static str, String); 6],
    setup: Result<setup::SetupIdentity, SetupProfileUnsupported>,
}
impl Bundle {
    /// Read-only setup identity from the same checked emission; never native admission.
    pub fn setup_identity(&self) -> Result<SetupEmissionView<'_>, SetupProfileUnsupported> {
        match &self.setup {
            Ok(identity) => Ok(setup::view(&self.files, identity)),
            Err(reason) => Err(*reason),
        }
    }
    pub fn files(&self) -> impl Iterator<Item = (&'static str, &str)> {
        self.files
            .iter()
            .map(|(name, bytes)| (*name, bytes.as_str()))
    }
    /// Publish the complete directory without replacing any destination entry.
    pub fn publish(&self, destination: impl AsRef<Path>) -> Result<(), OutputError> {
        super::publish::publish(self, destination.as_ref())
    }
}
fn invariant(message: &str) -> OutputError {
    OutputError::Infrastructure(message.into())
}
fn rendered(text: Buffer, result: fmt::Result) -> Result<String, OutputError> {
    if result.is_err() && !text.exhausted() {
        return Err(invariant("boot artifact formatting failed"));
    }
    if result.is_ok() && text.len() == 0 {
        return Err(invariant("empty boot artifact"));
    }
    text.finish()
}
fn identity(path: &str, text: &str) -> Value {
    json!({"path":path,"bytes":text.len(),"sha256":format!("{:x}",Sha256::digest(text.as_bytes()))})
}
fn selected_park(
    pair: &CheckedPair,
    function: usize,
) -> Result<Option<crate::mir::Temp>, OutputError> {
    let mut parks = pair.parks().iter().filter(|park| park.function == function);
    let Some(park) = parks.next() else {
        return if pair.program.entries.contains(&function) {
            Err(invariant("missing selected park for role"))
        } else {
            Ok(None)
        };
    };
    if parks.next().is_some() || !pair.program.entries.contains(&function) {
        return Err(invariant("duplicate or nonrole selected park"));
    }
    let source = super::mir::core_at(&pair.program.functions[function].body, &park.core_path)
        .ok_or_else(|| invariant("unresolved selected Core park"))?;
    let crate::types::ExprKind::While { condition, body } = &source.kind else {
        return Err(invariant("selected Core park is not while"));
    };
    if !matches!(condition.kind, crate::types::ExprKind::Boolean(true))
        || !matches!(body.kind, crate::types::ExprKind::Unit)
    {
        return Err(invariant("selected Core park is not literal true/unit"));
    }
    let instruction = super::mir::mir_at(&pair.functions[function].body, &park.mir_path)
        .ok_or_else(|| invariant("unresolved selected MIR park"))?;
    if !matches!(instruction.kind, crate::mir::Operation::While { .. })
        || instruction.destination.ty != Type::Unit
    {
        return Err(invariant("selected MIR park is not unit while"));
    }
    Ok(Some(instruction.destination))
}
fn byte_range(range: Range<usize>, text: &str) -> Result<Value, OutputError> {
    if range.start >= range.end
        || range.end > text.len()
        || !text.is_char_boundary(range.start)
        || !text.is_char_boundary(range.end)
    {
        return Err(invariant("unresolved boot artifact range"));
    }
    Ok(json!({"start":range.start,"end":range.end}))
}
fn source_span(pair: &CheckedPair, span: Span) -> Result<Value, OutputError> {
    if pair.program._sources.is_empty() {
        return Ok(Value::Null);
    }
    let [source] = pair.program._sources.as_slice() else {
        return Err(invariant("boot source inventory changed"));
    };
    if span.source_id != 0
        || span.start > span.end
        || span.end > source.text.len()
        || !source.text.is_char_boundary(span.start)
        || !source.text.is_char_boundary(span.end)
    {
        return Err(invariant("unresolved boot source span"));
    }
    Ok(json!({"start":span.start,"end":span.end}))
}
fn origin_value(origin: &Origin) -> Value {
    let core: Vec<_> = origin
        .core_path
        .iter()
        .map(|edge| {
            let name = match edge {
                CoreEdge::LetValue => "letValue",
                CoreEdge::LetBody => "letBody",
                CoreEdge::WhileCondition => "whileCondition",
                CoreEdge::WhileBody => "whileBody",
                CoreEdge::IfCondition => "ifCondition",
                CoreEdge::IfThen => "ifThen",
                CoreEdge::IfElse => "ifElse",
                CoreEdge::UnaryOperand => "unaryOperand",
                CoreEdge::BinaryLeft => "binaryLeft",
                CoreEdge::BinaryRight => "binaryRight",
                CoreEdge::ConvertOperand => "convertOperand",
                CoreEdge::ProjectOperand => "projectOperand",
                CoreEdge::AssignValue => "assignValue",
                CoreEdge::CallArgument(index) => {
                    return json!({"edge":"callArgument","index":index});
                }
                CoreEdge::TupleField(index) => return json!({"edge":"tupleField","index":index}),
            };
            json!({"edge":name})
        })
        .collect();
    let blocks: Vec<_> = origin.mir_path.blocks.iter().map(|edge| json!({"instruction":edge.instruction,"child":match edge.child {
        BlockChild::MutableBody=>"mutableBody",BlockChild::WhileCondition=>"whileCondition",BlockChild::WhileBody=>"whileBody",BlockChild::BranchThen=>"branchThen",BlockChild::BranchElse=>"branchElse",
    }})).collect();
    json!({"function":origin.function,"core_path":core,"mir_path":{"blocks":blocks,"instruction":origin.mir_path.instruction}})
}
fn signature(
    id: usize,
    function: &crate::mir::Function,
    role: bool,
    text: &mut Buffer,
) -> fmt::Result {
    if role {
        write!(text, "_Noreturn void anl_boot_f{id}(")?;
    } else {
        write!(
            text,
            "static {} anl_boot_f{id}(",
            codegen::c_type(function.result)
        )?;
    }
    if function.params.is_empty() {
        text.write_str("void")?;
    }
    for (i, param) in function.params.iter().enumerate() {
        if i > 0 {
            text.write_str(", ")?;
        }
        write!(text, "{} t{}", codegen::c_type(param.ty), param.id)?;
    }
    text.write_str(")")
}

/// Emit freestanding source artifacts from a checked canonical pair, without invoking a target tool.
pub fn emit(pair: &CheckedPair) -> Result<Bundle, OutputError> {
    let mut illegal_rows = pair
        .program
        .primitives
        .iter()
        .filter(|p| matches!(p.operation, Operation::IllegalInstruction { .. }));
    let illegal = illegal_rows.next();
    if illegal_rows.next().is_some()
        || illegal.is_some_and(|p| {
            pair.program.profile != Profile::V2
                || !matches!(p.operation, Operation::IllegalInstruction { authority: 0 })
        })
    {
        return Err(invariant(
            "invalid illegal primitive implementation inventory",
        ));
    }
    let core = super::export_pair_core(pair)?;
    let mir = super::export_mir(pair)?;
    let selected_parks: Vec<_> = (0..pair.functions.len())
        .map(|function| selected_park(pair, function))
        .collect::<Result<_, _>>()?;
    if selected_parks.iter().flatten().count() != 3 {
        return Err(invariant("selected park inventory is not three"));
    }
    let mut c = Buffer::new(
        Some(codegen::MAX_PRODUCT_C_BYTES),
        "boot C output exceeds 67108864 bytes",
    );
    let mut function_ranges = Vec::new();
    let mut primitive_ranges = Vec::new();
    let mut instruction_ranges = BTreeMap::new();
    let mut helper_count = 0;
    let result = (|| {
        templates::header(pair.program.profile, &mut c)?;
        codegen::emit_shapes(&pair.functions, &mut c)?;
        helper_count = codegen::emit_boot_helpers(&pair.functions, &mut c)?;
        for (id, function) in pair.functions.iter().enumerate() {
            signature(id, function, pair.program.entries.contains(&id), &mut c)?;
            c.write_str(";\n")?;
        }
        for primitive in &pair.program.primitives {
            let start = c.len();
            if matches!(primitive.operation, Operation::IllegalInstruction { .. }) {
                templates::illegal_declaration(primitive.id, &mut c)?;
            } else {
                templates::primitive(primitive, &mut c)?;
            }
            primitive_ranges.push(start..c.len());
        }
        for (id, function) in pair.functions.iter().enumerate() {
            let role = pair.program.entries.contains(&id);
            if function.view.is_some() || (role && function.result != Type::Unit) {
                return Err(fmt::Error);
            }
            let start = c.len();
            signature(id, function, role, &mut c)?;
            c.write_str(" {\n")?;
            let mut body = codegen::BodyEmission::boot(selected_parks[id]);
            codegen::emit_block(&function.body, &mut c, 1, id, None, &mut body)?;
            let ranges = body.finish()?;
            if !role {
                writeln!(c, "    return t{};", function.body.yield_value.id)?;
            }
            c.write_str("}\n")?;
            function_ranges.push(start..c.len());
            for (temp, range) in ranges {
                if instruction_ranges.insert((id, temp), range).is_some() {
                    return Err(fmt::Error);
                }
            }
        }
        Ok(())
    })();
    let c = rendered(c, result)?;
    let mut assembly = Buffer::new(
        Some(MAX_ASSEMBLY),
        "boot assembly output exceeds 1048576 bytes",
    );
    let mut abi_ranges = Vec::new();
    let mut illegal_range = None;
    let result = (|| {
        assembly.write_str(templates::ASSEMBLY_HEADER)?;
        for (role, function) in pair.program.entries.iter().enumerate() {
            let start = assembly.len();
            templates::entry(role, *function, &mut assembly)?;
            abi_ranges.push(start..assembly.len());
        }
        if let Some(primitive) = illegal {
            let start = assembly.len();
            templates::illegal_slot(primitive.id, &mut assembly)?;
            illegal_range = Some((primitive.id, start..assembly.len()));
        }
        assembly.write_str(templates::ASSEMBLY_FOOTER)
    })();
    let assembly = rendered(assembly, result)?;
    let mut linker = Buffer::new(Some(MAX_LINKER), "boot linker output exceeds 65536 bytes");
    let result = linker.write_str(templates::LINKER);
    let linker = rendered(linker, result)?;
    let setup = setup::build(
        pair,
        helper_count,
        &function_ranges,
        &primitive_ranges,
        &abi_ranges,
        &c,
        &assembly,
    )?;
    let functions: Vec<_> = pair.program.functions.iter().enumerate().map(|(id,f)| Ok(json!({
        "id":id,"name":f.name,"symbol":format!("anl_boot_f{id}"),"source_span":source_span(pair,f.span)?,"c_range":byte_range(function_ranges[id].clone(),&c)?,
    }))).collect::<Result<_,OutputError>>()?;
    let primitives: Vec<_> = pair.program.primitives.iter().zip(primitive_ranges).map(|(p,range)| {
        let (artifact, range, text) = if matches!(p.operation, Operation::IllegalInstruction { .. }) {
            let (id, range) = illegal_range.take().ok_or_else(|| invariant("missing illegal primitive implementation range"))?;
            if id != p.id {
                return Err(invariant("illegal primitive implementation ID differs"));
            }
            ("assembly", range, &assembly)
        } else {
            ("c", range, &c)
        };
        Ok(json!({"id":p.id,"operation":super::wire::operation_value(&p.operation),"symbol":format!("anl_boot_f{}",p.id),"artifact":artifact,"range":byte_range(range,text)?}))
    }).collect::<Result<_,OutputError>>()?;
    if illegal_range.is_some() {
        return Err(invariant("extra illegal primitive implementation range"));
    }
    let mut origins = Vec::new();
    for origin in pair.origins() {
        let instruction =
            super::mir::mir_at(&pair.functions[origin.function].body, &origin.mir_path)
                .ok_or_else(|| invariant("unresolved emitted MIR path"))?;
        let expr = super::mir::core_at(
            &pair.program.functions[origin.function].body,
            &origin.core_path,
        )
        .ok_or_else(|| invariant("unresolved emitted Core path"))?;
        let range = instruction_ranges
            .remove(&(origin.function, instruction.destination.id))
            .ok_or_else(|| invariant("missing emitted MIR range"))?;
        let mut value = origin_value(origin);
        value["source_span"] = source_span(pair, expr.span)?;
        value["c_range"] = byte_range(range, &c)?;
        origins.push(value);
    }
    if !instruction_ranges.is_empty() {
        return Err(invariant("extra emitted MIR range"));
    }
    let mut parks = json!({});
    let mut abi = json!({});
    for (role, name) in ["boot", "hardware", "language"].iter().enumerate() {
        parks[*name] = origin_value(&pair.parks()[role]);
        let symbol = [
            "anl_boot_entry",
            "anl_boot_hardware_entry",
            "anl_boot_language_entry",
        ][role];
        abi[*name] = json!({"function":pair.program.entries[role],"stack":if role==0 {0}else{1},"symbol":symbol,"range":byte_range(abi_ranges[role].clone(),&assembly)?});
    }
    let input = if let Some(source) = pair.program._sources.first() {
        json!({"kind":"source","bytes":source.text.len(),"sha256":format!("{:x}",Sha256::digest(source.text.as_bytes()))})
    } else {
        json!({"kind":"canonical_core","bytes":core.len(),"sha256":format!("{:x}",Sha256::digest(core.as_bytes()))})
    };
    let manifest = json!({"schema":pair.program.profile.bundle_schema(),"semantic_revision":pair.program.profile.semantic_revision(),"ordinary_semantic_revision":"anl-words-v1","target":pair.program.profile.target(),
        "input":input,"artifacts":{"core":identity("core.json",&core),"mir":identity("mir.json",&mir),"c":identity("program.c",&c),"assembly":identity("entry.S",&assembly),"linker":identity("link.ld",&linker)},
        "functions":functions,"primitives":primitives,"origins":origins,"parks":parks,"abi":abi});
    let mut out = Buffer::new(
        Some(MAX_MANIFEST),
        "boot manifest output exceeds 1048576 bytes",
    );
    let result = serde_json::to_writer(&mut out, &manifest);
    if result.is_ok() {
        let _ = std::io::Write::write_all(&mut out, b"\n");
    }
    let manifest = out.finish()?;
    result.map_err(|e| OutputError::Infrastructure(e.to_string()))?;
    Ok(Bundle {
        setup,
        files: [
            ("core.json", core),
            ("mir.json", mir),
            ("program.c", c),
            ("entry.S", assembly),
            ("link.ld", linker),
            ("manifest.json", manifest),
        ],
    })
}
