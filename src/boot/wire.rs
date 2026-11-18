use super::{CheckedProgram, Operation, Primitive, check};
use crate::{
    MAX_SOURCE_BYTES,
    bounded::{Buffer, OutputError},
    core::{self, ImportError, StrictValue, array, object, string, ty_words},
    diagnostic::Span,
    types::Function,
};
use serde_json::{Value, json};
use std::io::Write;

fn invalid(message: impl Into<String>) -> ImportError {
    ImportError::Invalid(message.into())
}
fn natural(v: &Value) -> Result<u64, ImportError> {
    v.as_u64().ok_or_else(|| invalid("expected uint64 natural"))
}
fn decimal(v: &Value) -> Result<u64, ImportError> {
    let s = string(v)?;
    let n = s
        .parse::<u64>()
        .map_err(|_| invalid("expected uint64 decimal string"))?;
    if n.to_string() != s {
        return Err(invalid("noncanonical uint64 string"));
    }
    Ok(n)
}
fn index(v: &Value, bound: usize) -> Result<usize, ImportError> {
    let n = natural(v)?;
    if n >= bound as u64 {
        return Err(invalid("boot index out of range"));
    }
    usize::try_from(n).map_err(|_| invalid("boot index out of range"))
}
fn effects(v: &Value) -> Result<Vec<u64>, ImportError> {
    array(v)?.iter().map(natural).collect()
}
fn metadata(entries: [usize; 3]) -> Value {
    json!({
        "schema": super::SCHEMA, "semantic_revision": super::SEMANTIC_REVISION,
        "ordinary_semantic_revision": "anl-words-v1",
        "target_profile": {"id": super::TARGET, "generated_isa": "rv64im_zicsr", "abi": "lp64", "endianness": "little", "privilege": "s", "translation": "bare", "harts": 1, "ram_base": "2147483648", "ram_bytes": 134217728},
        "image": {"base": "2149580800", "limit": 1048576},
        "stacks": [{"id": 0, "name": "boot_stack", "bytes": 16384, "alignment": 16}, {"id": 1, "name": "terminal_stack", "bytes": 4096, "alignment": 16}],
        "devices": [{"id": 0, "name": "uart0", "authority": 1, "base": "268435456", "size": 256, "read8": [5], "write8": [0,1,2,3,4]}],
        "entries": {"boot": {"function": entries[0], "stack": 0}, "hardware": {"function": entries[1], "stack": 1}, "language": {"function": entries[2], "stack": 1}}
    })
}
fn operation_value(op: &Operation) -> Value {
    match op {
        Operation::Read8 { region, offset } => {
            json!({"tag":"mmio_read8", "region":region, "offset":offset})
        }
        Operation::Write8 { region, offset } => {
            json!({"tag":"mmio_write8", "region":region, "offset":offset})
        }
        Operation::Fence { region } => json!({"tag":"io_fence", "region":region}),
        Operation::CsrClear {
            authority,
            register,
            mask,
        } => {
            json!({"tag":"csr_clear", "authority":authority, "register":register, "mask":mask.to_string()})
        }
        Operation::CsrWrite {
            authority,
            register,
            value,
        } => {
            json!({"tag":"csr_write", "authority":authority, "register":register, "value":value.to_string()})
        }
        Operation::InstallTrap { authority, handler } => {
            json!({"tag":"install_trap", "authority":authority, "handler":handler})
        }
    }
}
fn operation(v: &Value) -> Result<Operation, ImportError> {
    let tag = string(
        v.get("tag")
            .ok_or_else(|| invalid("missing operation tag"))?,
    )?;
    Ok(match tag {
        "mmio_read8" | "mmio_write8" => {
            let o = object(v, &["tag", "region", "offset"])?;
            let region = natural(&o["region"])?;
            let offset = natural(&o["offset"])?;
            if tag == "mmio_read8" {
                Operation::Read8 { region, offset }
            } else {
                Operation::Write8 { region, offset }
            }
        }
        "io_fence" => {
            let o = object(v, &["tag", "region"])?;
            Operation::Fence {
                region: natural(&o["region"])?,
            }
        }
        "csr_clear" => {
            let o = object(v, &["tag", "authority", "register", "mask"])?;
            Operation::CsrClear {
                authority: natural(&o["authority"])?,
                register: string(&o["register"])?.into(),
                mask: decimal(&o["mask"])?,
            }
        }
        "csr_write" => {
            let o = object(v, &["tag", "authority", "register", "value"])?;
            Operation::CsrWrite {
                authority: natural(&o["authority"])?,
                register: string(&o["register"])?.into(),
                value: decimal(&o["value"])?,
            }
        }
        "install_trap" => {
            let o = object(v, &["tag", "authority", "handler"])?;
            Operation::InstallTrap {
                authority: natural(&o["authority"])?,
                handler: natural(&o["handler"])?,
            }
        }
        _ => return Err(invalid("unknown boot operation")),
    })
}

// Preserve raw numeric spelling before serde can normalize -0 or an exponent.
fn numeric_tokens(text: &str) -> Result<(), ImportError> {
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'"' {
            i += 1;
            while i < b.len() && b[i] != b'"' {
                if b[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            i += usize::from(i < b.len());
        } else if b[i].is_ascii_digit() || matches!(b[i], b'-' | b'+') {
            let start = i;
            i += 1;
            while i < b.len()
                && (b[i].is_ascii_digit() || matches!(b[i], b'.' | b'e' | b'E' | b'-' | b'+'))
            {
                i += 1;
            }
            let token = &text[start..i];
            let n = token
                .parse::<u64>()
                .map_err(|_| invalid("unquoted numbers must be canonical uint64 naturals"))?;
            if n.to_string() != token {
                return Err(invalid(
                    "unquoted numbers must be canonical uint64 naturals",
                ));
            }
        } else {
            i += 1;
        }
    }
    Ok(())
}

/// Read the complete strict boot Core document and independently check all bodies.
pub fn import_core(text: &str) -> Result<CheckedProgram, ImportError> {
    if text.len() > MAX_SOURCE_BYTES {
        return Err(ImportError::ResourceLimit(
            "JSON exceeds 1048576 bytes".into(),
        ));
    }
    numeric_tokens(text)?;
    let StrictValue(value) = serde_json::from_str(text).map_err(|e| {
        let message = e.to_string();
        if e.is_syntax() && message.starts_with("recursion limit exceeded at line ") {
            ImportError::ResourceLimit(message)
        } else {
            invalid(message)
        }
    })?;
    let root = object(
        &value,
        &[
            "schema",
            "semantic_revision",
            "ordinary_semantic_revision",
            "target_profile",
            "image",
            "stacks",
            "devices",
            "entries",
            "functions",
        ],
    )?;
    let rows = array(&root["functions"])?;
    let entry_rows = object(&root["entries"], &["boot", "hardware", "language"])?;
    let mut entries = [0; 3];
    for (i, key) in ["boot", "hardware", "language"].into_iter().enumerate() {
        let row = object(&entry_rows[key], &["function", "stack"])?;
        entries[i] = index(&row["function"], rows.len())?;
    }
    let expected = metadata(entries);
    for (key, value) in expected.as_object().expect("metadata object") {
        if &root[key] != value {
            return Err(invalid(format!("invalid boot {key}")));
        }
    }
    let mut signatures = Vec::with_capacity(rows.len());
    let mut defined_count = 0;
    let mut primitive_phase = false;
    for (id, row) in rows.iter().enumerate() {
        let kind = string(
            row.get("kind")
                .ok_or_else(|| invalid("missing declaration kind"))?,
        )?;
        let fields: &[&str] = match kind {
            "defined" if !primitive_phase => {
                defined_count += 1;
                &[
                    "kind", "id", "name", "view", "params", "result", "effects", "body",
                ]
            }
            "primitive" => {
                primitive_phase = true;
                &[
                    "kind",
                    "id",
                    "name",
                    "operation",
                    "params",
                    "result",
                    "effects",
                ]
            }
            _ => return Err(invalid("expected defined prefix then primitive suffix")),
        };
        let row = object(row, fields)?;
        if natural(&row["id"])? != id as u64 {
            return Err(invalid("function ID must equal table index"));
        }
        if kind == "defined" && !row["view"].is_null() {
            return Err(invalid("boot functions cannot take views"));
        }
        let params = array(&row["params"])?
            .iter()
            .map(|v| ty_words(v, true, true))
            .collect::<Result<Vec<_>, _>>()?;
        signatures.push((params, ty_words(&row["result"], true, true)?));
    }
    let mut functions = Vec::with_capacity(defined_count);
    let mut declared_effects = Vec::with_capacity(defined_count);
    let mut primitives = Vec::new();
    for (id, row) in rows.iter().enumerate() {
        let (params, result) = &signatures[id];
        let name = string(&row["name"])?.to_owned();
        let effects = effects(&row["effects"])?;
        if id < defined_count {
            let body = core::check_boot_body(&row["body"], params, *result, &signatures)?;
            functions.push(Function {
                view: None,
                name,
                params: params.clone(),
                result: *result,
                body,
                span: Span::default(),
            });
            declared_effects.push(effects);
        } else {
            primitives.push(Primitive {
                id,
                name,
                operation: operation(&row["operation"])?,
                params: params.clone(),
                result: *result,
                effects,
            });
        }
    }
    check::finish(
        functions,
        declared_effects,
        primitives,
        entries,
        Default::default(),
        None,
    )
    .map_err(|e| invalid(e.message))
}

/// Materialize the entire bounded document, including its final newline, before publication.
pub fn export_core(program: &CheckedProgram) -> Result<String, OutputError> {
    let mut value = metadata(program.entries);
    let mut rows = Vec::new();
    for (id, f) in program.functions.iter().enumerate() {
        rows.push(json!({"kind":"defined", "id":id, "name":f.name, "view":null, "params":f.params, "result":f.result, "effects":program.effects[id], "body":f.body}));
    }
    for p in &program.primitives {
        rows.push(json!({"kind":"primitive", "id":p.id, "name":p.name, "operation":operation_value(&p.operation), "params":p.params, "result":p.result, "effects":p.effects}));
    }
    value["functions"] = Value::Array(rows);
    let mut out = Buffer::new(
        Some(MAX_SOURCE_BYTES),
        "boot Core output exceeds 1048576 bytes",
    );
    let result = serde_json::to_writer(&mut out, &value);
    if result.is_ok() {
        let _ = out.write_all(b"\n");
    }
    let text = out.finish()?;
    result.map_err(|e| OutputError::Infrastructure(e.to_string()))?;
    Ok(text)
}
