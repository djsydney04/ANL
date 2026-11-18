use super::body_wire::{Counts, block, temps};
use super::*;
use crate::{
    bounded::{Buffer, OutputError},
    core::{self, ImportError, StrictValue},
};
use serde::{
    Serialize, Serializer,
    ser::{SerializeMap, SerializeSeq},
};

pub(crate) const MAX_BYTES: usize = 8_388_608;
struct FunctionWire<'a>(usize, &'a Function);
impl Serialize for FunctionWire<'_> {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(8))?;
        let f = self.1;
        m.serialize_entry("id", &self.0)?;
        m.serialize_entry(
            "view",
            &f.view.map(
                |(mode, resource)| serde_json::json!({"mode":mode.as_str(),"resource":resource}),
            ),
        )?;
        m.serialize_entry("params", &f.params)?;
        m.serialize_entry("result", &f.result)?;
        m.serialize_entry("body", &f.body)?;
        m.serialize_entry("temp_count", &f.temp_count)?;
        m.serialize_entry("slot_count", &f.slot_count)?;
        m.serialize_entry("resource_count", &f.resource_count)?;
        m.end()
    }
}
struct Functions<'a>(&'a [Function]);
impl Serialize for Functions<'_> {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut seq = s.serialize_seq(Some(self.0.len()))?;
        for (i, f) in self.0.iter().enumerate() {
            seq.serialize_element(&FunctionWire(i, f))?;
        }
        seq.end()
    }
}
impl Serialize for Program {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(5))?;
        m.serialize_entry(
            "schema",
            if self.revision == IrRevision::WordsV4 {
                "anl-words-mir-v1"
            } else {
                "anl-memory-mir-v1"
            },
        )?;
        m.serialize_entry("semantic_revision", self.revision.semantic_revision())?;
        m.serialize_entry(
            "allocation_profile",
            &self.allocation_profile.expect("memory MIR profile").json(),
        )?;
        m.serialize_entry("functions", &Functions(&self.functions))?;
        m.serialize_entry("entry", &self.entry)?;
        m.end()
    }
}
pub(crate) fn export(program: &Program) -> std::result::Result<String, OutputError> {
    let mut b = Buffer::new(Some(MAX_BYTES), "memory MIR exceeds 8388608 bytes");
    if let Err(e) = serde_json::to_writer(&mut b, program)
        && !b.exhausted()
    {
        return Err(OutputError::Infrastructure(e.to_string()));
    }
    b.finish()
}
fn bad(s: &str) -> ImportError {
    ImportError::Invalid(s.into())
}
pub(crate) fn import(text: &str) -> std::result::Result<Program, ImportError> {
    if text.len() > MAX_BYTES {
        return Err(ImportError::ResourceLimit(
            "memory MIR exceeds 8388608 bytes".into(),
        ));
    }
    let StrictValue(v) = serde_json::from_str(text).map_err(|e| {
        let message = e.to_string();
        if e.is_syntax() && message.starts_with("recursion limit exceeded at line ") {
            ImportError::ResourceLimit(message)
        } else {
            bad(&message)
        }
    })?;
    let o = core::object(
        &v,
        &[
            "schema",
            "semantic_revision",
            "allocation_profile",
            "functions",
            "entry",
        ],
    )?;
    let revision = match (
        core::string(&o["schema"])?,
        core::string(&o["semantic_revision"])?,
    ) {
        ("anl-memory-mir-v1", crate::memory::SEMANTIC_REVISION) => IrRevision::MemoryV3,
        ("anl-words-mir-v1", "anl-words-v1") => IrRevision::WordsV4,
        _ => return Err(bad("unsupported memory MIR revision")),
    };
    let words = revision == IrRevision::WordsV4;
    let profile = core::profile(&o["allocation_profile"])?;
    let mut functions = Vec::new();
    for (id, v) in core::array(&o["functions"])?.iter().enumerate() {
        let o = core::object(
            v,
            &[
                "id",
                "view",
                "params",
                "result",
                "body",
                "temp_count",
                "slot_count",
                "resource_count",
            ],
        )?;
        if core::natural(&o["id"])? != id {
            return Err(bad("MIR function ID mismatch"));
        }
        let view = if o["view"].is_null() {
            None
        } else {
            let v = core::object(&o["view"], &["mode", "resource"])?;
            Some((core::view(&v["mode"])?, core::natural(&v["resource"])?))
        };
        let params = temps(&o["params"], words, None)?;
        let mut counts = Counts {
            temps: params.len(),
            slots: 0,
            resources: usize::from(view.is_some()),
        };
        let body = block(&o["body"], 0, &mut counts, words, None)?;
        let temp_count = core::natural(&o["temp_count"])?;
        let slot_count = core::natural(&o["slot_count"])?;
        let resource_count = core::natural(&o["resource_count"])?;
        if temp_count != counts.temps
            || slot_count != counts.slots
            || resource_count != counts.resources
        {
            return Err(bad("MIR counts do not match actual definitions"));
        }
        functions.push(Function {
            view,
            params,
            result: core::ty_words(&o["result"], true, words)?,
            body,
            temp_count,
            slot_count,
            resource_count,
        });
    }
    let program = Program {
        revision,
        allocation_profile: Some(profile),
        functions,
        entry: core::natural(&o["entry"])?,
    };
    validate(&program).map_err(|e| bad(&e.to_string()))?;
    Ok(program)
}
