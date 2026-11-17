use super::*;
use crate::{
    bounded::{Buffer, OutputError},
    core::{self, ImportError, StrictValue},
};
use serde::{
    Serialize, Serializer,
    ser::{SerializeMap, SerializeSeq},
};
use serde_json::Value;

pub(crate) const MAX_BYTES: usize = 8_388_608;
impl Serialize for Temp {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(2))?;
        m.serialize_entry("id", &self.id)?;
        m.serialize_entry("ty", &self.ty)?;
        m.end()
    }
}
impl Serialize for Slot {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        Temp {
            id: self.id,
            ty: self.ty,
        }
        .serialize(s)
    }
}
impl Serialize for Block {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(2))?;
        m.serialize_entry("instructions", &self.instructions)?;
        m.serialize_entry("yield", &self.yield_value)?;
        m.end()
    }
}
impl Serialize for Instruction {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(2))?;
        m.serialize_entry("destination", &self.destination)?;
        m.serialize_entry("operation", &self.kind)?;
        m.end()
    }
}
impl Serialize for Operation {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(None)?;
        macro_rules! tag {
            ($t:expr) => {
                m.serialize_entry("tag", $t)?
            };
        }
        macro_rules! field {
            ($k:expr,$v:expr) => {
                m.serialize_entry($k, $v)?
            };
        }
        match self {
            Self::Integer(v) => {
                tag!("integer");
                field!("value", &v.to_string());
            }
            Self::Boolean(v) => {
                tag!("boolean");
                field!("value", v);
            }
            Self::Unit => {
                tag!("unit");
            }
            Self::Tuple(v) => {
                tag!("tuple");
                field!("fields", v);
            }
            Self::Project(v, i) => {
                tag!("project");
                field!("value", v);
                field!("index", i);
            }
            Self::Unary(op, v) => {
                tag!("unary");
                field!("op", op.as_str());
                field!("operand", v);
            }
            Self::Binary(op, a, b) => {
                tag!("binary");
                field!("op", op.as_str());
                field!("left", a);
                field!("right", b);
            }
            Self::Call(f, a) => {
                tag!("call");
                field!("function", f);
                field!("arguments", a);
            }
            Self::MutableScope {
                slot,
                initial,
                body,
            } => {
                tag!("mutable_scope");
                field!("slot", slot);
                field!("initial", initial);
                field!("body", body);
            }
            Self::Load(v) => {
                tag!("load");
                field!("slot", v);
            }
            Self::Store(a, b) => {
                tag!("store");
                field!("slot", a);
                field!("value", b);
            }
            Self::While { condition, body } => {
                tag!("while");
                field!("condition", condition);
                field!("body", body);
            }
            Self::Branch {
                condition,
                then_block,
                else_block,
            } => {
                tag!("branch");
                field!("condition", condition);
                field!("then", then_block);
                field!("else", else_block);
            }
            Self::Memory(memory) => match memory.as_ref() {
                MemoryOperation::HeapScope {
                    site,
                    owner,
                    length,
                    initial,
                    success,
                    failure,
                } => {
                    tag!("heap_scope");
                    field!("site", site);
                    field!("owner", owner);
                    field!("length", length);
                    field!("initial", initial);
                    field!("success", success);
                    field!("failure", failure);
                }
                MemoryOperation::Length { resource } => {
                    tag!("buffer_length");
                    field!("resource", resource);
                }
                MemoryOperation::Read { resource, index } => {
                    tag!("buffer_read");
                    field!("resource", resource);
                    field!("index", index);
                }
                MemoryOperation::Write {
                    resource,
                    index,
                    value,
                } => {
                    tag!("buffer_write");
                    field!("resource", resource);
                    field!("index", index);
                    field!("value", value);
                }
                MemoryOperation::CallView {
                    function,
                    resource,
                    mode,
                    arguments,
                } => {
                    tag!("call_view");
                    field!("function", function);
                    field!("resource", resource);
                    field!("mode", mode.as_str());
                    field!("arguments", arguments);
                }
            },
        }
        m.end()
    }
}
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
        m.serialize_entry("schema", "anl-memory-mir-v1")?;
        m.serialize_entry("semantic_revision", crate::memory::SEMANTIC_REVISION)?;
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
fn temp(v: &Value) -> std::result::Result<Temp, ImportError> {
    let o = core::object(v, &["id", "ty"])?;
    Ok(Temp {
        id: core::natural(&o["id"])?,
        ty: core::ty(&o["ty"], true)?,
    })
}
fn slot(v: &Value) -> std::result::Result<Slot, ImportError> {
    let t = temp(v)?;
    Ok(Slot { id: t.id, ty: t.ty })
}
fn temps(v: &Value) -> std::result::Result<Vec<Temp>, ImportError> {
    core::array(v)?.iter().map(temp).collect()
}
#[derive(Default)]
struct Counts {
    temps: usize,
    slots: usize,
    resources: usize,
}
fn block(v: &Value, depth: usize, counts: &mut Counts) -> std::result::Result<Block, ImportError> {
    if depth >= crate::MAX_DEPTH {
        return Err(ImportError::ResourceLimit(
            "memory MIR block depth exceeded".into(),
        ));
    }
    let o = core::object(v, &["instructions", "yield"])?;
    let mut instructions = Vec::new();
    for v in core::array(&o["instructions"])? {
        let i = core::object(v, &["destination", "operation"])?;
        let destination = temp(&i["destination"])?;
        let kind = operation(&i["operation"], depth + 1, counts)?;
        counts.temps += 1;
        instructions.push(Instruction { destination, kind });
    }
    Ok(Block {
        instructions,
        yield_value: temp(&o["yield"])?,
    })
}
fn operation(
    v: &Value,
    depth: usize,
    c: &mut Counts,
) -> std::result::Result<Operation, ImportError> {
    let tag = v
        .get("tag")
        .and_then(Value::as_str)
        .ok_or_else(|| bad("missing MIR operation tag"))?;
    let fields: &[&str] = match tag {
        "integer" | "boolean" => &["tag", "value"],
        "unit" => &["tag"],
        "tuple" => &["tag", "fields"],
        "project" => &["tag", "value", "index"],
        "unary" => &["tag", "op", "operand"],
        "binary" => &["tag", "op", "left", "right"],
        "call" => &["tag", "function", "arguments"],
        "mutable_scope" => &["tag", "slot", "initial", "body"],
        "load" => &["tag", "slot"],
        "store" => &["tag", "slot", "value"],
        "while" => &["tag", "condition", "body"],
        "branch" => &["tag", "condition", "then", "else"],
        "heap_scope" => &[
            "tag", "site", "owner", "length", "initial", "success", "failure",
        ],
        "buffer_length" => &["tag", "resource"],
        "buffer_read" => &["tag", "resource", "index"],
        "buffer_write" => &["tag", "resource", "index", "value"],
        "call_view" => &["tag", "function", "resource", "mode", "arguments"],
        _ => return Err(bad("unknown MIR operation")),
    };
    let o = core::object(v, fields)?;
    Ok(match tag {
        "integer" => {
            let t = core::string(&o["value"])?;
            let n = t.parse::<i64>().map_err(|_| bad("invalid MIR integer"))?;
            if n.to_string() != t {
                return Err(bad("noncanonical MIR integer"));
            }
            Operation::Integer(n)
        }
        "boolean" => Operation::Boolean(
            o["value"]
                .as_bool()
                .ok_or_else(|| bad("invalid MIR bool"))?,
        ),
        "unit" => Operation::Unit,
        "tuple" => Operation::Tuple(temps(&o["fields"])?),
        "project" => Operation::Project(temp(&o["value"])?, core::natural(&o["index"])?),
        "unary" => Operation::Unary(
            match core::string(&o["op"])? {
                "neg" => UnaryOp::Neg,
                "not" => UnaryOp::Not,
                _ => return Err(bad("invalid MIR unary")),
            },
            temp(&o["operand"])?,
        ),
        "binary" => Operation::Binary(
            BinaryOp::from_name(core::string(&o["op"])?)
                .ok_or_else(|| bad("invalid MIR binary"))?,
            temp(&o["left"])?,
            temp(&o["right"])?,
        ),
        "call" => Operation::Call(core::natural(&o["function"])?, temps(&o["arguments"])?),
        "mutable_scope" => {
            c.slots += 1;
            Operation::MutableScope {
                slot: slot(&o["slot"])?,
                initial: temp(&o["initial"])?,
                body: block(&o["body"], depth, c)?,
            }
        }
        "load" => Operation::Load(slot(&o["slot"])?),
        "store" => Operation::Store(slot(&o["slot"])?, temp(&o["value"])?),
        "while" => Operation::While {
            condition: block(&o["condition"], depth, c)?,
            body: block(&o["body"], depth, c)?,
        },
        "branch" => Operation::Branch {
            condition: temp(&o["condition"])?,
            then_block: block(&o["then"], depth, c)?,
            else_block: block(&o["else"], depth, c)?,
        },
        _ => Operation::Memory(Box::new(match tag {
            "heap_scope" => {
                c.resources += 1;
                MemoryOperation::HeapScope {
                    site: core::natural(&o["site"])?,
                    owner: core::natural(&o["owner"])?,
                    length: temp(&o["length"])?,
                    initial: block(&o["initial"], depth, c)?,
                    success: block(&o["success"], depth, c)?,
                    failure: block(&o["failure"], depth, c)?,
                }
            }
            "buffer_length" => MemoryOperation::Length {
                resource: core::natural(&o["resource"])?,
            },
            "buffer_read" => MemoryOperation::Read {
                resource: core::natural(&o["resource"])?,
                index: temp(&o["index"])?,
            },
            "buffer_write" => MemoryOperation::Write {
                resource: core::natural(&o["resource"])?,
                index: temp(&o["index"])?,
                value: block(&o["value"], depth, c)?,
            },
            "call_view" => MemoryOperation::CallView {
                function: core::natural(&o["function"])?,
                resource: core::natural(&o["resource"])?,
                mode: core::view(&o["mode"])?,
                arguments: temps(&o["arguments"])?,
            },
            _ => return Err(bad("unknown memory MIR operation")),
        })),
    })
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
    if core::string(&o["schema"])? != "anl-memory-mir-v1"
        || core::string(&o["semantic_revision"])? != crate::memory::SEMANTIC_REVISION
    {
        return Err(bad("unsupported memory MIR revision"));
    }
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
        let params = temps(&o["params"])?;
        let mut counts = Counts {
            temps: params.len(),
            slots: 0,
            resources: usize::from(view.is_some()),
        };
        let body = block(&o["body"], 0, &mut counts)?;
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
            result: core::ty(&o["result"], true)?,
            body,
            temp_count,
            slot_count,
            resource_count,
        });
    }
    let program = Program {
        allocation_profile: Some(profile),
        functions,
        entry: core::natural(&o["entry"])?,
    };
    validate(&program).map_err(|e| bad(&e.to_string()))?;
    Ok(program)
}
