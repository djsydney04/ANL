use super::*;
use crate::core::{self, ImportError};
use serde::{Serialize, Serializer, ser::SerializeMap};
use serde_json::Value;
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
            Self::Word(w) => {
                tag!("word");
                field!("width", &w.width().bits());
                field!("value", &w.value().to_string());
            }
            Self::Convert {
                mode,
                target,
                operand,
            } => {
                tag!("convert");
                field!("mode", mode.as_str());
                field!("target", target);
                field!("operand", operand);
            }

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

#[derive(Clone, Copy)]
pub(super) struct BodyLimits {
    pub temps: usize,
    pub slots: usize,
    pub functions: usize,
}
fn bad(s: &str) -> ImportError {
    ImportError::Invalid(s.into())
}
fn number(v: &Value, bound: Option<usize>) -> std::result::Result<usize, ImportError> {
    if let Some(bound) = bound {
        let n = v.as_u64().ok_or_else(|| bad("expected uint64 index"))?;
        if n >= bound as u64 {
            return Err(bad("MIR index outside actual inventory"));
        }
        usize::try_from(n).map_err(|_| bad("MIR index does not fit host"))
    } else {
        core::natural(v)
    }
}
pub(super) fn temp(
    v: &Value,
    words: bool,
    bound: Option<usize>,
) -> std::result::Result<Temp, ImportError> {
    let o = core::object(v, &["id", "ty"])?;
    Ok(Temp {
        id: number(&o["id"], bound)?,
        ty: core::ty_words(&o["ty"], true, words)?,
    })
}
fn slot(
    v: &Value,
    words: bool,
    limits: Option<BodyLimits>,
) -> std::result::Result<Slot, ImportError> {
    let t = temp(v, words, limits.map(|n| n.slots))?;
    Ok(Slot { id: t.id, ty: t.ty })
}
pub(super) fn temps(
    v: &Value,
    words: bool,
    bound: Option<usize>,
) -> std::result::Result<Vec<Temp>, ImportError> {
    core::array(v)?
        .iter()
        .map(|v| temp(v, words, bound))
        .collect()
}
#[derive(Default)]
pub(super) struct Counts {
    pub temps: usize,
    pub slots: usize,
    pub resources: usize,
}
pub(super) fn block(
    v: &Value,
    depth: usize,
    counts: &mut Counts,
    words: bool,
    limits: Option<BodyLimits>,
) -> std::result::Result<Block, ImportError> {
    if depth >= crate::MAX_DEPTH {
        return Err(ImportError::ResourceLimit(
            if limits.is_some() {
                "boot MIR block depth exceeded"
            } else {
                "memory MIR block depth exceeded"
            }
            .into(),
        ));
    }
    let o = core::object(v, &["instructions", "yield"])?;
    let mut instructions = Vec::new();
    for v in core::array(&o["instructions"])? {
        let i = core::object(v, &["destination", "operation"])?;
        let destination = temp(&i["destination"], words, limits.map(|n| n.temps))?;
        let kind = operation(&i["operation"], depth + 1, counts, words, limits)?;
        counts.temps += 1;
        instructions.push(Instruction { destination, kind });
    }
    Ok(Block {
        instructions,
        yield_value: temp(&o["yield"], words, limits.map(|n| n.temps))?,
    })
}
fn operation(
    v: &Value,
    depth: usize,
    c: &mut Counts,
    words: bool,
    limits: Option<BodyLimits>,
) -> std::result::Result<Operation, ImportError> {
    let tag = v
        .get("tag")
        .and_then(Value::as_str)
        .ok_or_else(|| bad("missing MIR operation tag"))?;
    if limits.is_some()
        && matches!(
            tag,
            "heap_scope" | "buffer_length" | "buffer_read" | "buffer_write" | "call_view"
        )
    {
        return Err(bad("boot MIR forbids memory"));
    }
    if limits.is_some() && tag == "word" {
        number(&v["width"], Some(65))?;
    }
    let fields: &[&str] = match tag {
        "word" if words => &["tag", "width", "value"],
        "convert" if words => &["tag", "mode", "target", "operand"],
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
        "word" => Operation::Word(core::word_payload(&o["width"], &o["value"])?),
        "convert" => Operation::Convert {
            mode: ConvertMode::from_name(core::string(&o["mode"])?)
                .ok_or_else(|| bad("invalid conversion mode"))?,
            target: core::ty_words(&o["target"], false, true)?,
            operand: temp(&o["operand"], words, limits.map(|n| n.temps))?,
        },
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
        "tuple" => Operation::Tuple(temps(&o["fields"], words, limits.map(|n| n.temps))?),
        "project" => Operation::Project(
            temp(&o["value"], words, limits.map(|n| n.temps))?,
            number(&o["index"], limits.map(|_| types::MAX_TUPLE_FIELDS))?,
        ),
        "unary" => Operation::Unary(
            match core::string(&o["op"])? {
                "neg" => UnaryOp::Neg,
                "not" => UnaryOp::Not,
                "bit_not" if words => UnaryOp::BitNot,
                _ => return Err(bad("invalid MIR unary")),
            },
            temp(&o["operand"], words, limits.map(|n| n.temps))?,
        ),
        "binary" => Operation::Binary(
            BinaryOp::from_name(core::string(&o["op"])?)
                .filter(|op| words || !op.is_word())
                .ok_or_else(|| bad("invalid MIR binary"))?,
            temp(&o["left"], words, limits.map(|n| n.temps))?,
            temp(&o["right"], words, limits.map(|n| n.temps))?,
        ),
        "call" => Operation::Call(
            number(&o["function"], limits.map(|n| n.functions))?,
            temps(&o["arguments"], words, limits.map(|n| n.temps))?,
        ),
        "mutable_scope" => {
            c.slots += 1;
            Operation::MutableScope {
                slot: slot(&o["slot"], words, limits)?,
                initial: temp(&o["initial"], words, limits.map(|n| n.temps))?,
                body: block(&o["body"], depth, c, words, limits)?,
            }
        }
        "load" => Operation::Load(slot(&o["slot"], words, limits)?),
        "store" => Operation::Store(
            slot(&o["slot"], words, limits)?,
            temp(&o["value"], words, limits.map(|n| n.temps))?,
        ),
        "while" => Operation::While {
            condition: block(&o["condition"], depth, c, words, limits)?,
            body: block(&o["body"], depth, c, words, limits)?,
        },
        "branch" => Operation::Branch {
            condition: temp(&o["condition"], words, limits.map(|n| n.temps))?,
            then_block: block(&o["then"], depth, c, words, limits)?,
            else_block: block(&o["else"], depth, c, words, limits)?,
        },
        _ => Operation::Memory(Box::new(match tag {
            "heap_scope" => {
                c.resources += 1;
                MemoryOperation::HeapScope {
                    site: core::natural(&o["site"])?,
                    owner: core::natural(&o["owner"])?,
                    length: temp(&o["length"], words, limits.map(|n| n.temps))?,
                    initial: block(&o["initial"], depth, c, words, limits)?,
                    success: block(&o["success"], depth, c, words, limits)?,
                    failure: block(&o["failure"], depth, c, words, limits)?,
                }
            }
            "buffer_length" => MemoryOperation::Length {
                resource: core::natural(&o["resource"])?,
            },
            "buffer_read" => MemoryOperation::Read {
                resource: core::natural(&o["resource"])?,
                index: temp(&o["index"], words, limits.map(|n| n.temps))?,
            },
            "buffer_write" => MemoryOperation::Write {
                resource: core::natural(&o["resource"])?,
                index: temp(&o["index"], words, limits.map(|n| n.temps))?,
                value: block(&o["value"], depth, c, words, limits)?,
            },
            "call_view" => MemoryOperation::CallView {
                function: number(&o["function"], limits.map(|n| n.functions))?,
                resource: core::natural(&o["resource"])?,
                mode: core::view(&o["mode"])?,
                arguments: temps(&o["arguments"], words, limits.map(|n| n.temps))?,
            },
            _ => return Err(bad("unknown memory MIR operation")),
        })),
    })
}
