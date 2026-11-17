use crate::{
    bounded::{Buffer, OutputError},
    types::{Expr, ExprKind, Function, Program, ScalarType, Type},
};
use serde::{
    Serialize, Serializer,
    ser::{SerializeMap, SerializeSeq},
};

impl Serialize for ScalarType {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}
impl Serialize for Type {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if let Self::Tuple(shape) = self {
            let mut map = serializer.serialize_map(Some(1))?;
            map.serialize_entry("tuple", shape.fields())?;
            map.end()
        } else {
            serializer.serialize_str(self.as_str())
        }
    }
}
impl Serialize for Expr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("ty", &self.ty)?;
        match &self.kind {
            ExprKind::Integer(n) => {
                map.serialize_entry("tag", "integer")?;
                map.serialize_entry("value", &n.to_string())?;
            }
            ExprKind::Boolean(b) => {
                map.serialize_entry("tag", "boolean")?;
                map.serialize_entry("value", b)?;
            }
            ExprKind::Unit => {
                map.serialize_entry("tag", "unit")?;
            }
            ExprKind::Local(i) => {
                map.serialize_entry("tag", "local")?;
                map.serialize_entry("index", i)?;
            }
            ExprKind::Tuple(fields) => {
                map.serialize_entry("tag", "tuple")?;
                map.serialize_entry("fields", fields)?;
            }
            ExprKind::Project { value, index } => {
                map.serialize_entry("tag", "project")?;
                map.serialize_entry("value", value)?;
                map.serialize_entry("index", index)?;
            }
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                map.serialize_entry(
                    "tag",
                    if matches!(self.kind, ExprKind::LetMut { .. }) {
                        "let_mut"
                    } else {
                        "let"
                    },
                )?;
                map.serialize_entry("value", value)?;
                map.serialize_entry("body", body)?;
            }
            ExprKind::Assign { index, value } => {
                map.serialize_entry("tag", "assign")?;
                map.serialize_entry("index", index)?;
                map.serialize_entry("value", value)?;
            }
            ExprKind::While { condition, body } => {
                map.serialize_entry("tag", "while")?;
                map.serialize_entry("condition", condition)?;
                map.serialize_entry("body", body)?;
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                map.serialize_entry("tag", "if")?;
                map.serialize_entry("condition", condition)?;
                map.serialize_entry("then", then_branch)?;
                map.serialize_entry("else", else_branch)?;
            }
            ExprKind::Unary { op, operand } => {
                map.serialize_entry("tag", "unary")?;
                map.serialize_entry("op", op.as_str())?;
                map.serialize_entry("operand", operand)?;
            }
            ExprKind::Binary { op, left, right } => {
                map.serialize_entry("tag", "binary")?;
                map.serialize_entry("op", op.as_str())?;
                map.serialize_entry("left", left)?;
                map.serialize_entry("right", right)?;
            }
            ExprKind::Call {
                function,
                arguments,
            } => {
                map.serialize_entry("tag", "call")?;
                map.serialize_entry("function", function)?;
                map.serialize_entry("arguments", arguments)?;
            }
        }
        map.end()
    }
}
struct FunctionWire<'a>(usize, &'a Function);
impl Serialize for FunctionWire<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(5))?;
        map.serialize_entry("id", &self.0)?;
        map.serialize_entry("name", &self.1.name)?;
        map.serialize_entry("params", &self.1.params)?;
        map.serialize_entry("result", &self.1.result)?;
        map.serialize_entry("body", &self.1.body)?;
        map.end()
    }
}
struct Functions<'a>(&'a [Function]);
impl Serialize for Functions<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for (id, function) in self.0.iter().enumerate() {
            seq.serialize_element(&FunctionWire(id, function))?;
        }
        seq.end()
    }
}
struct ProgramWire<'a>(&'a Program, usize);
impl Serialize for ProgramWire<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(4))?;
        map.serialize_entry("schema", "apl-core-v2")?;
        map.serialize_entry("semantic_revision", super::FLAT_PRODUCTS_SEMANTIC_REVISION)?;
        map.serialize_entry("entry", &self.1)?;
        map.serialize_entry("functions", &Functions(&self.0.functions))?;
        map.end()
    }
}
pub(super) fn export(
    program: &Program,
    entry: usize,
    limit: usize,
) -> Result<serde_json::Value, OutputError> {
    let mut buffer = Buffer::new(Some(limit), "exported v2 JSON exceeds 1048576 bytes");
    if let Err(error) = serde_json::to_writer(&mut buffer, &ProgramWire(program, entry))
        && !buffer.exhausted()
    {
        return Err(OutputError::Infrastructure(error.to_string()));
    }
    drop(buffer.finish()?);
    // Materialize only after bounded serialization has established the exact wire size.
    serde_json::to_value(ProgramWire(program, entry))
        .map_err(|e| OutputError::Infrastructure(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_compact_document_size_bounds_emission_before_dom_construction() {
        let program = crate::compile("fn main()->i64{let p=(42,true,());p.0}").unwrap();
        let expected = serde_json::to_string(&ProgramWire(&program, 0)).unwrap();
        for limit in [expected.len() - 1, expected.len(), expected.len() + 1] {
            let emitted = export(&program, 0, limit);
            if limit < expected.len() {
                assert!(matches!(emitted, Err(OutputError::ResourceLimit(_))));
            } else {
                let emitted = emitted.unwrap();
                assert_eq!(emitted.to_string().len(), expected.len());
                assert_eq!(
                    emitted,
                    serde_json::from_str::<serde_json::Value>(&expected).unwrap()
                );
            }
        }
    }
}
