//! Strict JSON adapter. Imported type labels are independently checked.
use crate::{
    MAX_DEPTH, MAX_SOURCE_BYTES,
    diagnostic::Span,
    eval::{EvalError, Value as Scalar},
    syntax,
    types::{BinaryOp, Expr, ExprKind, Function, Program, Type, UnaryOp},
};
use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Value, json};
use std::{collections::HashSet, fmt};

pub const SEMANTIC_REVISION: &str = "m1-2026-11-16";
pub const LOCAL_STATE_SEMANTIC_REVISION: &str = "local-state-2026-11-17";
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportError {
    Invalid(String),
    ResourceLimit(String),
}
impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(s) | Self::ResourceLimit(s) => f.write_str(s),
        }
    }
}
impl std::error::Error for ImportError {}
pub struct Artifact {
    pub program: Program,
    pub entry: usize,
}

// serde_json::Value keeps the final duplicate member; reject duplicates first.
struct StrictValue(Value);
impl<'de> Deserialize<'de> for StrictValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct StrictVisitor;
        impl<'de> Visitor<'de> for StrictVisitor {
            type Value = StrictValue;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("JSON value without duplicate members")
            }
            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Self::Value, E> {
                Ok(StrictValue(v.into()))
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Self::Value, E> {
                Ok(StrictValue(v.into()))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Self::Value, E> {
                Ok(StrictValue(v.into()))
            }
            fn visit_f64<E: de::Error>(self, v: f64) -> Result<Self::Value, E> {
                serde_json::Number::from_f64(v)
                    .map(|n| StrictValue(Value::Number(n)))
                    .ok_or_else(|| E::custom("invalid JSON number"))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
                Ok(StrictValue(v.into()))
            }
            fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
                Ok(StrictValue(v.into()))
            }
            fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
                Ok(StrictValue(Value::Null))
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                let mut values = Vec::new();
                while let Some(StrictValue(value)) = seq.next_element()? {
                    values.push(value);
                }
                Ok(StrictValue(Value::Array(values)))
            }
            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                let mut values = Map::new();
                while let Some(key) = map.next_key::<String>()? {
                    if values.contains_key(&key) {
                        return Err(de::Error::custom(format!(
                            "duplicate object member `{key}`"
                        )));
                    }
                    let StrictValue(value) = map.next_value()?;
                    values.insert(key, value);
                }
                Ok(StrictValue(Value::Object(values)))
            }
        }
        deserializer.deserialize_any(StrictVisitor)
    }
}
fn invalid(message: impl Into<String>) -> ImportError {
    ImportError::Invalid(message.into())
}
fn object<'a>(value: &'a Value, fields: &[&str]) -> Result<&'a Map<String, Value>, ImportError> {
    let object = value
        .as_object()
        .ok_or_else(|| invalid("expected object"))?;
    if object.len() != fields.len() || fields.iter().any(|key| !object.contains_key(*key)) {
        return Err(invalid(format!(
            "expected exactly members {}",
            fields.join(", ")
        )));
    }
    Ok(object)
}
fn string(value: &Value) -> Result<&str, ImportError> {
    value.as_str().ok_or_else(|| invalid("expected string"))
}
fn natural(value: &Value) -> Result<usize, ImportError> {
    value
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| invalid("expected natural-number index"))
}
fn ty(value: &Value) -> Result<Type, ImportError> {
    Type::from_name(string(value)?).ok_or_else(|| invalid("unknown scalar type"))
}
fn array(value: &Value) -> Result<&Vec<Value>, ImportError> {
    value.as_array().ok_or_else(|| invalid("expected array"))
}

pub fn import(text: &str) -> Result<Artifact, ImportError> {
    if text.len() > MAX_SOURCE_BYTES {
        return Err(ImportError::ResourceLimit(
            "JSON exceeds 1048576 bytes".into(),
        ));
    }
    let StrictValue(value) = serde_json::from_str(text).map_err(|error| {
        let message = error.to_string();
        if error.is_syntax() && message.starts_with("recursion limit exceeded at line ") {
            ImportError::ResourceLimit(message)
        } else {
            invalid(message)
        }
    })?;
    let schema = value
        .get("schema")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("missing schema"))?;
    let fields: &[&str] = match schema {
        "apl-core-v0" | "apl-core-v1" => &["schema", "semantic_revision", "functions", "entry"],
        "apl-expr-v0" | "apl-expr-v1" => &["schema", "semantic_revision", "expression"],
        _ => return Err(invalid("unsupported schema")),
    };
    let root = object(&value, fields)?;
    let allow_local_state = matches!(schema, "apl-core-v1" | "apl-expr-v1");
    let revision = if allow_local_state {
        LOCAL_STATE_SEMANTIC_REVISION
    } else {
        SEMANTIC_REVISION
    };
    if string(&root["semantic_revision"])? != revision {
        return Err(invalid("unsupported semantic revision"));
    }
    let mut importer = Importer {
        signatures: Vec::new(),
        next_id: 0,
        allow_calls: matches!(schema, "apl-core-v0" | "apl-core-v1"),
        allow_local_state,
    };
    if !importer.allow_calls {
        let body = importer.expr(&root["expression"], &mut Vec::new(), 0)?;
        return Ok(Artifact {
            program: Program {
                sources: Default::default(),
                contracts: None,
                functions: vec![Function {
                    name: "expression".into(),
                    params: Vec::new(),
                    result: body.ty,
                    body,
                    span: Span::default(),
                }],
            },
            entry: 0,
        });
    }
    let functions = array(&root["functions"])?;
    let mut names = HashSet::new();
    for (id, function) in functions.iter().enumerate() {
        let function = object(function, &["id", "name", "params", "result", "body"])?;
        if natural(&function["id"])? != id {
            return Err(invalid("function ID must equal table index"));
        }
        let name = string(&function["name"])?;
        if !syntax::identifier(name) || !names.insert(name.to_owned()) {
            return Err(invalid("invalid or duplicate function name"));
        }
        let params = array(&function["params"])?
            .iter()
            .map(ty)
            .collect::<Result<Vec<_>, _>>()?;
        importer.signatures.push((params, ty(&function["result"])?));
    }
    let entry = natural(&root["entry"])?;
    let entry_signature = importer
        .signatures
        .get(entry)
        .ok_or_else(|| invalid("entry function does not exist"))?;
    if !entry_signature.0.is_empty() || entry_signature.1 != Type::I64 {
        return Err(invalid("entry must be nullary with i64 result"));
    }
    let mut checked = Vec::new();
    for (id, function) in functions.iter().enumerate() {
        let (params, result) = importer.signatures[id].clone();
        let mut env = params
            .iter()
            .map(|ty| Binding {
                ty: *ty,
                mutable: false,
            })
            .collect();
        let body = importer.expr(&function["body"], &mut env, 0)?;
        if body.ty != result {
            return Err(invalid("function result type mismatch"));
        }
        checked.push(Function {
            name: string(&function["name"])?.into(),
            params,
            result,
            body,
            span: Span::default(),
        });
    }
    Ok(Artifact {
        program: Program {
            functions: checked,
            sources: Default::default(),
            contracts: None,
        },
        entry,
    })
}
struct Importer {
    signatures: Vec<(Vec<Type>, Type)>,
    next_id: usize,
    allow_calls: bool,
    allow_local_state: bool,
}
struct Binding {
    ty: Type,
    mutable: bool,
}
fn local_position(length: usize, index: usize) -> Result<usize, ImportError> {
    length
        .checked_sub(
            index
                .checked_add(1)
                .ok_or_else(|| invalid("local index out of range"))?,
        )
        .ok_or_else(|| invalid("unbound local index"))
}
impl Importer {
    fn expr(
        &mut self,
        value: &Value,
        env: &mut Vec<Binding>,
        nesting: usize,
    ) -> Result<Expr, ImportError> {
        if nesting >= MAX_DEPTH {
            return Err(ImportError::ResourceLimit(
                "IR expression depth limit exceeded".into(),
            ));
        }
        let tag = value
            .get("tag")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("missing expression tag"))?;
        let fields: &[&str] = match tag {
            "integer" | "boolean" => &["tag", "ty", "value"],
            "unit" => &["tag", "ty"],
            "local" => &["tag", "ty", "index"],
            "let" => &["tag", "ty", "value", "body"],
            "let_mut" if self.allow_local_state => &["tag", "ty", "value", "body"],
            "assign" if self.allow_local_state => &["tag", "ty", "index", "value"],
            "while" if self.allow_local_state => &["tag", "ty", "condition", "body"],
            "if" => &["tag", "ty", "condition", "then", "else"],
            "unary" => &["tag", "ty", "op", "operand"],
            "binary" => &["tag", "ty", "op", "left", "right"],
            "call" => &["tag", "ty", "function", "arguments"],
            _ => return Err(invalid("unknown expression constructor")),
        };
        let obj = object(value, fields)?;
        let annotation = ty(&obj["ty"])?;
        let next = nesting + 1;
        let (inferred, kind, depth) = match tag {
            "integer" => {
                let text = string(&obj["value"])?;
                let value = text
                    .parse::<i64>()
                    .map_err(|_| invalid("integer outside i64 range"))?;
                if value.to_string() != text {
                    return Err(invalid("integer is not canonical decimal"));
                }
                (Type::I64, ExprKind::Integer(value), 1)
            }
            "boolean" => (
                Type::Bool,
                ExprKind::Boolean(
                    obj["value"]
                        .as_bool()
                        .ok_or_else(|| invalid("expected boolean value"))?,
                ),
                1,
            ),
            "unit" => (Type::Unit, ExprKind::Unit, 1),
            "local" => {
                let index = natural(&obj["index"])?;
                let position = local_position(env.len(), index)?;
                (env[position].ty, ExprKind::Local(index), 1)
            }
            "let" | "let_mut" => {
                let value = self.expr(&obj["value"], env, next)?;
                env.push(Binding {
                    ty: value.ty,
                    mutable: tag == "let_mut",
                });
                let body = self.expr(&obj["body"], env, next)?;
                env.pop();
                let depth = value.depth.max(body.depth) + 1;
                let ty = body.ty;
                let kind = if tag == "let_mut" {
                    ExprKind::LetMut {
                        value: Box::new(value),
                        body: Box::new(body),
                    }
                } else {
                    ExprKind::Let {
                        value: Box::new(value),
                        body: Box::new(body),
                    }
                };
                (ty, kind, depth)
            }
            "assign" => {
                let index = natural(&obj["index"])?;
                let position = local_position(env.len(), index)?;
                if !env[position].mutable {
                    return Err(invalid("assignment target is immutable"));
                }
                let expected = env[position].ty;
                let value = self.expr(&obj["value"], env, next)?;
                if value.ty != expected {
                    return Err(invalid("assignment value type mismatch"));
                }
                let depth = value.depth + 1;
                (
                    Type::Unit,
                    ExprKind::Assign {
                        index,
                        value: Box::new(value),
                    },
                    depth,
                )
            }
            "while" => {
                let condition = self.expr(&obj["condition"], env, next)?;
                let body = self.expr(&obj["body"], env, next)?;
                if condition.ty != Type::Bool || body.ty != Type::Unit {
                    return Err(invalid("while requires bool condition and unit body"));
                }
                let depth = condition.depth.max(body.depth) + 1;
                (
                    Type::Unit,
                    ExprKind::While {
                        condition: Box::new(condition),
                        body: Box::new(body),
                    },
                    depth,
                )
            }
            "if" => {
                let condition = self.expr(&obj["condition"], env, next)?;
                let then_branch = self.expr(&obj["then"], env, next)?;
                let else_branch = self.expr(&obj["else"], env, next)?;
                if condition.ty != Type::Bool || then_branch.ty != else_branch.ty {
                    return Err(invalid("if type mismatch"));
                }
                let depth = 1 + condition
                    .depth
                    .max(then_branch.depth)
                    .max(else_branch.depth);
                (
                    then_branch.ty,
                    ExprKind::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    depth,
                )
            }
            "unary" => {
                let op = match string(&obj["op"])? {
                    "neg" => UnaryOp::Neg,
                    "not" => UnaryOp::Not,
                    _ => return Err(invalid("unknown unary operator")),
                };
                let operand = self.expr(&obj["operand"], env, next)?;
                if operand.ty != op.input() {
                    return Err(invalid("unary operand type mismatch"));
                }
                let depth = operand.depth + 1;
                (
                    op.input(),
                    ExprKind::Unary {
                        op,
                        operand: Box::new(operand),
                    },
                    depth,
                )
            }
            "binary" => {
                let op = BinaryOp::from_name(string(&obj["op"])?)
                    .ok_or_else(|| invalid("unknown binary operator"))?;
                let left = self.expr(&obj["left"], env, next)?;
                let right = self.expr(&obj["right"], env, next)?;
                let result = op
                    .result(left.ty, right.ty)
                    .ok_or_else(|| invalid("binary operand type mismatch"))?;
                let depth = left.depth.max(right.depth) + 1;
                (
                    result,
                    ExprKind::Binary {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    depth,
                )
            }
            "call" => {
                if !self.allow_calls {
                    return Err(invalid("calls are outside expression fixture scope"));
                }
                let function = natural(&obj["function"])?;
                let (params, result) = self
                    .signatures
                    .get(function)
                    .cloned()
                    .ok_or_else(|| invalid("unknown function ID"))?;
                let arguments = array(&obj["arguments"])?;
                if arguments.len() != params.len() {
                    return Err(invalid("call arity mismatch"));
                }
                let mut checked = Vec::new();
                let mut depth = 1;
                for (argument, expected) in arguments.iter().zip(params) {
                    let argument = self.expr(argument, env, next)?;
                    if argument.ty != expected {
                        return Err(invalid("call argument type mismatch"));
                    }
                    depth = depth.max(argument.depth + 1);
                    checked.push(argument);
                }
                (
                    result,
                    ExprKind::Call {
                        function,
                        arguments: checked,
                    },
                    depth,
                )
            }
            _ => unreachable!(),
        };
        if annotation != inferred {
            return Err(invalid("expression ty does not match inferred type"));
        }
        let id = self.next_id;
        self.next_id += 1;
        Ok(Expr {
            ty: inferred,
            kind,
            id,
            span: Span::default(),
            depth,
        })
    }
}

pub fn export(program: &Program, entry: usize) -> Value {
    let functions: Vec<Value> = program.functions.iter().enumerate().map(|(id, function)| json!({
        "id": id, "name": function.name, "params": function.params.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        "result": function.result.as_str(), "body": export_expr(&function.body)
    })).collect();
    let schema = if program.has_local_state() {
        "apl-core-v1"
    } else {
        "apl-core-v0"
    };
    json!({"schema":schema, "semantic_revision":program.semantic_revision(), "functions":functions, "entry":entry})
}
fn export_expr(expr: &Expr) -> Value {
    let mut value = match &expr.kind {
        ExprKind::Integer(n) => json!({"tag":"integer", "value":n.to_string()}),
        ExprKind::Boolean(b) => json!({"tag":"boolean", "value":b}),
        ExprKind::Unit => json!({"tag":"unit"}),
        ExprKind::Local(index) => json!({"tag":"local", "index":index}),
        ExprKind::Let { value, body } => {
            json!({"tag":"let", "value":export_expr(value), "body":export_expr(body)})
        }
        ExprKind::LetMut { value, body } => {
            json!({"tag":"let_mut", "value":export_expr(value), "body":export_expr(body)})
        }
        ExprKind::Assign { index, value } => {
            json!({"tag":"assign", "index":index, "value":export_expr(value)})
        }
        ExprKind::While { condition, body } => {
            json!({"tag":"while", "condition":export_expr(condition), "body":export_expr(body)})
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            json!({"tag":"if", "condition":export_expr(condition), "then":export_expr(then_branch), "else":export_expr(else_branch)})
        }
        ExprKind::Unary { op, operand } => {
            json!({"tag":"unary", "op":op.as_str(), "operand":export_expr(operand)})
        }
        ExprKind::Binary { op, left, right } => {
            json!({"tag":"binary", "op":op.as_str(), "left":export_expr(left), "right":export_expr(right)})
        }
        ExprKind::Call {
            function,
            arguments,
        } => {
            json!({"tag":"call", "function":function, "arguments":arguments.iter().map(export_expr).collect::<Vec<_>>()})
        }
    };
    value["ty"] = expr.ty.as_str().into();
    value
}
pub fn outcome(result: &Result<Scalar, EvalError>) -> Value {
    match result {
        Ok(value) => {
            let repr = match value {
                Scalar::Integer(n) => json!(n.to_string()),
                Scalar::Boolean(b) => json!(b),
                Scalar::Unit => Value::Null,
            };
            json!({"outcome":"value", "type":value.ty().as_str(), "value":repr})
        }
        Err(EvalError::Trap { kind, .. }) => json!({"outcome":"trap", "trap":kind.as_str()}),
        Err(EvalError::ResourceLimit { .. }) => json!({"outcome":"resource_limit"}),
        Err(EvalError::InvalidIr) => json!({"outcome":"invalid_ir"}),
    }
}
