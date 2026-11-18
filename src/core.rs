//! Strict JSON adapter. Imported type labels are independently checked.
mod wire;
use crate::{
    MAX_DEPTH, MAX_SOURCE_BYTES,
    diagnostic::Span,
    eval::{EvalError, Value as Scalar},
    syntax,
    types::{
        BinaryOp, Expr, ExprKind, Function, IrRevision, MemoryExpr, Program, ResourceMode, Type,
        UnaryOp, ViewMode,
    },
    word::{ConvertMode, WordValue, WordWidth},
};
use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Value, json};
use std::{collections::HashSet, fmt};

pub const FLAT_PRODUCTS_SEMANTIC_REVISION: &str = "flat-products-2026-11-17";
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
pub(crate) struct StrictValue(pub(crate) Value);
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
pub(crate) fn object<'a>(
    value: &'a Value,
    fields: &[&str],
) -> Result<&'a Map<String, Value>, ImportError> {
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
pub(crate) fn string(value: &Value) -> Result<&str, ImportError> {
    value.as_str().ok_or_else(|| invalid("expected string"))
}
pub(crate) fn natural(value: &Value) -> Result<usize, ImportError> {
    value
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| invalid("expected natural-number index"))
}
pub(crate) fn ty_words(value: &Value, products: bool, words: bool) -> Result<Type, ImportError> {
    if let Some(name) = value.as_str() {
        return Type::from_name(name)
            .filter(|t| words || !t.contains_words())
            .ok_or_else(|| invalid("unknown scalar type"));
    }
    if !products {
        return Err(invalid("tuple types require v2"));
    }
    let fields = array(&object(value, &["tuple"])?["tuple"])?;
    if !(1..=crate::types::MAX_TUPLE_FIELDS).contains(&fields.len()) {
        return Err(invalid("tuple requires 1..8 scalar fields"));
    }
    let fields = fields
        .iter()
        .map(|v| {
            Type::from_name(string(v)?)
                .filter(|t| words || !t.contains_words())
                .and_then(Type::scalar)
                .ok_or_else(|| invalid("tuple field must be a scalar type"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Tuple(
        crate::types::TupleShape::new(&fields).map_err(|e| invalid(e.to_string()))?,
    ))
}
pub(crate) fn word_payload(width: &Value, value: &Value) -> Result<WordValue, ImportError> {
    let width = width
        .as_u64()
        .and_then(WordWidth::from_bits)
        .ok_or_else(|| invalid("invalid word width"))?;
    let text = string(value)?;
    let n = text
        .parse::<u64>()
        .map_err(|_| invalid("word literal is outside uint64"))?;
    if n.to_string() != text {
        return Err(invalid("noncanonical word literal"));
    }
    WordValue::new(width, n).ok_or_else(|| invalid("word literal is outside declared width"))
}
pub(crate) fn array(value: &Value) -> Result<&Vec<Value>, ImportError> {
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
        "anl-core-v3" | "anl-core-v4" => &[
            "schema",
            "semantic_revision",
            "allocation_profile",
            "functions",
            "entry",
        ],
        "apl-core-v0" | "apl-core-v1" | "apl-core-v2" => {
            &["schema", "semantic_revision", "functions", "entry"]
        }
        "apl-expr-v0" | "apl-expr-v1" | "apl-expr-v2" => {
            &["schema", "semantic_revision", "expression"]
        }
        _ => return Err(invalid("unsupported schema")),
    };
    let root = object(&value, fields)?;
    let allow_words = schema == "anl-core-v4";
    let allow_memory = allow_words || schema == "anl-core-v3";
    let allocation_profile = if allow_memory {
        Some(profile(&root["allocation_profile"])?)
    } else {
        None
    };
    let allow_products = allow_memory || matches!(schema, "apl-core-v2" | "apl-expr-v2");
    let allow_local_state = allow_products || matches!(schema, "apl-core-v1" | "apl-expr-v1");
    let revision = if allow_words {
        "anl-words-v1"
    } else if allow_memory {
        crate::memory::SEMANTIC_REVISION
    } else if allow_products {
        FLAT_PRODUCTS_SEMANTIC_REVISION
    } else if allow_local_state {
        LOCAL_STATE_SEMANTIC_REVISION
    } else {
        SEMANTIC_REVISION
    };
    if string(&root["semantic_revision"])? != revision {
        return Err(invalid("unsupported semantic revision"));
    }
    let mut importer = Importer {
        strict_indices: false,
        views: Vec::new(),
        resources: Vec::new(),
        next_site: 0,
        allow_memory,
        allow_words,
        signatures: Vec::new(),
        next_id: 0,
        allow_calls: allow_memory
            || matches!(schema, "apl-core-v0" | "apl-core-v1" | "apl-core-v2"),
        allow_local_state,
        allow_products,
    };
    if !importer.allow_calls {
        let body = importer.expr(&root["expression"], &mut Vec::new(), 0)?;
        return Ok(Artifact {
            program: Program {
                retained_revision: None,
                allocation_profile: None,
                sources: Default::default(),
                contracts: None,
                functions: vec![Function {
                    view: None,
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
        let fields: &[&str] = if allow_memory {
            &["id", "name", "view", "params", "result", "body"]
        } else {
            &["id", "name", "params", "result", "body"]
        };
        let function = object(function, fields)?;
        importer
            .views
            .push(if allow_memory && !function["view"].is_null() {
                Some(view(&function["view"])?)
            } else {
                None
            });
        if natural(&function["id"])? != id {
            return Err(invalid("function ID must equal table index"));
        }
        let name = string(&function["name"])?;
        if !syntax::identifier(name) || !names.insert(name.to_owned()) {
            return Err(invalid("invalid or duplicate function name"));
        }
        let params = array(&function["params"])?
            .iter()
            .map(|v| ty_words(v, allow_products, allow_words))
            .collect::<Result<Vec<_>, _>>()?;
        importer.signatures.push((
            params,
            ty_words(&function["result"], allow_products, allow_words)?,
        ));
    }
    let entry = natural(&root["entry"])?;
    let entry_signature = importer
        .signatures
        .get(entry)
        .ok_or_else(|| invalid("entry function does not exist"))?;
    if importer.views[entry].is_some()
        || !entry_signature.0.is_empty()
        || entry_signature.1 != Type::I64
    {
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
        importer.next_site = 0;
        importer.resources = importer.views[id]
            .into_iter()
            .map(ResourceMode::from)
            .collect();
        let body = importer.expr(&function["body"], &mut env, 0)?;
        if body.ty != result {
            return Err(invalid("function result type mismatch"));
        }
        checked.push(Function {
            view: importer.views[id],
            name: string(&function["name"])?.into(),
            params,
            result,
            body,
            span: Span::default(),
        });
    }
    Ok(Artifact {
        program: Program {
            retained_revision: allow_words.then_some(IrRevision::WordsV4),
            allocation_profile,
            functions: checked,
            sources: Default::default(),
            contracts: None,
        },
        entry,
    })
}
pub(crate) fn check_boot_body(
    value: &Value,
    params: &[Type],
    result: Type,
    signatures: &[(Vec<Type>, Type)],
) -> Result<Expr, ImportError> {
    let mut importer = Importer {
        views: vec![None; signatures.len()],
        resources: Vec::new(),
        next_site: 0,
        allow_memory: false,
        allow_words: true,
        signatures: signatures.to_vec(),
        next_id: 0,
        allow_calls: true,
        allow_local_state: true,
        allow_products: true,
        strict_indices: true,
    };
    let mut env = params
        .iter()
        .map(|&ty| Binding { ty, mutable: false })
        .collect();
    let body = importer.expr(value, &mut env, 0)?;
    if body.ty != result {
        return Err(invalid("function result type mismatch"));
    }
    Ok(body)
}

pub(crate) fn profile(value: &Value) -> Result<crate::memory::AllocationProfile, ImportError> {
    let o = object(
        value,
        &[
            "abi",
            "char_bits",
            "i64_bytes",
            "i64_align",
            "size_bits",
            "ptrdiff_bits",
        ],
    )?;
    if string(&o["abi"])? != "anl-buffer-c11-v1"
        || natural(&o["char_bits"])? != 8
        || natural(&o["i64_bytes"])? != 8
    {
        return Err(invalid("unsupported allocation profile"));
    }
    let n = |key: &str| -> Result<u32, ImportError> {
        u32::try_from(natural(&o[key])?).map_err(|_| invalid("profile number out of range"))
    };
    let p = crate::memory::AllocationProfile {
        i64_align: n("i64_align")?,
        size_bits: n("size_bits")?,
        ptrdiff_bits: n("ptrdiff_bits")?,
    };
    if !p.valid() {
        return Err(invalid("unsupported allocation profile"));
    }
    Ok(p)
}
pub(crate) fn view(value: &Value) -> Result<ViewMode, ImportError> {
    ViewMode::from_name(string(value)?).ok_or_else(|| invalid("unknown view mode"))
}
struct Importer {
    strict_indices: bool,
    views: Vec<Option<ViewMode>>,
    resources: Vec<ResourceMode>,
    next_site: usize,
    allow_memory: bool,
    allow_words: bool,
    signatures: Vec<(Vec<Type>, Type)>,
    next_id: usize,
    allow_calls: bool,
    allow_local_state: bool,
    allow_products: bool,
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
    fn index(&self, value: &Value, bound: usize) -> Result<usize, ImportError> {
        if self.strict_indices {
            let n = value
                .as_u64()
                .ok_or_else(|| invalid("expected natural-number index"))?;
            if n >= bound as u64 {
                return Err(invalid("index out of range"));
            }
            usize::try_from(n).map_err(|_| invalid("index out of range"))
        } else {
            natural(value)
        }
    }

    fn memory(
        &mut self,
        tag: &str,
        obj: &Map<String, Value>,
        env: &mut Vec<Binding>,
        next: usize,
    ) -> Result<MemoryExpr, ImportError> {
        if tag == "heap" {
            let site = natural(&obj["site"])?;
            if site != self.next_site {
                return Err(invalid("noncanonical heap site"));
            }
            self.next_site += 1;
            let length = self.expr(&obj["length"], env, next)?;
            let initial = self.expr(&obj["initial"], env, next)?;
            if length.ty != Type::I64 || initial.ty != Type::I64 {
                return Err(invalid("heap length/initializer must be i64"));
            }
            self.resources.push(ResourceMode::Owner);
            let success = self.expr(&obj["success"], env, next);
            self.resources.pop();
            let success = success?;
            let failure = self.expr(&obj["failure"], env, next)?;
            if success.ty != failure.ty {
                return Err(invalid("heap branch type mismatch"));
            }
            return Ok(MemoryExpr::Heap {
                site,
                length: Box::new(length),
                initial: Box::new(initial),
                success: Box::new(success),
                failure: Box::new(failure),
            });
        }
        let resource = natural(&obj["resource"])?;
        let position = local_position(self.resources.len(), resource)?;
        let permission = self.resources[position];
        if tag == "buffer_length" {
            return Ok(MemoryExpr::Length { resource });
        }
        if tag == "call_view" {
            let mode = view(&obj["mode"])?;
            let function = natural(&obj["function"])?;
            let (params, _) = self
                .signatures
                .get(function)
                .ok_or_else(|| invalid("unknown view callee"))?
                .clone();
            if self.views[function] != Some(mode) || !permission.lends(mode) {
                return Err(invalid("invalid view permission"));
            }
            let args = array(&obj["arguments"])?;
            if args.len() != params.len() {
                return Err(invalid("view call arity mismatch"));
            }
            let mut arguments = Vec::new();
            for (a, t) in args.iter().zip(params) {
                let a = self.expr(a, env, next)?;
                if a.ty != t {
                    return Err(invalid("view argument type mismatch"));
                }
                arguments.push(a);
            }
            return Ok(MemoryExpr::CallView {
                function,
                resource,
                mode,
                arguments,
            });
        }
        let index = self.expr(&obj["index"], env, next)?;
        if index.ty != Type::I64 {
            return Err(invalid("buffer index must be i64"));
        }
        if tag == "buffer_read" {
            return Ok(MemoryExpr::Read {
                resource,
                index: Box::new(index),
            });
        }
        if !permission.writable() {
            return Err(invalid("cannot write a read view"));
        }
        let value = self.expr(&obj["value"], env, next)?;
        if value.ty != Type::I64 {
            return Err(invalid("buffer value must be i64"));
        }
        Ok(MemoryExpr::Write {
            resource,
            index: Box::new(index),
            value: Box::new(value),
        })
    }
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
            "word" if self.allow_words => &["tag", "ty", "width", "value"],
            "convert" if self.allow_words => &["tag", "ty", "mode", "target", "operand"],
            "heap" if self.allow_memory => &[
                "tag", "ty", "site", "length", "initial", "success", "failure",
            ],
            "buffer_length" if self.allow_memory => &["tag", "ty", "resource"],
            "buffer_read" if self.allow_memory => &["tag", "ty", "resource", "index"],
            "buffer_write" if self.allow_memory => &["tag", "ty", "resource", "index", "value"],
            "call_view" if self.allow_memory => {
                &["tag", "ty", "function", "resource", "mode", "arguments"]
            }
            "tuple" if self.allow_products => &["tag", "fields", "ty"],
            "project" if self.allow_products => &["tag", "value", "index", "ty"],
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
        let annotation = ty_words(&obj["ty"], self.allow_products, self.allow_words)?;
        let next = nesting + 1;
        let (inferred, kind, depth) = match tag {
            "word" => {
                let value = word_payload(&obj["width"], &obj["value"])?;
                (Type::Word(value.width()), ExprKind::Word(value), 1)
            }
            "convert" => {
                let mode = ConvertMode::from_name(string(&obj["mode"])?)
                    .ok_or_else(|| invalid("unknown conversion mode"))?;
                let target = ty_words(&obj["target"], false, true)?;
                let operand = self.expr(&obj["operand"], env, next)?;
                let ty = mode
                    .result(operand.ty, target)
                    .ok_or_else(|| invalid("invalid conversion signature"))?;
                let depth = operand.depth + 1;
                (
                    ty,
                    ExprKind::Convert {
                        mode,
                        target,
                        operand: Box::new(operand),
                    },
                    depth,
                )
            }

            "heap" | "buffer_length" | "buffer_read" | "buffer_write" | "call_view" => {
                let kind = self.memory(tag, obj, env, next)?;
                let ty = match &kind {
                    MemoryExpr::Heap { success, .. } => success.ty,
                    MemoryExpr::Write { .. } => Type::Unit,
                    MemoryExpr::CallView { function, .. } => self.signatures[*function].1,
                    _ => Type::I64,
                };
                let depth = 1 + kind.children().iter().map(|e| e.depth).max().unwrap_or(0);
                (ty, ExprKind::Memory(Box::new(kind)), depth)
            }
            "tuple" => {
                let fields = array(&obj["fields"])?;
                if !(1..=crate::types::MAX_TUPLE_FIELDS).contains(&fields.len()) {
                    return Err(invalid("tuple requires 1..8 scalar fields"));
                }
                let mut checked = Vec::new();
                let mut shape = Vec::new();
                let mut depth = 1;
                for field in fields {
                    let field = self.expr(field, env, next)?;
                    shape.push(
                        field
                            .ty
                            .scalar()
                            .ok_or_else(|| invalid("nested tuples are unsupported"))?,
                    );
                    depth = depth.max(field.depth + 1);
                    checked.push(field);
                }
                (
                    Type::Tuple(
                        crate::types::TupleShape::new(&shape)
                            .map_err(|e| invalid(e.to_string()))?,
                    ),
                    ExprKind::Tuple(checked),
                    depth,
                )
            }
            "project" => {
                let index = self.index(&obj["index"], crate::types::MAX_TUPLE_FIELDS)?;
                if index >= crate::types::MAX_TUPLE_FIELDS {
                    return Err(invalid("projection index outside 0..7"));
                }
                let value = self.expr(&obj["value"], env, next)?;
                let Type::Tuple(shape) = value.ty else {
                    return Err(invalid("projection requires tuple"));
                };
                let ty = shape
                    .fields()
                    .get(index)
                    .ok_or_else(|| invalid("projection index out of bounds"))?
                    .as_type();
                let depth = value.depth + 1;
                (
                    ty,
                    ExprKind::Project {
                        value: Box::new(value),
                        index,
                    },
                    depth,
                )
            }
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
                let index = self.index(&obj["index"], env.len())?;
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
                let index = self.index(&obj["index"], env.len())?;
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
                    "bit_not" if self.allow_words => UnaryOp::BitNot,
                    _ => return Err(invalid("unknown unary operator")),
                };
                let operand = self.expr(&obj["operand"], env, next)?;
                let ty = op
                    .result(operand.ty)
                    .ok_or_else(|| invalid("unary operand type mismatch"))?;
                let depth = operand.depth + 1;
                (
                    ty,
                    ExprKind::Unary {
                        op,
                        operand: Box::new(operand),
                    },
                    depth,
                )
            }
            "binary" => {
                let op = BinaryOp::from_name(string(&obj["op"])?)
                    .filter(|op| self.allow_words || !op.is_word())
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
                let id = self.index(&obj["function"], self.signatures.len())?;
                if self.views.get(id).is_some_and(Option::is_some) {
                    return Err(invalid("ordinary call targets a view function"));
                }
                if !self.allow_calls {
                    return Err(invalid("calls are outside expression fixture scope"));
                }
                let function = id;
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

/// Export the lowest applicable schema. This host API is fallible: v2 emission
/// is bounded before materializing the JSON value; scalar wire bytes are unchanged.
pub fn export(program: &Program, entry: usize) -> Result<Value, crate::bounded::OutputError> {
    if program.effective_revision() == IrRevision::WordsV4
        || program.has_memory()
        || program.has_flat_products()
    {
        return wire::export(program, entry, MAX_SOURCE_BYTES);
    }
    let functions: Vec<Value> = program.functions.iter().enumerate().map(|(id, function)| json!({
        "id": id, "name": function.name, "params": function.params.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        "result": function.result.as_str(), "body": export_expr(&function.body)
    })).collect();
    let schema = if program.has_local_state() {
        "apl-core-v1"
    } else {
        "apl-core-v0"
    };
    Ok(
        json!({"schema":schema, "semantic_revision":program.semantic_revision(), "functions":functions, "entry":entry}),
    )
}
fn export_expr(expr: &Expr) -> Value {
    let mut value = match &expr.kind {
        ExprKind::Word(_)
        | ExprKind::Convert { .. }
        | ExprKind::Memory(_)
        | ExprKind::Tuple(_)
        | ExprKind::Project { .. } => {
            unreachable!("aggregate export uses bounded serializer")
        }
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
                Scalar::Word(w) => json!(w.value().to_string()),
                Scalar::Integer(n) => json!(n.to_string()),
                Scalar::Boolean(b) => json!(b),
                Scalar::Unit => Value::Null,
                Scalar::Tuple(tuple) => Value::Array(
                    tuple
                        .fields()
                        .iter()
                        .map(|field| match field {
                            crate::eval::ScalarValue::Word(w) => json!(w.value().to_string()),
                            crate::eval::ScalarValue::Integer(n) => json!(n.to_string()),
                            crate::eval::ScalarValue::Boolean(b) => json!(b),
                            crate::eval::ScalarValue::Unit => Value::Null,
                        })
                        .collect(),
                ),
            };
            json!({"outcome":"value", "type":value.ty(), "value":repr})
        }
        Err(EvalError::Trap { kind, .. }) => json!({"outcome":"trap", "trap":kind.as_str()}),
        Err(EvalError::ResourceLimit { .. }) => json!({"outcome":"resource_limit"}),
        Err(EvalError::Infrastructure(reason)) => {
            json!({"outcome":"infrastructure_error","reason":reason})
        }
        Err(EvalError::InvalidIr) => json!({"outcome":"invalid_ir"}),
    }
}
