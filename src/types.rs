use crate::diagnostic::{Diagnostic, Sources, Span};
use crate::word::{ConvertMode, WordValue, WordWidth};
use std::{collections::BTreeMap, fmt};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Word(WordWidth),
    I64,
    Bool,
    Unit,
    Tuple(TupleShape),
}
pub const MAX_TUPLE_FIELDS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarType {
    Word(WordWidth),
    I64,
    Bool,
    Unit,
}
impl ScalarType {
    pub fn as_type(self) -> Type {
        match self {
            Self::Word(w) => Type::Word(w),
            Self::I64 => Type::I64,
            Self::Bool => Type::Bool,
            Self::Unit => Type::Unit,
        }
    }
    pub fn as_str(self) -> &'static str {
        self.as_type().as_str()
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TupleError;
impl fmt::Display for TupleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("tuple requires 1..8 scalar fields")
    }
}
impl std::error::Error for TupleError {}

/// A nonempty flat product shape. Unused storage is always normalized.
///
/// ```compile_fail,E0451
/// use anl::types::{TupleShape, ScalarType};
/// let shape = TupleShape { fields: [ScalarType::Unit; 8], len: 0 };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TupleShape {
    fields: [ScalarType; MAX_TUPLE_FIELDS],
    len: u8,
}
impl TupleShape {
    pub fn new(fields: &[ScalarType]) -> Result<Self, TupleError> {
        if !(1..=MAX_TUPLE_FIELDS).contains(&fields.len()) {
            return Err(TupleError);
        }
        let mut shape = Self {
            fields: [ScalarType::Unit; MAX_TUPLE_FIELDS],
            len: fields.len() as u8,
        };
        shape.fields[..fields.len()].copy_from_slice(fields);
        Ok(shape)
    }
    pub fn fields(&self) -> &[ScalarType] {
        &self.fields[..usize::from(self.len)]
    }
}
impl Type {
    pub fn scalar(self) -> Option<ScalarType> {
        match self {
            Self::Word(w) => Some(ScalarType::Word(w)),
            Self::I64 => Some(ScalarType::I64),
            Self::Bool => Some(ScalarType::Bool),
            Self::Unit => Some(ScalarType::Unit),
            Self::Tuple(_) => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Word(w) => w.as_str(),
            Self::I64 => "i64",
            Self::Bool => "bool",
            Self::Unit => "unit",
            Self::Tuple(_) => "tuple",
        }
    }
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "i64" => Some(Self::I64),
            "bool" => Some(Self::Bool),
            "unit" => Some(Self::Unit),
            name => WordWidth::from_name(name).map(Self::Word),
        }
    }
    pub fn integer(self) -> bool {
        matches!(self, Self::I64 | Self::Word(_))
    }
    pub fn contains_words(self) -> bool {
        match self {
            Self::Word(_) => true,
            Self::Tuple(s) => s.fields().iter().any(|t| matches!(t, ScalarType::Word(_))),
            _ => false,
        }
    }
}
impl ConvertMode {
    pub fn result(self, input: Type, target: Type) -> Option<Type> {
        (input.integer()
            && target.integer()
            && (self == Self::Checked || matches!(target, Type::Word(_))))
        .then_some(target)
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Self::Tuple(shape) = self {
            f.write_str("(")?;
            for (i, field) in shape.fields().iter().enumerate() {
                if i > 0 {
                    f.write_str(",")?;
                }
                f.write_str(field.as_str())?;
            }
            if shape.fields().len() == 1 {
                f.write_str(",")?;
            }
            f.write_str(")")
        } else {
            f.write_str(self.as_str())
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    BitNot,
    Neg,
    Not,
}
impl UnaryOp {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::BitNot => "bit_not",
            Self::Neg => "neg",
            Self::Not => "not",
        }
    }
    pub fn is_word(self) -> bool {
        self == Self::BitNot
    }
    pub fn result(self, input: Type) -> Option<Type> {
        match self {
            Self::BitNot if matches!(input, Type::Word(_)) => Some(input),
            Self::Neg if input == Type::I64 => Some(Type::I64),
            Self::Not if input == Type::Bool => Some(Type::Bool),
            _ => None,
        }
    }
    pub fn legacy_input(self) -> Option<Type> {
        match self {
            Self::Neg => Some(Type::I64),
            Self::Not => Some(Type::Bool),
            Self::BitNot => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    WrapAdd,
    WrapSub,
    WrapMul,
    BitAnd,
    BitXor,
    BitOr,
    Shl,
    Shr,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
}
impl BinaryOp {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::WrapAdd => "wrap_add",
            Self::WrapSub => "wrap_sub",
            Self::WrapMul => "wrap_mul",
            Self::BitAnd => "bit_and",
            Self::BitXor => "bit_xor",
            Self::BitOr => "bit_or",
            Self::Shl => "shl",
            Self::Shr => "shr",
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Div => "div",
            Self::Rem => "rem",
            Self::Lt => "lt",
            Self::Le => "le",
            Self::Gt => "gt",
            Self::Ge => "ge",
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::And => "and",
            Self::Or => "or",
        }
    }
    pub fn from_name(name: &str) -> Option<Self> {
        [
            Self::WrapAdd,
            Self::WrapSub,
            Self::WrapMul,
            Self::BitAnd,
            Self::BitXor,
            Self::BitOr,
            Self::Shl,
            Self::Shr,
            Self::Add,
            Self::Sub,
            Self::Mul,
            Self::Div,
            Self::Rem,
            Self::Lt,
            Self::Le,
            Self::Gt,
            Self::Ge,
            Self::Eq,
            Self::Ne,
            Self::And,
            Self::Or,
        ]
        .into_iter()
        .find(|op| op.as_str() == name)
    }
    pub fn is_word(self) -> bool {
        matches!(
            self,
            Self::WrapAdd
                | Self::WrapSub
                | Self::WrapMul
                | Self::BitAnd
                | Self::BitXor
                | Self::BitOr
                | Self::Shl
                | Self::Shr
        )
    }
    pub fn result(self, left: Type, right: Type) -> Option<Type> {
        if matches!(self, Self::Shl | Self::Shr) {
            return (matches!(left, Type::Word(_)) && right == Type::I64).then_some(left);
        }
        if left != right {
            return None;
        }
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Rem if left.integer() => {
                Some(left)
            }
            Self::WrapAdd
            | Self::WrapSub
            | Self::WrapMul
            | Self::BitAnd
            | Self::BitXor
            | Self::BitOr
                if matches!(left, Type::Word(_)) =>
            {
                Some(left)
            }
            Self::Lt | Self::Le | Self::Gt | Self::Ge if left.integer() => Some(Type::Bool),
            Self::Eq | Self::Ne => Some(Type::Bool),
            Self::And | Self::Or if left == Type::Bool => Some(Type::Bool),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub ty: Type,
    pub span: Span,
    pub id: usize,
    pub kind: ExprKind,
    pub depth: usize,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Word(WordValue),
    Convert {
        mode: ConvertMode,
        target: Type,
        operand: Box<Expr>,
    },
    Memory(Box<MemoryExpr>),
    Tuple(Vec<Expr>),
    Project {
        value: Box<Expr>,
        index: usize,
    },
    Integer(i64),
    Boolean(bool),
    Unit,
    Local(usize),
    Let {
        value: Box<Expr>,
        body: Box<Expr>,
    },
    LetMut {
        value: Box<Expr>,
        body: Box<Expr>,
    },
    Assign {
        index: usize,
        value: Box<Expr>,
    },
    While {
        condition: Box<Expr>,
        body: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        function: usize,
        arguments: Vec<Expr>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ViewMode {
    Read,
    Edit,
}
impl ViewMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Edit => "edit",
        }
    }
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        match name {
            "read" => Some(Self::Read),
            "edit" => Some(Self::Edit),
            _ => None,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ResourceMode {
    Owner,
    Read,
    Edit,
}
impl ResourceMode {
    pub(crate) fn writable(self) -> bool {
        self != Self::Read
    }
    pub(crate) fn lends(self, mode: ViewMode) -> bool {
        mode == ViewMode::Read || self.writable()
    }
}
impl From<ViewMode> for ResourceMode {
    fn from(mode: ViewMode) -> Self {
        match mode {
            ViewMode::Read => Self::Read,
            ViewMode::Edit => Self::Edit,
        }
    }
}
#[derive(Clone, Debug)]
pub enum MemoryExpr {
    Heap {
        site: usize,
        length: Box<Expr>,
        initial: Box<Expr>,
        success: Box<Expr>,
        failure: Box<Expr>,
    },
    Length {
        resource: usize,
    },
    Read {
        resource: usize,
        index: Box<Expr>,
    },
    Write {
        resource: usize,
        index: Box<Expr>,
        value: Box<Expr>,
    },
    CallView {
        function: usize,
        resource: usize,
        mode: ViewMode,
        arguments: Vec<Expr>,
    },
}
impl MemoryExpr {
    pub(crate) fn children(&self) -> Vec<&Expr> {
        match self {
            Self::Heap {
                length,
                initial,
                success,
                failure,
                ..
            } => vec![length, initial, success, failure],
            Self::Length { .. } => vec![],
            Self::Read { index, .. } => vec![index],
            Self::Write { index, value, .. } => vec![index, value],
            Self::CallView { arguments, .. } => arguments.iter().collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub view: Option<ViewMode>,
    pub name: String,
    pub params: Vec<Type>,
    pub result: Type,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SpecType {
    Int,
    Bool,
    Unit,
    Tuple(TupleShape),
}

impl SpecType {
    pub(crate) fn from_type(ty: Type) -> Option<Self> {
        if ty.contains_words() {
            return None;
        }
        Some(match ty {
            Type::Word(_) => return None,
            Type::I64 => Self::Int,
            Type::Bool => Self::Bool,
            Type::Unit => Self::Unit,
            Type::Tuple(shape) => Self::Tuple(shape),
        })
    }
}

impl SpecType {
    pub(crate) fn value_type(self) -> Type {
        match self {
            Self::Int => Type::I64,
            Self::Bool => Type::Bool,
            Self::Unit => Type::Unit,
            Self::Tuple(shape) => Type::Tuple(shape),
        }
    }
}

impl fmt::Display for SpecType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Self::Tuple(shape) = self {
            f.write_str("(")?;
            for (index, field) in shape.fields().iter().enumerate() {
                if index > 0 {
                    f.write_str(",")?;
                }
                f.write_str(match field {
                    ScalarType::Word(_) => "unsupported-word",
                    ScalarType::I64 => "int",
                    ScalarType::Bool => "bool",
                    ScalarType::Unit => "unit",
                })?;
            }
            if shape.fields().len() == 1 {
                f.write_str(",")?;
            }
            return f.write_str(")");
        }
        f.write_str(match self {
            Self::Tuple(_) => unreachable!(),
            Self::Int => "int",
            Self::Bool => "bool",
            Self::Unit => "unit",
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SpecExpr {
    pub(crate) ty: SpecType,
    pub(crate) span: Span,
    pub(crate) kind: SpecExprKind,
}

#[derive(Clone, Debug)]
pub(crate) enum SpecExprKind {
    Tuple(Vec<SpecExpr>),
    Project {
        value: Box<SpecExpr>,
        index: usize,
    },
    Integer(String),
    Boolean(bool),
    Unit,
    Param(usize),
    Result,
    Unary {
        op: UnaryOp,
        operand: Box<SpecExpr>,
    },
    Binary {
        op: BinaryOp,
        left: Box<SpecExpr>,
        right: Box<SpecExpr>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct Clause {
    pub(crate) expr: SpecExpr,
    pub(crate) span: Span,
}

// Source-only assertion metadata is retained for future loop verification. It is
// deliberately absent from executable expressions, core interchange, and Stage A.
#[derive(Clone, Debug)]
pub(crate) struct LocalAssertion {
    pub(crate) ty: SpecType,
    pub(crate) span: Span,
    pub(crate) kind: LocalAssertionKind,
}

#[derive(Clone, Debug)]
pub(crate) enum LocalAssertionKind {
    Tuple(Vec<LocalAssertion>),
    Project {
        value: Box<LocalAssertion>,
        index: usize,
    },
    Integer(String),
    Boolean(bool),
    Unit,
    Local(usize),
    Unary {
        op: UnaryOp,
        operand: Box<LocalAssertion>,
    },
    Binary {
        op: BinaryOp,
        left: Box<LocalAssertion>,
        right: Box<LocalAssertion>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct LocalClause {
    pub(crate) expr: LocalAssertion,
    pub(crate) span: Span,
}

/// Function-local identity in the persistent source binding table, not a local index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BindingId(pub(crate) usize);

#[derive(Clone, Debug)]
pub(crate) struct HeadBinding {
    pub(crate) parent: Option<BindingId>,
    pub(crate) name: Option<String>,
    pub(crate) ty: Type,
    pub(crate) mutable: bool,
    pub(crate) span: Span,
}

#[derive(Clone, Debug)]
pub(crate) struct LoopAnnotation {
    pub(crate) head: Option<BindingId>,
    pub(crate) clauses: Vec<LocalClause>,
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionContract {
    pub(crate) view_name: Option<String>,
    pub(crate) source_name: String,
    pub(crate) param_names: Vec<String>,
    pub(crate) requires: Vec<Clause>,
    pub(crate) ensures: Vec<Clause>,
    pub(crate) bindings: Vec<HeadBinding>,
    pub(crate) loops: BTreeMap<usize, LoopAnnotation>,
}

/// A checked program produced by [`crate::compile`] or [`crate::core::import`].
/// Its function table cannot be constructed or mutated by library callers.
///
/// ```compile_fail,E0616
/// let mut program = anl::compile("fn main()->i64{42}").unwrap();
/// program.functions.clear();
/// ```
///
/// ```compile_fail,E0451
/// let program = anl::types::Program { functions: Vec::new() };
/// ```
#[derive(Clone, Debug)]
pub struct Program {
    pub(crate) retained_revision: Option<IrRevision>,
    pub(crate) allocation_profile: Option<crate::memory::AllocationProfile>,
    pub(crate) functions: Vec<Function>,
    pub(crate) sources: Sources,
    pub(crate) contracts: Option<Vec<FunctionContract>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IrRevision {
    ScalarV0,
    StateV1,
    ProductsV2,
    MemoryV3,
    WordsV4,
}
impl IrRevision {
    pub fn semantic_revision(self) -> &'static str {
        match self {
            Self::ScalarV0 => crate::core::SEMANTIC_REVISION,
            Self::StateV1 => crate::core::LOCAL_STATE_SEMANTIC_REVISION,
            Self::ProductsV2 => crate::core::FLAT_PRODUCTS_SEMANTIC_REVISION,
            Self::MemoryV3 => crate::memory::SEMANTIC_REVISION,
            Self::WordsV4 => "anl-words-v1",
        }
    }
    pub fn core_schema(self) -> &'static str {
        match self {
            Self::ScalarV0 => "apl-core-v0",
            Self::StateV1 => "apl-core-v1",
            Self::ProductsV2 => "apl-core-v2",
            Self::MemoryV3 => "anl-core-v3",
            Self::WordsV4 => "anl-core-v4",
        }
    }
}
impl Expr {
    fn any(&self, predicate: &impl Fn(&Expr) -> bool) -> bool {
        if predicate(self) {
            return true;
        }
        match &self.kind {
            ExprKind::Memory(m) => m.children().into_iter().any(|e| e.any(predicate)),
            ExprKind::Tuple(xs) | ExprKind::Call { arguments: xs, .. } => {
                xs.iter().any(|e| e.any(predicate))
            }
            ExprKind::Project { value, .. }
            | ExprKind::Assign { value, .. }
            | ExprKind::Unary { operand: value, .. }
            | ExprKind::Convert { operand: value, .. } => value.any(predicate),
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                value.any(predicate) || body.any(predicate)
            }
            ExprKind::While { condition, body } => condition.any(predicate) || body.any(predicate),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                condition.any(predicate) || then_branch.any(predicate) || else_branch.any(predicate)
            }
            ExprKind::Binary { left, right, .. } => left.any(predicate) || right.any(predicate),
            _ => false,
        }
    }
}
impl Program {
    pub fn has_memory(&self) -> bool {
        self.functions
            .iter()
            .any(|f| f.view.is_some() || f.body.any(&|e| matches!(e.kind, ExprKind::Memory(_))))
    }
    pub fn has_local_state(&self) -> bool {
        self.functions.iter().any(|f| {
            f.body.any(&|e| {
                matches!(
                    e.kind,
                    ExprKind::LetMut { .. } | ExprKind::Assign { .. } | ExprKind::While { .. }
                )
            })
        })
    }
    pub fn has_flat_products(&self) -> bool {
        self.functions.iter().any(|f| {
            f.params
                .iter()
                .chain(std::iter::once(&f.result))
                .any(|t| matches!(t, Type::Tuple(_)))
                || f.body.any(&|e| {
                    matches!(e.ty, Type::Tuple(_)) || matches!(e.kind, ExprKind::Project { .. })
                })
        }) || self.contracts.as_ref().is_some_and(|cs| {
            cs.iter()
                .any(|c| c.bindings.iter().any(|b| matches!(b.ty, Type::Tuple(_))))
        })
    }
    pub fn uses_words(&self) -> bool {
        self.functions.iter().any(|f| {
            f.params
                .iter()
                .chain(std::iter::once(&f.result))
                .any(|t| t.contains_words())
                || f.body.any(&|e| {
                    e.ty.contains_words()
                        || matches!(e.kind, ExprKind::Word(_) | ExprKind::Convert { .. })
                        || matches!(e.kind, ExprKind::Unary { op, .. } if op.is_word())
                        || matches!(e.kind, ExprKind::Binary { op, .. } if op.is_word())
                })
        }) || self.contracts.as_ref().is_some_and(|cs| {
            cs.iter()
                .any(|c| c.bindings.iter().any(|b| b.ty.contains_words()))
        })
    }
    pub fn effective_revision(&self) -> IrRevision {
        self.retained_revision.unwrap_or_else(|| {
            if self.uses_words() {
                IrRevision::WordsV4
            } else if self.has_memory() {
                IrRevision::MemoryV3
            } else if self.has_flat_products() {
                IrRevision::ProductsV2
            } else if self.has_local_state() {
                IrRevision::StateV1
            } else {
                IrRevision::ScalarV0
            }
        })
    }
    pub fn semantic_revision(&self) -> &'static str {
        self.effective_revision().semantic_revision()
    }

    /// Attach this program's immutable source map to a diagnostic, including
    /// evaluator traps. Programs imported from core JSON have no source map.
    pub fn source_diagnostic(&self, diagnostic: Diagnostic) -> Diagnostic {
        diagnostic.with_sources(self.sources.clone())
    }

    pub fn entry(&self) -> Result<usize, crate::diagnostic::Diagnostic> {
        let id = self
            .functions
            .iter()
            .position(|f| f.name == "main")
            .ok_or_else(|| {
                crate::diagnostic::Diagnostic::new(
                    Span::default(),
                    "executable requires fn main() -> i64",
                )
            })?;
        let main = &self.functions[id];
        if main.view.is_some() || !main.params.is_empty() || main.result != Type::I64 {
            return Err(self.source_diagnostic(crate::diagnostic::Diagnostic::new(
                main.span,
                "executable entry must have signature fn main() -> i64",
            )));
        }
        Ok(id)
    }
}
