use crate::diagnostic::{Diagnostic, Sources, Span};
use std::{collections::BTreeMap, fmt};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    I64,
    Bool,
    Unit,
    Tuple(TupleShape),
}
pub const MAX_TUPLE_FIELDS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarType {
    I64,
    Bool,
    Unit,
}
impl ScalarType {
    pub fn as_type(self) -> Type {
        match self {
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
            Self::I64 => Some(ScalarType::I64),
            Self::Bool => Some(ScalarType::Bool),
            Self::Unit => Some(ScalarType::Unit),
            Self::Tuple(_) => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
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
            _ => None,
        }
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
    Neg,
    Not,
}
impl UnaryOp {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Neg => "neg",
            Self::Not => "not",
        }
    }
    pub fn input(self) -> Type {
        match self {
            Self::Neg => Type::I64,
            Self::Not => Type::Bool,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
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
    pub fn result(self, left: Type, right: Type) -> Option<Type> {
        if left != right {
            return None;
        }
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Rem if left == Type::I64 => {
                Some(Type::I64)
            }
            Self::Lt | Self::Le | Self::Gt | Self::Ge if left == Type::I64 => Some(Type::Bool),
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

#[derive(Clone, Debug)]
pub struct Function {
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
}

impl SpecType {
    pub(crate) fn checked(ty: Type, span: Span) -> Result<Self, Diagnostic> {
        match ty {
            Type::I64 => Ok(Self::Int),
            Type::Bool => Ok(Self::Bool),
            Type::Unit => Ok(Self::Unit),
            Type::Tuple(_) => Err(Diagnostic::new(
                span,
                "tuple references are not allowed in scalar specifications",
            )),
        }
    }
}

impl SpecType {
    pub(crate) fn scalar_type(self) -> Type {
        match self {
            Self::Int => Type::I64,
            Self::Bool => Type::Bool,
            Self::Unit => Type::Unit,
        }
    }
}

impl fmt::Display for SpecType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
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
    pub(crate) functions: Vec<Function>,
    pub(crate) sources: Sources,
    pub(crate) contracts: Option<Vec<FunctionContract>>,
}

impl Program {
    pub fn has_local_state(&self) -> bool {
        fn contains(expr: &Expr) -> bool {
            match &expr.kind {
                ExprKind::LetMut { .. } | ExprKind::Assign { .. } | ExprKind::While { .. } => true,
                ExprKind::Let { value, body } => contains(value) || contains(body),
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => contains(condition) || contains(then_branch) || contains(else_branch),
                ExprKind::Tuple(fields) => fields.iter().any(contains),
                ExprKind::Project { value, .. } => contains(value),
                ExprKind::Unary { operand, .. } => contains(operand),
                ExprKind::Binary { left, right, .. } => contains(left) || contains(right),
                ExprKind::Call { arguments, .. } => arguments.iter().any(contains),
                ExprKind::Integer(_)
                | ExprKind::Boolean(_)
                | ExprKind::Unit
                | ExprKind::Local(_) => false,
            }
        }
        self.functions
            .iter()
            .any(|function| contains(&function.body))
    }

    /// Structural feature detection includes unreachable code and retained source bindings.
    pub fn has_flat_products(&self) -> bool {
        fn contains(e: &Expr) -> bool {
            if matches!(e.ty, Type::Tuple(_)) {
                return true;
            }
            match &e.kind {
                ExprKind::Tuple(_) | ExprKind::Project { .. } => true,
                ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                    contains(value) || contains(body)
                }
                ExprKind::Assign { value, .. } | ExprKind::Unary { operand: value, .. } => {
                    contains(value)
                }
                ExprKind::While { condition, body } => contains(condition) || contains(body),
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => contains(condition) || contains(then_branch) || contains(else_branch),
                ExprKind::Binary { left, right, .. } => contains(left) || contains(right),
                ExprKind::Call { arguments, .. } => arguments.iter().any(contains),
                _ => false,
            }
        }
        self.functions.iter().any(|f| {
            f.params
                .iter()
                .chain(std::iter::once(&f.result))
                .any(|t| matches!(t, Type::Tuple(_)))
                || contains(&f.body)
        }) || self.contracts.as_ref().is_some_and(|cs| {
            cs.iter()
                .any(|c| c.bindings.iter().any(|b| matches!(b.ty, Type::Tuple(_))))
        })
    }

    pub fn semantic_revision(&self) -> &'static str {
        if self.has_flat_products() {
            crate::core::FLAT_PRODUCTS_SEMANTIC_REVISION
        } else if self.has_local_state() {
            crate::core::LOCAL_STATE_SEMANTIC_REVISION
        } else {
            crate::core::SEMANTIC_REVISION
        }
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
        if !main.params.is_empty() || main.result != Type::I64 {
            return Err(self.source_diagnostic(crate::diagnostic::Diagnostic::new(
                main.span,
                "executable entry must have signature fn main() -> i64",
            )));
        }
        Ok(id)
    }
}
