//! Structural occurrence identities derived during canonical lowering.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoreEdge {
    LetValue,
    LetBody,
    WhileCondition,
    WhileBody,
    IfCondition,
    IfThen,
    IfElse,
    UnaryOperand,
    BinaryLeft,
    BinaryRight,
    CallArgument(usize),
    ConvertOperand,
    TupleField(usize),
    ProjectOperand,
    AssignValue,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockChild {
    MutableBody,
    WhileCondition,
    WhileBody,
    BranchThen,
    BranchElse,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockEdge {
    pub instruction: usize,
    pub child: BlockChild,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirPath {
    pub blocks: Vec<BlockEdge>,
    pub instruction: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    pub function: usize,
    pub core_path: Vec<CoreEdge>,
    pub mir_path: MirPath,
}
