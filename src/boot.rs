//! Checked boot source and Core admission. Freestanding source emission does not invoke a target compiler.
mod check;
mod emit;
mod publish;
mod templates;
pub use emit::{Bundle, emit};
mod mir;
mod source;
mod wire;
pub use mir::{
    BlockChild, BlockEdge, CheckedPair, CoreEdge, MIR_SCHEMA, MirPath, Origin, PairError,
    export_mir, export_pair_core, import_pair, lower,
};

use crate::{
    diagnostic::Sources,
    types::{Function, FunctionContract, Type},
    word::WordWidth,
};
pub use wire::{export_core, import_core};

pub const SCHEMA: &str = "anl-boot-core-v1";
pub const SEMANTIC_REVISION: &str = "anl-boot-rv64-virt-v1";
pub const TARGET: &str = "rv64-virt-sbi-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Operation {
    Read8 {
        region: u64,
        offset: u64,
    },
    Write8 {
        region: u64,
        offset: u64,
    },
    Fence {
        region: u64,
    },
    CsrClear {
        authority: u64,
        register: String,
        mask: u64,
    },
    CsrWrite {
        authority: u64,
        register: String,
        value: u64,
    },
    InstallTrap {
        authority: u64,
        handler: u64,
    },
}
impl Operation {
    fn params(&self) -> Vec<Type> {
        if matches!(self, Self::Write8 { .. }) {
            vec![Type::Word(WordWidth::U8)]
        } else {
            vec![]
        }
    }
    fn result(&self) -> Type {
        if matches!(self, Self::Read8 { .. }) {
            Type::Word(WordWidth::U8)
        } else {
            Type::Unit
        }
    }
    fn effects(&self) -> Vec<u64> {
        vec![if matches!(
            self,
            Self::Read8 { .. } | Self::Write8 { .. } | Self::Fence { .. }
        ) {
            1
        } else {
            0
        }]
    }
    fn valid(&self, hardware: usize) -> bool {
        match self {
            Self::Read8 { region, offset } => *region == 0 && *offset == 5,
            Self::Write8 { region, offset } => *region == 0 && *offset <= 4,
            Self::Fence { region } => *region == 0,
            Self::CsrClear {
                authority,
                register,
                mask,
            } => *authority == 0 && register == "sstatus" && *mask == 2,
            Self::CsrWrite {
                authority,
                register,
                value,
            } => *authority == 0 && register == "sie" && *value == 0,
            Self::InstallTrap { authority, handler } => {
                *authority == 0 && *handler == hardware as u64
            }
        }
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Primitive {
    pub id: usize,
    pub name: String,
    pub operation: Operation,
    pub params: Vec<Type>,
    pub result: Type,
    pub effects: Vec<u64>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TailEdge {
    Value,
    Body,
}

/// Constructed only after ordinary typing and the complete boot policy check.
/// It deliberately has no conversion or accessor to a hosted `types::Program`.
pub struct CheckedProgram {
    functions: Vec<Function>,
    effects: Vec<Vec<u64>>,
    primitives: Vec<Primitive>,
    entries: [usize; 3],
    _tails: [Vec<TailEdge>; 3],
    _sources: Sources,
    _contracts: Option<Vec<FunctionContract>>,
}

pub(crate) use source::check_source;
