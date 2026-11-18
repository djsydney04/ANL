//! Immutable checked-emission identity for the dedicated architectural exception slot.
use super::{CheckedPair, Operation, Profile, setup};
use crate::{bounded::OutputError, types::Type};
use std::{fmt, ops::Range};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IllegalSlotUnsupported {
    Revision { profile: Profile },
}
impl fmt::Display for IllegalSlotUnsupported {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Revision { profile } => write!(
                out,
                "illegal-slot identity does not support {}",
                profile.target()
            ),
        }
    }
}
impl std::error::Error for IllegalSlotUnsupported {}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExceptionSetupUnsupported {
    Revision { profile: Profile },
    MissingIllegalSlot,
    Setup(setup::SetupProfileUnsupported),
}
impl fmt::Display for ExceptionSetupUnsupported {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Revision { profile } => write!(
                out,
                "exception setup identity does not support {}",
                profile.target()
            ),
            Self::MissingIllegalSlot => {
                out.write_str("exception setup identity requires the illegal slot")
            }
            Self::Setup(reason) => reason.fmt(out),
        }
    }
}
impl std::error::Error for ExceptionSetupUnsupported {}
struct IllegalIdentity {
    primitive: usize,
    symbol: String,
    assembly: Range<usize>,
}
pub(super) struct Identity {
    profile: Profile,
    illegal: Option<IllegalIdentity>,
    setup: Result<setup::SetupIdentity, ExceptionSetupUnsupported>,
}
/// Source-artifact identity only. Public construction and mutation are unavailable.
pub struct IllegalSlotEmissionView<'a> {
    files: &'a [(&'static str, String); 6],
    identity: &'a IllegalIdentity,
}
impl IllegalSlotEmissionView<'_> {
    pub fn profile(&self) -> Profile {
        Profile::V2
    }
    pub fn primitive(&self) -> usize {
        self.identity.primitive
    }
    pub fn authority(&self) -> u64 {
        0
    }
    pub fn symbol(&self) -> &str {
        &self.identity.symbol
    }
    pub fn params(&self) -> &[Type] {
        &[]
    }
    pub fn result(&self) -> Type {
        Type::Unit
    }
    pub fn effects(&self) -> &[u64] {
        &[0]
    }
    /// Textual definition interval, not a native instruction length.
    pub fn assembly_range(&self) -> Range<usize> {
        self.identity.assembly.clone()
    }
    pub fn core(&self) -> &str {
        &self.files[0].1
    }
    pub fn mir(&self) -> &str {
        &self.files[1].1
    }
    pub fn c(&self) -> &str {
        &self.files[2].1
    }
    pub fn assembly(&self) -> &str {
        &self.files[3].1
    }
    pub fn linker(&self) -> &str {
        &self.files[4].1
    }
    pub fn manifest(&self) -> &str {
        &self.files[5].1
    }
}
/// Separate V2 authority domain; this never exposes a V1 SetupEmissionView.
pub struct ExceptionSetupEmissionView<'a> {
    files: &'a [(&'static str, String); 6],
    illegal: &'a IllegalIdentity,
    setup: &'a setup::SetupIdentity,
}
impl ExceptionSetupEmissionView<'_> {
    pub fn profile(&self) -> Profile {
        Profile::V2
    }
    pub fn functions(&self) -> &[setup::SetupFunction; 3] {
        self.setup.functions()
    }
    pub fn setup_primitives(&self) -> &[setup::SetupPrimitive] {
        self.setup.primitives()
    }
    pub fn abi(&self) -> &[setup::SetupAbi; 3] {
        self.setup.abi()
    }
    pub fn helper_count(&self) -> usize {
        0
    }
    pub fn illegal_slot(&self) -> IllegalSlotEmissionView<'_> {
        IllegalSlotEmissionView {
            files: self.files,
            identity: self.illegal,
        }
    }
}
impl Identity {
    pub(super) fn illegal<'a>(
        &'a self,
        files: &'a [(&'static str, String); 6],
    ) -> Result<Option<IllegalSlotEmissionView<'a>>, IllegalSlotUnsupported> {
        if self.profile != Profile::V2 {
            return Err(IllegalSlotUnsupported::Revision {
                profile: self.profile,
            });
        }
        Ok(self
            .illegal
            .as_ref()
            .map(|identity| IllegalSlotEmissionView { files, identity }))
    }
    pub(super) fn setup<'a>(
        &'a self,
        files: &'a [(&'static str, String); 6],
    ) -> Result<ExceptionSetupEmissionView<'a>, ExceptionSetupUnsupported> {
        let setup = self.setup.as_ref().map_err(|reason| *reason)?;
        let illegal = self
            .illegal
            .as_ref()
            .ok_or(ExceptionSetupUnsupported::MissingIllegalSlot)?;
        Ok(ExceptionSetupEmissionView {
            files,
            illegal,
            setup,
        })
    }
}
fn invariant(message: &str) -> OutputError {
    OutputError::Infrastructure(message.into())
}
// The arguments are the existing emitter's exact independently bounded range collections.
#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    pair: &CheckedPair,
    helper_count: usize,
    function_ranges: &[Range<usize>],
    primitive_ranges: &[Range<usize>],
    abi_ranges: &[Range<usize>],
    c: &str,
    assembly: &str,
    illegal_range: Option<&(usize, Range<usize>)>,
) -> Result<Identity, OutputError> {
    let profile = pair.program.profile;
    if profile != Profile::V2 {
        if profile == Profile::V1 && illegal_range.is_some() {
            return Err(invariant("legacy emission has an illegal slot range"));
        }
        // V3 retains manifest ownership but has no qualified native identity view.
        return Ok(Identity {
            profile,
            illegal: None,
            setup: Err(ExceptionSetupUnsupported::Revision { profile }),
        });
    }
    let mut rows = pair
        .program
        .primitives
        .iter()
        .filter(|p| matches!(p.operation, Operation::IllegalInstruction { .. }));
    let Some(row) = rows.next() else {
        if illegal_range.is_some() {
            return Err(invariant("illegal slot range lacks a checked operation"));
        }
        return Ok(Identity {
            profile,
            illegal: None,
            setup: Err(ExceptionSetupUnsupported::MissingIllegalSlot),
        });
    };
    if rows.next().is_some()
        || row.operation != (Operation::IllegalInstruction { authority: 0 })
        || !row.params.is_empty()
        || row.result != Type::Unit
        || row.effects != [0]
    {
        return Err(invariant("illegal slot checked identity changed"));
    }
    let (id, range) =
        illegal_range.ok_or_else(|| invariant("illegal operation lacks its emission range"))?;
    if *id != row.id
        || range.start >= range.end
        || range.end > assembly.len()
        || !assembly.is_char_boundary(range.start)
        || !assembly.is_char_boundary(range.end)
    {
        return Err(invariant("illegal slot definition range changed"));
    }
    let illegal = IllegalIdentity {
        primitive: row.id,
        symbol: format!("anl_boot_f{}", row.id),
        assembly: range.clone(),
    };
    let setup = setup::build_exception(
        pair,
        helper_count,
        function_ranges,
        primitive_ranges,
        abi_ranges,
        c,
        assembly,
    )?
    .map_err(ExceptionSetupUnsupported::Setup);
    Ok(Identity {
        profile,
        illegal: Some(illegal),
        setup,
    })
}
