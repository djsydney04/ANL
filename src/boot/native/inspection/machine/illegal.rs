//! A checked source identity authorizes one exact zero slot, not arbitrary unknown code.
use super::*;
use anl::boot::{IllegalSlotEmissionView, Profile, V3IllegalSlotEmissionView};

pub struct IllegalSite<'a> {
    emission: IllegalSlotEmissionView<'a>,
    contribution: ContributionId,
    word: WordId,
    pc: u64,
}
impl<'a> IllegalSite<'a> {
    pub fn emission(&self) -> &IllegalSlotEmissionView<'a> {
        &self.emission
    }
    pub fn contribution(&self) -> ContributionId {
        self.contribution
    }
    pub fn word(&self) -> WordId {
        self.word
    }
    pub fn pc(&self) -> u64 {
        self.pc
    }
    /// Owned container extent. This does not assert architectural instruction length.
    pub fn extent(&self) -> u64 {
        4
    }
}
/// V3 identity stays separate from the existing V2 site and its accessor.
pub struct V3IllegalSite<'a> {
    emission: V3IllegalSlotEmissionView<'a>,
    contribution: ContributionId,
    word: WordId,
    pc: u64,
}
impl<'a> V3IllegalSite<'a> {
    pub fn emission(&self) -> &V3IllegalSlotEmissionView<'a> {
        &self.emission
    }
    pub fn contribution(&self) -> ContributionId {
        self.contribution
    }
    pub fn word(&self) -> WordId {
        self.word
    }
    pub fn pc(&self) -> u64 {
        self.pc
    }
    /// Owned container extent, not an architectural instruction length.
    pub fn extent(&self) -> u64 {
        4
    }
}

// Only the two compiler-owned opaque domains can select the shared slot checks.
pub(super) enum SlotView<'a> {
    V2(IllegalSlotEmissionView<'a>),
    V3(V3IllegalSlotEmissionView<'a>),
}
impl SlotView<'_> {
    fn signature_valid(&self) -> bool {
        match self {
            Self::V2(view) => {
                view.profile() == Profile::V2
                    && view.authority() == 0
                    && view.params().is_empty()
                    && view.result() == anl::types::Type::Unit
                    && view.effects() == [0]
            }
            Self::V3(view) => {
                view.profile() == Profile::V3
                    && view.authority() == 0
                    && view.params().is_empty()
                    && view.result() == anl::types::Type::Unit
                    && view.effects() == [0]
            }
        }
    }
    fn assembly_range(&self) -> std::ops::Range<usize> {
        match self {
            Self::V2(view) => view.assembly_range(),
            Self::V3(view) => view.assembly_range(),
        }
    }
    fn assembly(&self) -> &str {
        match self {
            Self::V2(view) => view.assembly(),
            Self::V3(view) => view.assembly(),
        }
    }
    fn symbol(&self) -> &str {
        match self {
            Self::V2(view) => view.symbol(),
            Self::V3(view) => view.symbol(),
        }
    }
}

pub(super) struct BoundIllegal<'a> {
    emission: SlotView<'a>,
    pub(super) contribution: ContributionId,
    pub(super) pc: u64,
}
fn at(mut e: MachineError, contribution: ContributionId, pc: u64) -> MachineError {
    e.contribution = Some(contribution);
    e.pc = Some(pc);
    e
}
fn charge(inventory: &mut Inventory, contribution: ContributionId, pc: u64) -> Result<()> {
    inventory
        .row(Stage::IllegalSlot)
        .map_err(|e| at(e, contribution, pc))
}
fn check(ok: bool, reason: &'static str, contribution: ContributionId, pc: u64) -> Result<()> {
    require(ok, Stage::IllegalSlot, reason).map_err(|e| at(e, contribution, pc))
}
fn bytes(raw: &[u8], offset: u64, size: u64) -> Result<&[u8]> {
    let stop = offset.checked_add(size).ok_or_else(|| {
        error(
            ErrorClass::Infrastructure,
            Stage::IllegalSlot,
            "slot file range overflows",
        )
    })?;
    let first = usize::try_from(offset).map_err(|_| {
        error(
            ErrorClass::Infrastructure,
            Stage::IllegalSlot,
            "slot offset exceeds host",
        )
    })?;
    let last = usize::try_from(stop).map_err(|_| {
        error(
            ErrorClass::Infrastructure,
            Stage::IllegalSlot,
            "slot end exceeds host",
        )
    })?;
    raw.get(first..last).ok_or_else(|| {
        error(
            ErrorClass::Infrastructure,
            Stage::IllegalSlot,
            "slot file range escapes input",
        )
    })
}
pub(super) fn bind<'a>(
    text: &TextInspection<'a>,
    image: &elf::ElfStructure<'a>,
    view: SlotView<'a>,
    inventory: &mut Inventory,
) -> Result<BoundIllegal<'a>> {
    require(
        view.signature_valid(),
        Stage::IllegalSlot,
        "opaque illegal-slot signature changed",
    )?;
    let range = view.assembly_range();
    require(
        range.start < range.end && view.assembly().get(range).is_some(),
        Stage::IllegalSlot,
        "opaque illegal-slot range changed",
    )?;
    let mut found = None;
    for (id, c) in text.contributions().iter().enumerate() {
        charge(inventory, id, c.image.value)?;
        for alias in &c.aliases {
            charge(inventory, id, c.image.value)?;
            if alias.name == view.symbol() {
                check(
                    found
                        .replace((id, alias.binding == 1 && alias.visibility == 0))
                        .is_none(),
                    "duplicate illegal-slot symbol",
                    id,
                    c.image.value,
                )?;
            }
        }
    }
    let (id, canonical_object) = found.ok_or_else(|| {
        error(
            ErrorClass::Infrastructure,
            Stage::IllegalSlot,
            "checked illegal-slot symbol is absent",
        )
    })?;
    let c = &text.contributions()[id];
    let pc = c.image.value;
    check(
        c.object == 0 && pc.is_multiple_of(4) && c.image.size == 4 && c.patches.is_empty(),
        "illegal slot has wrong owner, extent, alignment or patch",
        id,
        pc,
    )?;
    let object = elf::read_structure(text.inputs()[0], ArtifactKind::Object)
        .map_err(|e| at(imported(e, Stage::IllegalSlot), id, pc))?;
    let section = object.sections.get(c.section).ok_or_else(|| {
        at(
            error(
                ErrorClass::Infrastructure,
                Stage::IllegalSlot,
                "illegal slot object section is absent",
            ),
            id,
            pc,
        )
    })?;
    check(
        section.address == 0 && section.size == 4 && section.alignment >= 4,
        "illegal slot object section changed",
        id,
        pc,
    )?;
    check(
        bytes(object.bytes, section.offset, section.size).map_err(|e| at(e, id, pc))?
            == [0, 0, 0, 0],
        "illegal slot original bytes are nonzero",
        id,
        pc,
    )?;
    let linked = image
        .sections
        .get(usize::from(c.image.section))
        .ok_or_else(|| {
            at(
                error(
                    ErrorClass::Infrastructure,
                    Stage::IllegalSlot,
                    "illegal slot linked section is absent",
                ),
                id,
                pc,
            )
        })?;
    let offset = pc
        .checked_sub(linked.address)
        .and_then(|n| linked.offset.checked_add(n))
        .ok_or_else(|| {
            at(
                error(
                    ErrorClass::Infrastructure,
                    Stage::IllegalSlot,
                    "illegal slot linked offset overflows",
                ),
                id,
                pc,
            )
        })?;
    check(
        bytes(image.bytes, offset, 4).map_err(|e| at(e, id, pc))? == [0, 0, 0, 0],
        "illegal slot linked bytes are nonzero",
        id,
        pc,
    )?;
    let end = pc.checked_add(4).ok_or_else(|| {
        at(
            error(
                ErrorClass::Infrastructure,
                Stage::IllegalSlot,
                "illegal slot address end overflows",
            ),
            id,
            pc,
        )
    })?;
    let interior = |address| pc < address && address < end;
    check(
        !interior(image.entry),
        "ELF entry targets illegal slot interior",
        id,
        pc,
    )?;
    // Inspect all supported relocation targets, including an odd pre-mask CALL target.
    for (owner, contribution) in text.contributions().iter().enumerate() {
        for patch in &contribution.patches {
            let site = contribution
                .image
                .value
                .checked_add(patch.offset)
                .ok_or_else(|| {
                    at(
                        error(
                            ErrorClass::Infrastructure,
                            Stage::IllegalSlot,
                            "relocation site overflows",
                        ),
                        owner,
                        contribution.image.value,
                    )
                })?;
            charge(inventory, owner, site)?;
            check(
                !interior(patch.target),
                "relocation targets illegal slot interior",
                owner,
                site,
            )?;
        }
    }
    for table in &image.symbol_tables {
        for symbol in &table.symbols {
            charge(inventory, id, pc)?;
            check(
                symbol.kind != 2 || !interior(symbol.value),
                "function entry targets illegal slot interior",
                id,
                pc,
            )?;
        }
    }
    let mut image_name_found = false;
    let mut canonical_image = false;
    for alias in &c.image_aliases {
        charge(inventory, id, pc)?;
        if alias.name == view.symbol() {
            check(
                !image_name_found,
                "duplicate linked illegal-slot symbol",
                id,
                pc,
            )?;
            image_name_found = true;
            canonical_image = alias.binding == 1 && alias.visibility == 0;
        }
    }
    check(
        image_name_found,
        "linked illegal-slot canonical symbol is absent",
        id,
        pc,
    )?;
    if !canonical_object || !canonical_image || c.aliases.len() != 1 || c.image_aliases.len() != 1 {
        return Err(at(
            error(
                ErrorClass::Unsupported,
                Stage::IllegalSlot,
                "illegal-slot aliases or localization are not implemented",
            ),
            id,
            pc,
        ));
    }
    charge(inventory, id, pc)?;
    Ok(BoundIllegal {
        emission: view,
        contribution: id,
        pc,
    })
}
impl<'a> BoundIllegal<'a> {
    pub(super) fn finish(
        self,
        index: &BTreeMap<u64, WordId>,
        inventory: &Inventory,
    ) -> Result<InspectedSlot<'a>> {
        let word = owned(self.pc, index, Stage::IllegalSlot)?;
        let i = inventory.instructions[word];
        check(
            i.contribution == self.contribution
                && i.kind == InstructionKind::IntentionalIllegalSlot,
            "illegal-slot inventory identity changed",
            self.contribution,
            self.pc,
        )?;
        Ok(InspectedSlot {
            emission: self.emission,
            contribution: self.contribution,
            word,
            pc: self.pc,
        })
    }
}

/// Coordinates shared internally; each public owner retains its own identity domain.
pub(super) struct InspectedSlot<'a> {
    emission: SlotView<'a>,
    contribution: ContributionId,
    word: WordId,
    pc: u64,
}
impl<'a> InspectedSlot<'a> {
    pub(super) fn into_v2(self) -> Result<IllegalSite<'a>> {
        let SlotView::V2(emission) = self.emission else {
            return Err(at(
                error(
                    ErrorClass::Infrastructure,
                    Stage::IllegalSlot,
                    "slot identity domain differs from its owner",
                ),
                self.contribution,
                self.pc,
            ));
        };
        Ok(IllegalSite {
            emission,
            contribution: self.contribution,
            word: self.word,
            pc: self.pc,
        })
    }
    pub(super) fn into_v3(self) -> Result<V3IllegalSite<'a>> {
        let SlotView::V3(emission) = self.emission else {
            return Err(at(
                error(
                    ErrorClass::Infrastructure,
                    Stage::IllegalSlot,
                    "slot identity domain differs from its owner",
                ),
                self.contribution,
                self.pc,
            ));
        };
        Ok(V3IllegalSite {
            emission,
            contribution: self.contribution,
            word: self.word,
            pc: self.pc,
        })
    }
}
