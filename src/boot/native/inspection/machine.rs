//! Known instruction edges only; returns, authority and native safety stay open.
use crate::decode::{Decoded, Effect, Op, Operands, decode};
use crate::text::elf::{self, ArtifactKind, ErrorClass, StructuralError};
use crate::text::{MAX_TEXT_BYTES, MAX_WITNESS_ROWS, TextInspection};
use std::collections::BTreeMap;

pub const MAX_WORDS: usize = (MAX_TEXT_BYTES / 4) as usize;
pub const MAX_EDGES: usize = MAX_WORDS * 2;
pub type WordId = usize;
pub type ContributionId = usize;
pub type PairId = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    Structure,
    Inventory,
    Decode,
    Edges,
    Pairs,
}
#[derive(Debug)]
pub struct MachineError {
    pub class: ErrorClass,
    pub reason: &'static str,
    pub stage: Stage,
    pub contribution: Option<ContributionId>,
    pub pc: Option<u64>,
}
type Result<T> = std::result::Result<T, MachineError>;
fn error(class: ErrorClass, stage: Stage, reason: &'static str) -> MachineError {
    MachineError {
        class,
        reason,
        stage,
        contribution: None,
        pc: None,
    }
}
fn located(mut e: MachineError, instruction: Instruction) -> MachineError {
    e.contribution = Some(instruction.contribution);
    e.pc = Some(instruction.pc);
    e
}
fn imported(e: StructuralError, stage: Stage) -> MachineError {
    error(e.class, stage, e.reason)
}
fn require(condition: bool, stage: Stage, reason: &'static str) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(error(ErrorClass::Infrastructure, stage, reason))
    }
}
fn unsupported<T>(reason: &'static str) -> Result<T> {
    Err(error(ErrorClass::Unsupported, Stage::Edges, reason))
}
fn add(address: u64, displacement: i64, stage: Stage) -> Result<u64> {
    let value = i128::from(address) + i128::from(displacement);
    u64::try_from(value).map_err(|_| {
        error(
            ErrorClass::Infrastructure,
            stage,
            "PC arithmetic escapes address domain",
        )
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Instruction {
    pub id: WordId,
    pub contribution: ContributionId,
    pub pc: u64,
    pub raw: u32,
    pub decoded: Decoded,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeKind {
    Fallthrough,
    BranchTaken,
    BranchNotTaken,
    Jump,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalEdge {
    pub source: WordId,
    pub target: WordId,
    pub kind: EdgeKind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Continuation {
    pub source: WordId,
    pub target: WordId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Transfer {
    pub source: WordId,
    pub target: WordId,
    pub target_contribution: ContributionId,
    pub link_register: u8,
    pub pair: Option<PairId>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pair {
    pub id: PairId,
    pub contribution: ContributionId,
    pub patch: usize,
    pub first: WordId,
    pub second: WordId,
    pub unmasked_target: u64,
    pub effective_target: u64,
}

/// Private constructor and immutable accessors; never a publication permit.
pub struct MachineInspection<'a> {
    text: TextInspection<'a>,
    inventory: Inventory,
}
impl<'a> MachineInspection<'a> {
    pub fn text(&self) -> &TextInspection<'a> {
        &self.text
    }
    pub fn instructions(&self) -> &[Instruction] {
        &self.inventory.instructions
    }
    pub fn local_edges(&self) -> &[LocalEdge] {
        &self.inventory.local_edges
    }
    pub fn transfers(&self) -> &[Transfer] {
        &self.inventory.transfers
    }
    pub fn continuations(&self) -> &[Continuation] {
        &self.inventory.continuations
    }
    pub fn pairs(&self) -> &[Pair] {
        &self.inventory.pairs
    }
    pub fn returns(&self) -> &[WordId] {
        &self.inventory.returns
    }
    pub fn memory_sites(&self) -> &[WordId] {
        &self.inventory.memory
    }
    pub fn csr_sites(&self) -> &[WordId] {
        &self.inventory.csr
    }
    pub fn fence_sites(&self) -> &[WordId] {
        &self.inventory.fences
    }
    pub fn witness_rows(&self) -> usize {
        self.inventory.rows
    }
    pub fn edge_count(&self) -> usize {
        self.inventory.edges
    }
}
#[derive(Default)]
struct Inventory {
    instructions: Vec<Instruction>,
    local_edges: Vec<LocalEdge>,
    transfers: Vec<Transfer>,
    continuations: Vec<Continuation>,
    pairs: Vec<Pair>,
    returns: Vec<WordId>,
    memory: Vec<WordId>,
    csr: Vec<WordId>,
    fences: Vec<WordId>,
    rows: usize,
    edges: usize,
}
impl Inventory {
    fn row(&mut self, stage: Stage) -> Result<()> {
        if self.rows >= MAX_WITNESS_ROWS {
            return Err(error(
                ErrorClass::Resource,
                stage,
                "combined machine witness row limit exceeded",
            ));
        }
        self.rows += 1;
        Ok(())
    }
    fn edge(&mut self) -> Result<()> {
        if self.edges >= MAX_EDGES {
            return Err(error(
                ErrorClass::Resource,
                Stage::Edges,
                "machine edge limit exceeded",
            ));
        }
        self.row(Stage::Edges)?;
        self.edges += 1;
        Ok(())
    }
    fn local(&mut self, source: WordId, target: WordId, kind: EdgeKind) -> Result<()> {
        self.edge()?;
        self.local_edges.push(LocalEdge {
            source,
            target,
            kind,
        });
        Ok(())
    }
}

fn owned(pc: u64, index: &BTreeMap<u64, WordId>, stage: Stage) -> Result<WordId> {
    require(
        pc.is_multiple_of(4),
        stage,
        "control target is not four-byte aligned",
    )?;
    index.get(&pc).copied().ok_or_else(|| {
        error(
            ErrorClass::Infrastructure,
            stage,
            "control target is not an owned instruction",
        )
    })
}
fn next(i: Instruction, inventory: &Inventory, index: &BTreeMap<u64, WordId>) -> Result<WordId> {
    let target = owned(add(i.pc, 4, Stage::Edges)?, index, Stage::Edges)?;
    require(
        inventory.instructions[target].contribution == i.contribution,
        Stage::Edges,
        "fallthrough escapes its contribution",
    )?;
    Ok(target)
}
fn transfer(
    inventory: &mut Inventory,
    index: &BTreeMap<u64, WordId>,
    entries: &BTreeMap<u64, ContributionId>,
    i: Instruction,
    target: WordId,
    rd: u8,
    pair: Option<PairId>,
) -> Result<()> {
    if rd != 0 && rd != 1 {
        return unsupported("alternate link destination is not implemented");
    }
    let target_instruction = inventory.instructions[target];
    require(
        entries.get(&target_instruction.pc) == Some(&target_instruction.contribution),
        Stage::Edges,
        "transfer target is not a function entry",
    )?;
    let continuation = if rd == 1 {
        let pc = add(i.pc, 4, Stage::Edges)?;
        match index.get(&pc).copied() {
            Some(id) if inventory.instructions[id].contribution == i.contribution => Some(id),
            _ => {
                return unsupported(
                    "linking transfer continuation is not implemented at function end",
                );
            }
        }
    } else {
        None
    };
    inventory.edge()?;
    inventory.transfers.push(Transfer {
        source: i.id,
        target,
        target_contribution: target_instruction.contribution,
        link_register: rd,
        pair,
    });
    if let Some(target) = continuation {
        inventory.edge()?;
        inventory.continuations.push(Continuation {
            source: i.id,
            target,
        });
    }
    Ok(())
}

/// Consumes actual M1 evidence; no caller-supplied records or file reopening.
pub fn inspect_machine<'a>(text: TextInspection<'a>) -> Result<MachineInspection<'a>> {
    let image = elf::read_structure(text.inputs()[2], ArtifactKind::Image)
        .map_err(|e| imported(e, Stage::Structure))?;
    let mut inventory = Inventory {
        rows: text.witness_rows(),
        ..Inventory::default()
    };
    let mut order: Vec<_> = (0..text.contributions().len()).collect();
    order.sort_unstable_by_key(|&id| text.contributions()[id].image.value);
    let mut index = BTreeMap::new();
    let mut entries = BTreeMap::new();
    for id in order {
        let c = &text.contributions()[id];
        require(
            c.image.value.is_multiple_of(4) && c.image.size.is_multiple_of(4),
            Stage::Inventory,
            "owned text interval is not word aligned",
        )?;
        require(
            entries.insert(c.image.value, id).is_none(),
            Stage::Inventory,
            "duplicate contribution entry",
        )?;
        let section = image
            .sections
            .get(usize::from(c.image.section))
            .ok_or_else(|| {
                error(
                    ErrorClass::Infrastructure,
                    Stage::Inventory,
                    "contribution section is absent",
                )
            })?;
        let offset = c
            .image
            .value
            .checked_sub(section.address)
            .and_then(|relative| section.offset.checked_add(relative))
            .ok_or_else(|| {
                error(
                    ErrorClass::Infrastructure,
                    Stage::Inventory,
                    "contribution file offset overflows",
                )
            })?;
        let stop = offset.checked_add(c.image.size).ok_or_else(|| {
            error(
                ErrorClass::Infrastructure,
                Stage::Inventory,
                "contribution file interval overflows",
            )
        })?;
        let start = usize::try_from(offset).map_err(|_| {
            error(
                ErrorClass::Infrastructure,
                Stage::Inventory,
                "file offset exceeds host",
            )
        })?;
        let stop = usize::try_from(stop).map_err(|_| {
            error(
                ErrorClass::Infrastructure,
                Stage::Inventory,
                "file end exceeds host",
            )
        })?;
        let bytes = image.bytes.get(start..stop).ok_or_else(|| {
            error(
                ErrorClass::Infrastructure,
                Stage::Inventory,
                "contribution escapes image bytes",
            )
        })?;
        for (offset, bytes) in bytes.as_chunks::<4>().0.iter().enumerate() {
            if inventory.instructions.len() >= MAX_WORDS {
                return Err(error(
                    ErrorClass::Resource,
                    Stage::Inventory,
                    "machine word limit exceeded",
                ));
            }
            inventory.row(Stage::Inventory)?;
            let pc = c
                .image
                .value
                .checked_add((offset as u64) * 4)
                .ok_or_else(|| {
                    error(
                        ErrorClass::Infrastructure,
                        Stage::Inventory,
                        "instruction PC overflows",
                    )
                })?;
            let raw = u32::from_le_bytes(*bytes);
            let decoded = decode(raw).map_err(|e| MachineError {
                class: e.class,
                reason: e.reason,
                stage: Stage::Decode,
                contribution: Some(id),
                pc: Some(pc),
            })?;
            let instruction = Instruction {
                id: inventory.instructions.len(),
                contribution: id,
                pc,
                raw,
                decoded,
            };
            require(
                index.insert(pc, instruction.id).is_none(),
                Stage::Inventory,
                "duplicate instruction PC",
            )?;
            inventory.instructions.push(instruction);
        }
    }

    let mut second_words = BTreeMap::new();
    for (id, c) in text.contributions().iter().enumerate() {
        for (patch_id, patch) in c.patches.iter().enumerate() {
            if patch.kind != 19 {
                continue;
            }
            let pc = c.image.value.checked_add(patch.offset).ok_or_else(|| {
                error(
                    ErrorClass::Infrastructure,
                    Stage::Pairs,
                    "pair PC overflows",
                )
            })?;
            let first = owned(pc, &index, Stage::Pairs)?;
            let second = owned(add(pc, 4, Stage::Pairs)?, &index, Stage::Pairs)?;
            let a = inventory.instructions[first];
            let b = inventory.instructions[second];
            require(
                a.contribution == id && b.contribution == id,
                Stage::Pairs,
                "pair escapes its contribution",
            )?;
            let (high_reg, high) = match (a.decoded.operation, a.decoded.operands) {
                (Op::Auipc, Operands::Upper { rd, immediate }) if rd != 0 => (rd, immediate),
                _ => {
                    return Err(located(
                        error(
                            ErrorClass::Infrastructure,
                            Stage::Pairs,
                            "pair first word is not live AUIPC",
                        ),
                        a,
                    ));
                }
            };
            let (base, low) = match (b.decoded.operation, b.decoded.operands) {
                (Op::Jalr, Operands::Indirect { base, offset, .. }) => (base, offset),
                _ => {
                    return Err(located(
                        error(
                            ErrorClass::Infrastructure,
                            Stage::Pairs,
                            "pair second word is not JALR",
                        ),
                        b,
                    ));
                }
            };
            require(
                base == high_reg,
                Stage::Pairs,
                "pair base register disagrees",
            )?;
            let combined = i128::from(a.pc) + i128::from(high) + i128::from(low);
            let unmasked_target = u64::try_from(combined).map_err(|_| {
                error(
                    ErrorClass::Infrastructure,
                    Stage::Pairs,
                    "combined pair arithmetic escapes address domain",
                )
            })?;
            require(
                unmasked_target == patch.target && patch.high_site == a.pc,
                Stage::Pairs,
                "decoded pair target disagrees with relocation",
            )?;
            require(
                patch.linked_words.as_slice() == [a.raw, b.raw],
                Stage::Pairs,
                "pair words disagree with M1 witness",
            )?;
            let effective_target = unmasked_target & !1;
            let target = owned(effective_target, &index, Stage::Pairs)?;
            require(
                entries.get(&effective_target)
                    == Some(&inventory.instructions[target].contribution),
                Stage::Pairs,
                "pair target is not a function entry",
            )?;
            inventory.row(Stage::Pairs)?;
            let pair = Pair {
                id: inventory.pairs.len(),
                contribution: id,
                patch: patch_id,
                first,
                second,
                unmasked_target,
                effective_target,
            };
            require(
                second_words.insert(second, pair.id).is_none(),
                Stage::Pairs,
                "duplicate pair second word",
            )?;
            inventory.pairs.push(pair);
        }
    }

    for word in 0..inventory.instructions.len() {
        let i = inventory.instructions[word];
        let result = (|| {
            match i.decoded.effect {
                Effect::None => {}
                Effect::Load { .. } | Effect::Store { .. } => {
                    inventory.row(Stage::Edges)?;
                    inventory.memory.push(word);
                }
                Effect::Csr { .. } => {
                    inventory.row(Stage::Edges)?;
                    inventory.csr.push(word);
                }
                Effect::Fence => {
                    inventory.row(Stage::Edges)?;
                    inventory.fences.push(word);
                }
            }
            // A CALL pair can end in the exact generic return encoding.
            if let Some(&pair_id) = second_words.get(&word) {
                let pair = inventory.pairs[pair_id];
                let rd = match i.decoded.operands {
                    Operands::Indirect { rd, .. } => rd,
                    _ => {
                        return Err(error(
                            ErrorClass::Infrastructure,
                            Stage::Pairs,
                            "pair descriptor changed",
                        ));
                    }
                };
                let target = owned(pair.effective_target, &index, Stage::Pairs)?;
                return transfer(
                    &mut inventory,
                    &index,
                    &entries,
                    i,
                    target,
                    rd,
                    Some(pair_id),
                );
            }
            match i.decoded.operands {
                Operands::Branch { displacement, .. } => {
                    let target =
                        owned(add(i.pc, displacement, Stage::Edges)?, &index, Stage::Edges)?;
                    if inventory.instructions[target].contribution != i.contribution {
                        if entries.contains_key(&inventory.instructions[target].pc) {
                            return unsupported(
                                "conditional interfunction transfer is not implemented",
                            );
                        }
                        return Err(error(
                            ErrorClass::Infrastructure,
                            Stage::Edges,
                            "branch targets another function interior",
                        ));
                    }
                    let fallthrough = next(i, &inventory, &index)?;
                    inventory.local(word, target, EdgeKind::BranchTaken)?;
                    inventory.local(word, fallthrough, EdgeKind::BranchNotTaken)
                }
                Operands::Jump { rd, displacement } => {
                    let target =
                        owned(add(i.pc, displacement, Stage::Edges)?, &index, Stage::Edges)?;
                    if rd == 0 && inventory.instructions[target].contribution == i.contribution {
                        inventory.local(word, target, EdgeKind::Jump)
                    } else {
                        transfer(&mut inventory, &index, &entries, i, target, rd, None)
                    }
                }
                Operands::Indirect {
                    rd: 0,
                    base: 1,
                    offset: 0,
                } => {
                    inventory.row(Stage::Edges)?;
                    inventory.returns.push(word);
                    Ok(())
                }
                Operands::Indirect { .. } => {
                    unsupported("indirect target analysis is not implemented")
                }
                _ => {
                    let target = next(i, &inventory, &index)?;
                    inventory.local(word, target, EdgeKind::Fallthrough)
                }
            }
        })();
        result.map_err(|e| located(e, i))?;
    }

    // Only known edges/entry roots are covered. Unresolved returns stay open.
    for pair in &inventory.pairs {
        let second = inventory.instructions[pair.second];
        require(
            !entries.contains_key(&second.pc),
            Stage::Pairs,
            "function entry bypasses pair first word",
        )?;
        require(
            image.entry != second.pc,
            Stage::Pairs,
            "ELF entry bypasses pair first word",
        )?;
    }
    for edge in &inventory.local_edges {
        if let Some(&pair_id) = second_words.get(&edge.target) {
            let pair = inventory.pairs[pair_id];
            require(
                edge.source == pair.first && edge.kind == EdgeKind::Fallthrough,
                Stage::Pairs,
                "local control bypasses pair first word",
            )?;
        }
    }
    for edge in &inventory.transfers {
        require(
            !second_words.contains_key(&edge.target),
            Stage::Pairs,
            "transfer bypasses pair first word",
        )?;
    }
    for edge in &inventory.continuations {
        require(
            !second_words.contains_key(&edge.target),
            Stage::Pairs,
            "call continuation bypasses pair first word",
        )?;
    }
    Ok(MachineInspection { text, inventory })
}
