//! Closed setup identity, returning leaves, and independent entry-stack episodes.
//! All conclusions remain conditional on the documented native refinement premises.
use super::*;
use crate::machine::decode::CsrSource;
use crate::machine::text::elf::{self, ArtifactKind};
use anl::boot::{Bundle, SetupEmissionView, SetupOperation, SetupRole};

pub type StackError = FrameError;

#[derive(Clone, Copy, Debug)]
pub struct IdentityJoin {
    pub contribution: ContributionId,
    pub source_function: usize,
    pub role: Option<SetupRole>,
    pub primitive: Option<SetupOperation>,
    pub entry_thunk: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct CallUse {
    pub caller: WordId,
    pub target: ContributionId,
    pub transfer: usize,
    pub pair: usize,
    pub continuation: WordId,
    pub link_value: u64,
    pub caller_sp: i64,
    pub leaf: usize,
    pub combined_depth: u128,
}
/// No public constructor or mutable projection: only a complete leaf check creates this.
pub struct ReturningSetupLeaf {
    contribution: ContributionId,
    operation: SetupOperation,
    csr: WordId,
    return_word: WordId,
    depth: u64,
}
impl ReturningSetupLeaf {
    pub fn contribution(&self) -> ContributionId {
        self.contribution
    }
    pub fn operation(&self) -> SetupOperation {
        self.operation
    }
    pub fn csr(&self) -> WordId {
        self.csr
    }
    pub fn return_word(&self) -> WordId {
        self.return_word
    }
    pub fn depth(&self) -> u64 {
        self.depth
    }
}
/// The checked stackless thunk establishes a fresh entry premise, not an ordinary call.
pub struct RootEntry {
    role: SetupRole,
    contribution: ContributionId,
    target: ContributionId,
    stack: Range<u64>,
    tail: WordId,
    pair: usize,
}
impl RootEntry {
    pub fn role(&self) -> SetupRole {
        self.role
    }
    pub fn contribution(&self) -> ContributionId {
        self.contribution
    }
    pub fn target(&self) -> ContributionId {
        self.target
    }
    pub fn stack(&self) -> Range<u64> {
        self.stack.clone()
    }
    pub fn tail(&self) -> WordId {
        self.tail
    }
    pub fn pair(&self) -> usize {
        self.pair
    }
}
pub struct ConditionalSetupStackBounds {
    boot: u64,
    hardware: u64,
    language: u64,
    terminal: u64,
}
impl ConditionalSetupStackBounds {
    pub fn boot(&self) -> u64 {
        self.boot
    }
    pub fn hardware(&self) -> u64 {
        self.hardware
    }
    pub fn language(&self) -> u64 {
        self.language
    }
    pub fn terminal(&self) -> u64 {
        self.terminal
    }
    pub fn premise_profile(&self) -> &'static str {
        "setup_only_normal_instruction_refinement"
    }
}
pub struct SetupStackInspection<'b, 'a> {
    emission: SetupEmissionView<'b>,
    machine: MachineInspection<'a>,
    joins: Vec<IdentityJoin>,
    leaves: Vec<ReturningSetupLeaf>,
    roots: Vec<RootEntry>,
    data: FrameData,
    bounds: Option<ConditionalSetupStackBounds>,
}
impl<'b, 'a> SetupStackInspection<'b, 'a> {
    pub fn emission(&self) -> &SetupEmissionView<'b> {
        &self.emission
    }
    pub fn machine(&self) -> &MachineInspection<'a> {
        &self.machine
    }
    pub fn joins(&self) -> &[IdentityJoin] {
        &self.joins
    }
    pub fn leaves(&self) -> &[ReturningSetupLeaf] {
        &self.leaves
    }
    pub fn roots(&self) -> &[RootEntry] {
        &self.roots
    }
    pub fn calls(&self) -> &[CallUse] {
        &self.data.calls
    }
    pub fn state(&self, word: WordId) -> Option<&State> {
        self.data.states.get(word).and_then(Option::as_deref)
    }
    pub fn contributions(&self) -> &[ContributionFrames] {
        &self.data.contributions
    }
    pub fn frontiers(&self) -> &[Frontier] {
        &self.data.frontiers
    }
    pub fn memory(&self) -> &[MemoryObservation] {
        &self.data.memory
    }
    pub fn returns(&self) -> &[ReturnEvidence] {
        &self.data.returns
    }
    pub fn counters(&self) -> Counters {
        self.data.counters
    }
    pub fn bounds(&self) -> Option<&ConditionalSetupStackBounds> {
        self.bounds.as_ref()
    }
    pub fn native_admitted(&self) -> bool {
        false
    }
    pub fn formal_native_correspondence(&self) -> bool {
        false
    }
    pub fn source_correspondence_established(&self) -> bool {
        false
    }
    pub fn stack_metadata_agreement(&self) -> bool {
        false
    }
}

fn fail(
    class: ErrorClass,
    stage: Stage,
    reason: &'static str,
    machine: &MachineInspection<'_>,
    word: Option<WordId>,
) -> FrameError {
    let mut e = error(class, stage, reason);
    e.word = word;
    e.contribution = word
        .and_then(|w| machine.instructions().get(w))
        .map(|w| w.contribution);
    e
}
fn require(
    ok: bool,
    stage: Stage,
    reason: &'static str,
    machine: &MachineInspection<'_>,
    word: WordId,
) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(fail(
            ErrorClass::Infrastructure,
            stage,
            reason,
            machine,
            Some(word),
        ))
    }
}
fn unsupported(
    stage: Stage,
    reason: &'static str,
    machine: &MachineInspection<'_>,
    word: WordId,
) -> FrameError {
    fail(ErrorClass::Unsupported, stage, reason, machine, Some(word))
}
fn charge(
    budget: &mut Budget,
    stage: Stage,
    machine: &MachineInspection<'_>,
    word: WordId,
) -> Result<()> {
    budget
        .row(stage)
        .map_err(|e| located(e, Site::of(machine.instructions()[word])))
}
fn role_index(role: SetupRole) -> usize {
    match role {
        SetupRole::Boot => 0,
        SetupRole::Hardware => 1,
        SetupRole::Language => 2,
    }
}
fn contribution_words(
    machine: &MachineInspection<'_>,
    contribution: ContributionId,
) -> Range<usize> {
    // M2 supplies contribution-contiguous instructions in exact text order.
    let words = machine.instructions();
    let first = words.partition_point(|w| w.contribution < contribution);
    let end = words.partition_point(|w| w.contribution <= contribution);
    first..end
}
fn joined(machine: &MachineInspection<'_>, symbol: &str, object: u8) -> Result<ContributionId> {
    let mut found = None;
    for (id, c) in machine.text().contributions().iter().enumerate() {
        if c.aliases.iter().any(|a| a.name == symbol) {
            let word = contribution_words(machine, id).start;
            require(
                c.object == object,
                Stage::SetupBind,
                "typed symbol has the wrong producer object",
                machine,
                word,
            )?;
            require(
                c.image_aliases.iter().any(|a| a.name == symbol),
                Stage::SetupBind,
                "typed object/image alias is missing",
                machine,
                word,
            )?;
            if found.replace(id).is_some() {
                return Err(unsupported(
                    Stage::SetupBind,
                    "typed symbol name has multiple coherent contributions",
                    machine,
                    word,
                ));
            }
        }
    }
    found.ok_or_else(|| {
        fail(
            ErrorClass::Infrastructure,
            Stage::SetupBind,
            "typed emitted symbol is missing",
            machine,
            None,
        )
    })
}
fn add_join(
    rows: &mut Vec<IdentityJoin>,
    row: IdentityJoin,
    machine: &MachineInspection<'_>,
    budget: &mut Budget,
) -> Result<()> {
    let word = contribution_words(machine, row.contribution).start;
    require(
        !rows.iter().any(|r| r.contribution == row.contribution),
        Stage::SetupBind,
        "distinct typed identities share a native contribution",
        machine,
        word,
    )?;
    charge(budget, Stage::SetupBind, machine, word)?;
    rows.push(row);
    Ok(())
}
struct Bound {
    joins: Vec<IdentityJoin>,
    roles: [ContributionId; 3],
    thunks: [ContributionId; 3],
}
fn bind(
    view: &SetupEmissionView<'_>,
    machine: &MachineInspection<'_>,
    budget: &mut Budget,
) -> Result<Bound> {
    if view.primitives().len() != 3 || view.helper_count() != 0 {
        return Err(invariant(
            Stage::SetupBind,
            "opaque setup inventory exceeds the fixed profile",
        ));
    }
    let mut joins = Vec::new();
    let mut roles = [usize::MAX; 3];
    let mut thunks = [usize::MAX; 3];
    for row in view.functions() {
        let i = role_index(row.role());
        let contribution = joined(machine, row.symbol(), 1)?;
        roles[i] = contribution;
        add_join(
            &mut joins,
            IdentityJoin {
                contribution,
                source_function: row.id(),
                role: Some(row.role()),
                primitive: None,
                entry_thunk: false,
            },
            machine,
            budget,
        )?;
    }
    for row in view.primitives() {
        let contribution = joined(machine, row.symbol(), 1)?;
        add_join(
            &mut joins,
            IdentityJoin {
                contribution,
                source_function: row.id(),
                role: None,
                primitive: Some(row.operation()),
                entry_thunk: false,
            },
            machine,
            budget,
        )?;
    }
    for row in view.abi() {
        let i = role_index(row.role());
        let contribution = joined(machine, row.symbol(), 0)?;
        thunks[i] = contribution;
        let word = contribution_words(machine, contribution).start;
        require(
            view.functions()
                .iter()
                .any(|f| f.role() == row.role() && f.id() == row.function())
                && row.stack() == usize::from(i != 0),
            Stage::SetupBind,
            "opaque setup ABI identity is inconsistent",
            machine,
            word,
        )?;
        add_join(
            &mut joins,
            IdentityJoin {
                contribution,
                source_function: row.function(),
                role: Some(row.role()),
                primitive: None,
                entry_thunk: true,
            },
            machine,
            budget,
        )?;
    }
    // Complete privileged-site ownership precedes every coverage7 shape/alias result.
    let mut counts = [0_usize; 9];
    for &word in machine.csr_sites() {
        budget
            .evaluation(Stage::SetupBind)
            .map_err(|e| located(e, Site::of(machine.instructions()[word])))?;
        let instruction = machine.instructions()[word];
        let decoded = ordinary(instruction, Stage::SetupBind)?;
        let Some((index, row)) = joins
            .iter()
            .enumerate()
            .find(|(_, r)| r.contribution == instruction.contribution)
        else {
            return Err(fail(
                ErrorClass::Infrastructure,
                Stage::SetupBind,
                "CSR is outside a typed setup leaf or hardware entry",
                machine,
                Some(word),
            ));
        };
        counts[index] += 1;
        if let Some(operation) = row.primitive {
            require(
                csr_matches(instruction, operation).is_some(),
                Stage::SetupLeaf,
                "CSR contradicts the typed setup operation",
                machine,
                word,
            )?;
            require(
                counts[index] == 1,
                Stage::SetupLeaf,
                "extra CSR in setup leaf",
                machine,
                word,
            )?;
        } else if row.entry_thunk && row.role == Some(SetupRole::Hardware) {
            let offset = word - contribution_words(machine, row.contribution).start;
            let expected = [(10, 0x142), (11, 0x141), (12, 0x143)].get(offset).copied();
            require(
                expected.is_some_and(|(rd, csr)| {
                    decoded.operation == Op::Csrrs
                        && decoded.operands
                            == Operands::Csr {
                                rd,
                                csr,
                                source: CsrSource::Register(0),
                            }
                        && decoded.effect
                            == Effect::Csr {
                                reads: true,
                                writes: false,
                            }
                }),
                Stage::SetupRoot,
                "hardware entry capture contradicts its ABI",
                machine,
                word,
            )?;
        } else {
            return Err(fail(
                ErrorClass::Infrastructure,
                Stage::SetupBind,
                "CSR is outside a typed setup leaf or hardware entry",
                machine,
                Some(word),
            ));
        }
    }
    for (index, row) in joins.iter().enumerate() {
        let word = contribution_words(machine, row.contribution).start;
        if row.primitive.is_some() {
            require(
                counts[index] == 1,
                Stage::SetupLeaf,
                "typed setup leaf lacks its CSR",
                machine,
                word,
            )?;
        } else if row.entry_thunk && row.role == Some(SetupRole::Hardware) {
            require(
                counts[index] == 3,
                Stage::SetupRoot,
                "hardware entry capture contradicts its ABI",
                machine,
                word,
            )?;
        }
    }
    if let Some(&word) = machine.fence_sites().first() {
        return Err(fail(
            ErrorClass::Infrastructure,
            Stage::SetupBind,
            "fence is outside the setup-only profile",
            machine,
            Some(word),
        ));
    }
    for transfer in machine.transfers() {
        let caller = machine.instructions()[transfer.source].contribution;
        let Some(caller_row) = joins.iter().find(|r| r.contribution == caller) else {
            continue;
        };
        if caller_row.role.is_some() && !caller_row.entry_thunk {
            let target = joins
                .iter()
                .find(|r| r.contribution == transfer.target_contribution);
            require(
                target.is_some_and(|r| r.primitive.is_some()),
                Stage::SetupBind,
                "role body transfers to a role or root thunk",
                machine,
                transfer.source,
            )?;
            let definition = view
                .functions()
                .iter()
                .find(|f| f.id() == caller_row.source_function)
                .ok_or_else(|| invariant(Stage::SetupBind, "missing held role definition"))?;
            require(
                definition.effects().contains(&0),
                Stage::SetupBind,
                "role call lacks its typed machine authority",
                machine,
                transfer.source,
            )?;
        }
    }
    // Detect distinct-role collisions before classifying otherwise legal alias forms.
    for row in &joins {
        let c = &machine.text().contributions()[row.contribution];
        if c.aliases.len() != 1 || c.image_aliases.len() != 1 {
            return Err(unsupported(
                Stage::SetupBind,
                "setup identity does not implement additional exact aliases",
                machine,
                contribution_words(machine, row.contribution).start,
            ));
        }
    }
    if joins.len() != machine.text().contributions().len() {
        let c = (0..machine.text().contributions().len())
            .find(|c| !joins.iter().any(|r| r.contribution == *c))
            .ok_or_else(|| {
                fail(
                    ErrorClass::Infrastructure,
                    Stage::SetupBind,
                    "setup contribution count changed",
                    machine,
                    None,
                )
            })?;
        return Err(unsupported(
            Stage::SetupBind,
            "additional native contribution is not implemented by setup analysis",
            machine,
            contribution_words(machine, c).start,
        ));
    }
    Ok(Bound {
        joins,
        roles,
        thunks,
    })
}

pub(super) struct LeafRule {
    contribution: ContributionId,
    operation: SetupOperation,
    csr: WordId,
    source: Option<u8>,
    hardware_entry: u64,
}
fn csr_matches(instruction: Instruction, operation: SetupOperation) -> Option<Option<u8>> {
    let decoded = instruction.ordinary()?;
    match (
        operation,
        decoded.operation,
        decoded.operands,
        decoded.effect,
    ) {
        (
            SetupOperation::ClearSstatusSie,
            Op::Csrrci,
            Operands::Csr {
                rd: 0,
                csr: 0x100,
                source: CsrSource::Immediate(2),
            },
            Effect::Csr {
                reads: true,
                writes: true,
            },
        ) => Some(None),
        (
            SetupOperation::WriteSieZero,
            Op::Csrrw,
            Operands::Csr {
                rd: 0,
                csr: 0x104,
                source: CsrSource::Register(0),
            },
            Effect::Csr {
                reads: false,
                writes: true,
            },
        ) => Some(None),
        (
            SetupOperation::InstallTrap { .. },
            Op::Csrrw,
            Operands::Csr {
                rd: 0,
                csr: 0x105,
                source: CsrSource::Register(r),
            },
            Effect::Csr {
                reads: false,
                writes: true,
            },
        ) => Some(Some(r)),
        _ => None,
    }
}
fn leaf_rule(
    machine: &MachineInspection<'_>,
    graph: &Graph,
    row: IdentityJoin,
    hardware_entry: u64,
    budget: &mut Budget,
) -> Result<LeafRule> {
    let range = contribution_words(machine, row.contribution);
    let operation = row
        .primitive
        .ok_or_else(|| invariant(Stage::SetupLeaf, "missing bound primitive"))?;
    let mut csr = None;
    let mut source = None;
    for word in range.clone() {
        budget
            .evaluation(Stage::SetupLeaf)
            .map_err(|e| located(e, Site::of(machine.instructions()[word])))?;
        let instruction = machine.instructions()[word];
        let decoded = ordinary(instruction, Stage::SetupLeaf)?;
        if matches!(decoded.effect, Effect::Csr { .. }) {
            let register = csr_matches(instruction, operation).ok_or_else(|| {
                fail(
                    ErrorClass::Infrastructure,
                    Stage::SetupLeaf,
                    "CSR contradicts the typed setup operation",
                    machine,
                    Some(word),
                )
            })?;
            require(
                csr.replace(word).is_none(),
                Stage::SetupLeaf,
                "extra CSR in setup leaf",
                machine,
                word,
            )?;
            source = register;
        }
    }
    let csr = csr.ok_or_else(|| {
        fail(
            ErrorClass::Infrastructure,
            Stage::SetupLeaf,
            "typed setup leaf lacks its CSR",
            machine,
            Some(range.start),
        )
    })?;
    // Complete ownership precedes every unsupported shape result, including dead code.
    for word in range.clone() {
        budget
            .evaluation(Stage::SetupLeaf)
            .map_err(|e| located(e, Site::of(machine.instructions()[word])))?;
        let instruction = machine.instructions()[word];
        let decoded = ordinary(instruction, Stage::SetupLeaf)?;
        let links = graph.links[word];
        if links.transfer.is_some() {
            return Err(unsupported(
                Stage::SetupLeaf,
                "nested or tail setup-leaf call is not implemented",
                machine,
                word,
            ));
        }
        if word + 1 == range.end {
            if !links.returns || links.local.iter().any(Option::is_some) {
                return Err(unsupported(
                    Stage::SetupLeaf,
                    "setup leaf has no final ordinary return",
                    machine,
                    word,
                ));
            }
        } else if links.returns
            || links.local != [Some(word + 1), None]
            || matches!(
                decoded.operands,
                Operands::Branch { .. } | Operands::Jump { .. } | Operands::Indirect { .. }
            )
        {
            return Err(unsupported(
                Stage::SetupLeaf,
                "setup leaf is not a complete straight-line body",
                machine,
                word,
            ));
        }
    }
    Ok(LeafRule {
        contribution: row.contribution,
        operation,
        csr,
        source,
        hardware_entry,
    })
}
pub(super) fn authorize_csr(
    instruction: Instruction,
    state: &State,
    rule: &LeafRule,
) -> Result<()> {
    if instruction.id != rule.csr || instruction.contribution != rule.contribution {
        return Err(located(
            invariant(Stage::SetupLeaf, "CSR lost its typed leaf identity"),
            Site::of(instruction),
        ));
    }
    if let Some(register) = rule.source {
        match state.registers[usize::from(register)] {
            Fact::Const(value) if value == rule.hardware_entry => {}
            Fact::Const(_) => {
                return Err(located(
                    invariant(
                        Stage::SetupLeaf,
                        "install-trap source is a different concrete address",
                    ),
                    Site::of(instruction),
                ));
            }
            _ => {
                return Err(located(
                    error(
                        ErrorClass::Unsupported,
                        Stage::SetupLeaf,
                        "install-trap source address is not established",
                    ),
                    Site::of(instruction),
                ));
            }
        }
    }
    Ok(())
}

pub(super) fn resume(
    machine: &MachineInspection<'_>,
    graph: &Graph,
    instruction: Instruction,
    state: &State,
    budget: &mut Budget,
    stage: Stage,
    leaves: &[ReturningSetupLeaf],
) -> Result<Option<Step>> {
    let transfer_id = graph.links[instruction.id].transfer.ok_or_else(|| {
        located(
            invariant(Stage::SetupResume, "missing call transfer"),
            Site::of(instruction),
        )
    })?;
    let transfer = machine.transfers()[transfer_id];
    if transfer.link_register != 1 {
        return Ok(None);
    }
    let Some((leaf_id, leaf)) = leaves
        .iter()
        .enumerate()
        .find(|(_, l)| l.contribution == transfer.target_contribution)
    else {
        return Ok(None);
    };
    let Some(pair_id) = transfer.pair else {
        return Ok(None);
    };
    let pair = machine.pairs()[pair_id];
    let Some(continuation) = graph.links[instruction.id].continuation else {
        return Ok(None);
    };
    let link_value = instruction.pc.checked_add(4).ok_or_else(|| {
        located(
            invariant(Stage::SetupResume, "call continuation address overflows"),
            Site::of(instruction),
        )
    })?;
    require(
        pair.second == instruction.id
            && pair.contribution == instruction.contribution
            && machine.instructions()[continuation].pc == link_value
            && machine.instructions()[continuation].contribution == instruction.contribution
            && transfer.target == graph.entries[leaf.contribution],
        Stage::SetupResume,
        "setup call pair or continuation identity changed",
        machine,
        instruction.id,
    )?;
    let Fact::EntrySpPlus(sp) = state.registers[2] else {
        return Ok(None);
    };
    if sp > 0 || sp % 16 != 0 {
        return Ok(None);
    }
    let combined_depth = (-i128::from(sp)) as u128 + u128::from(leaf.depth);
    let mut output = copied(state, budget, stage)?;
    for r in 1..32 {
        if r != 2 && CALLEE_SAVED & (1 << r) == 0 {
            output.registers[r] = Fact::Unknown;
        }
    }
    output.registers[0] = Fact::Const(0);
    output.registers[1] = Fact::Const(link_value);
    Ok(Some(Step::Continue(
        output,
        None,
        [Some(continuation), None],
        Some(CallUse {
            caller: instruction.id,
            target: leaf.contribution,
            transfer: transfer_id,
            pair: pair_id,
            continuation,
            link_value,
            caller_sp: sp,
            leaf: leaf_id,
            combined_depth,
        }),
    )))
}

fn stack_ranges(machine: &MachineInspection<'_>) -> Result<[Range<u64>; 2]> {
    let parsed = elf::read_structure(machine.text().inputs()[2], ArtifactKind::Image)
        .map_err(|e| error(e.class, Stage::SetupBind, e.reason))?;
    let get = |name| -> Result<Range<u64>> {
        let mut rows = parsed.sections.iter().filter(|s| s.name == name);
        let s = rows
            .next()
            .ok_or_else(|| invariant(Stage::SetupBind, "checked stack section is missing"))?;
        if rows.next().is_some() {
            return Err(invariant(
                Stage::SetupBind,
                "checked stack section is ambiguous",
            ));
        }
        let top = s
            .address
            .checked_add(s.size)
            .ok_or_else(|| invariant(Stage::SetupBind, "checked stack extent overflows"))?;
        Ok(s.address..top)
    };
    Ok([get(".boot_stack")?, get(".terminal_stack")?])
}
fn address_pair(
    machine: &MachineInspection<'_>,
    contribution: ContributionId,
    high: WordId,
    low: WordId,
    rd: u8,
    target: u64,
) -> Result<()> {
    let words = machine.instructions();
    let h = words[high];
    let l = words[low];
    let hd = ordinary(h, Stage::SetupRoot)?;
    let ld = ordinary(l, Stage::SetupRoot)?;
    let c = &machine.text().contributions()[contribution];
    let valid_shape = matches!(hd.operands, Operands::Upper { rd: r, .. } if r == rd)
        && hd.operation == Op::Auipc
        && matches!(ld.operands, Operands::Immediate { rd: r, rs1, .. } if r == rd && rs1 == rd)
        && ld.operation == Op::Addi;
    require(
        valid_shape,
        Stage::SetupRoot,
        "root stack address has the wrong instruction shape",
        machine,
        high,
    )?;
    let hp = c
        .patches
        .iter()
        .find(|p| p.kind == 23 && p.offset == h.pc - c.image.value);
    let lp = c
        .patches
        .iter()
        .find(|p| p.kind == 24 && p.offset == l.pc - c.image.value);
    require(
        hp.is_some() && lp.is_some(),
        Stage::SetupRoot,
        "root stack address lacks exact high/low relocation evidence",
        machine,
        high,
    )?;
    let (hp, lp) = (hp.unwrap(), lp.unwrap());
    require(
        hp.target == target
            && lp.target == target
            && hp.high_site == lp.high_site
            && hp.high_site == h.pc
            && hp.linked_words.as_slice() == [h.raw]
            && lp.linked_words.as_slice() == [l.raw],
        Stage::SetupRoot,
        "root stack relocation is not the checked reservation top",
        machine,
        high,
    )?;
    let Operands::Upper { immediate: hi, .. } = hd.operands else {
        return Err(invariant(Stage::SetupRoot, "root upper operand changed"));
    };
    let Operands::Immediate { immediate: lo, .. } = ld.operands else {
        return Err(invariant(Stage::SetupRoot, "root lower operand changed"));
    };
    require(
        i128::from(h.pc) + i128::from(hi) + i128::from(lo) == i128::from(target),
        Stage::SetupRoot,
        "root stack address arithmetic disagrees",
        machine,
        high,
    )
}
fn root_entry(
    machine: &MachineInspection<'_>,
    graph: &Graph,
    role: SetupRole,
    contribution: ContributionId,
    target: ContributionId,
    stack: Range<u64>,
    budget: &mut Budget,
) -> Result<RootEntry> {
    let range = contribution_words(machine, contribution);
    let words = machine.instructions();
    let stage = Stage::SetupRoot;
    let prefix = match role {
        SetupRole::Boot => 0,
        SetupRole::Hardware => 3,
        SetupRole::Language => 1,
    };
    // Closed grammar, derived from the held ABI kind; no fixture instruction addresses.
    require(
        range.len() == prefix + 5,
        stage,
        "root thunk has extra or missing instructions",
        machine,
        range.start,
    )?;
    for word in range.clone() {
        budget
            .evaluation(stage)
            .map_err(|e| located(e, Site::of(words[word])))?;
    }
    if role == SetupRole::Hardware {
        for (offset, (rd, csr)) in [(10, 0x142), (11, 0x141), (12, 0x143)]
            .into_iter()
            .enumerate()
        {
            let i = words[range.start + offset];
            require(
                ordinary(i, stage)?.operation == Op::Csrrs
                    && ordinary(i, stage)?.operands
                        == Operands::Csr {
                            rd,
                            csr,
                            source: CsrSource::Register(0),
                        }
                    && ordinary(i, stage)?.effect
                        == Effect::Csr {
                            reads: true,
                            writes: false,
                        },
                stage,
                "hardware entry capture contradicts its ABI",
                machine,
                i.id,
            )?;
        }
    } else if role == SetupRole::Language {
        let i = words[range.start];
        require(
            ordinary(i, stage)?.operation == Op::Andi
                && ordinary(i, stage)?.operands
                    == Operands::Immediate {
                        rd: 10,
                        rs1: 10,
                        immediate: 255,
                    },
            stage,
            "language entry does not preserve the u8 trap tag",
            machine,
            i.id,
        )?;
    }
    for word in range.clone() {
        if matches!(ordinary(words[word], stage)?.effect, Effect::Csr { .. }) {
            require(
                role == SetupRole::Hardware && word < range.start + prefix,
                stage,
                "extra CSR in root thunk",
                machine,
                word,
            )?;
        }
    }
    let high = range.start + prefix;
    address_pair(machine, contribution, high, high + 1, 2, stack.end)?;
    let align = words[high + 2];
    require(
        ordinary(align, stage)?.operation == Op::Andi
            && ordinary(align, stage)?.operands
                == Operands::Immediate {
                    rd: 2,
                    rs1: 2,
                    immediate: -16,
                }
            && stack.end.is_multiple_of(16),
        stage,
        "root stack alignment contradicts its ABI",
        machine,
        align.id,
    )?;
    let tail = range.end - 1;
    let transfer_id = graph.links[tail].transfer.ok_or_else(|| {
        fail(
            ErrorClass::Infrastructure,
            stage,
            "root lacks a final nonlinking role transfer",
            machine,
            Some(tail),
        )
    })?;
    let transfer = machine.transfers()[transfer_id];
    let pair_id = transfer.pair.ok_or_else(|| {
        unsupported(
            stage,
            "unpaired root tail is not implemented",
            machine,
            tail,
        )
    })?;
    let pair = machine.pairs()[pair_id];
    require(
        transfer.link_register == 0
            && transfer.target_contribution == target
            && transfer.target == graph.entries[target]
            && pair.first == tail - 1
            && pair.second == tail
            && pair.contribution == contribution
            && graph.links[tail].continuation.is_none(),
        stage,
        "root tail links or targets a different role",
        machine,
        tail,
    )?;
    let scratch = match ordinary(words[tail - 1], stage)?.operands {
        Operands::Upper { rd, .. } => rd,
        _ => {
            return Err(fail(
                ErrorClass::Infrastructure,
                stage,
                "root tail lacks its AUIPC",
                machine,
                Some(tail - 1),
            ));
        }
    };
    let args = match role {
        SetupRole::Boot => (1 << 10) | (1 << 11),
        SetupRole::Hardware => (1 << 10) | (1 << 11) | (1 << 12),
        SetupRole::Language => 1 << 10,
    };
    require(
        scratch != 2 && args & (1 << scratch) == 0,
        stage,
        "root tail clobbers its stack or role argument",
        machine,
        tail - 1,
    )?;
    for word in range.clone() {
        let links = graph.links[word];
        if word == tail {
            require(
                links.local == [None, None] && !links.returns,
                stage,
                "root tail has a fallthrough or return",
                machine,
                word,
            )?;
        } else {
            require(
                links.local == [Some(word + 1), None] && links.transfer.is_none() && !links.returns,
                stage,
                "root prefix is not complete and linear",
                machine,
                word,
            )?;
        }
        require(
            !matches!(
                ordinary(words[word], stage)?.effect,
                Effect::Load { .. } | Effect::Store { .. } | Effect::Fence
            ),
            stage,
            "root thunk touches memory or fence",
            machine,
            word,
        )?;
    }
    let patches = &machine.text().contributions()[contribution].patches;
    require(
        patches.len() == 3,
        stage,
        "root thunk has extra relocation sites",
        machine,
        range.start,
    )?;
    charge(budget, stage, machine, range.start)?;
    Ok(RootEntry {
        role,
        contribution,
        target,
        stack,
        tail,
        pair: pair_id,
    })
}

pub fn inspect_setup_stacks<'b, 'a>(
    bundle: &'b Bundle,
    machine: MachineInspection<'a>,
) -> Result<SetupStackInspection<'b, 'a>> {
    require_ordinary(&machine, Stage::SetupBind)?;
    let emission = bundle.setup_identity().map_err(|_| {
        error(
            ErrorClass::Unsupported,
            Stage::SetupBind,
            "bundle is outside the setup-only emission profile",
        )
    })?;
    let mut budget = budget(&machine);
    let bound = bind(&emission, &machine, &mut budget)?;
    let stacks = stack_ranges(&machine)?;
    let mut engine = Engine::new(&machine, budget)?;
    let mut roots = Vec::new();
    for role in [SetupRole::Boot, SetupRole::Hardware, SetupRole::Language] {
        let i = role_index(role);
        roots.push(root_entry(
            &machine,
            &engine.graph,
            role,
            bound.thunks[i],
            bound.roles[i],
            stacks[usize::from(i != 0)].clone(),
            &mut engine.budget,
        )?);
    }
    let hardware_entry = machine.text().contributions()[bound.thunks[1]].image.value;
    let mut leaves = Vec::new();
    // Fixed contribution order, not primitive source order or caller-controlled order.
    for contribution in 0..machine.text().contributions().len() {
        let Some(&row) = bound
            .joins
            .iter()
            .find(|r| r.contribution == contribution && r.primitive.is_some())
        else {
            continue;
        };
        let rule = leaf_rule(
            &machine,
            &engine.graph,
            row,
            hardware_entry,
            &mut engine.budget,
        )?;
        engine.worklist(contribution, Policy::Leaf(&rule))?;
        engine.finish(contribution, Policy::Leaf(&rule))?;
        let frame = engine
            .contributions
            .last()
            .ok_or_else(|| invariant(Stage::SetupLeaf, "missing completed setup leaf"))?;
        let range = contribution_words(&machine, contribution);
        let Some(summary) = frame.local_return_summary() else {
            let word = engine
                .frontiers
                .get(frame.frontier_indices.start)
                .map(|f| f.word)
                .unwrap_or(range.start);
            return Err(unsupported(
                Stage::SetupLeaf,
                "setup leaf frame/ordinary return is not established",
                &machine,
                word,
            ));
        };
        if frame.covered_words != range.len() || frame.return_indices.len() != 1 {
            return Err(unsupported(
                Stage::SetupLeaf,
                "setup leaf does not cover its complete body and single return",
                &machine,
                range.start,
            ));
        }
        let depth = summary.local_depth_bound();
        let return_word = engine.returns[frame.return_indices.start].word;
        charge(&mut engine.budget, Stage::SetupLeaf, &machine, range.start)?;
        leaves.push(ReturningSetupLeaf {
            contribution,
            operation: rule.operation,
            csr: rule.csr,
            return_word,
            depth,
        });
    }
    for contribution in bound.roles {
        engine.worklist(contribution, Policy::Role(&leaves))?;
        engine.finish(contribution, Policy::Role(&leaves))?;
    }
    let data = engine.into_data()?;
    let mut peaks = [0_u64; 3];
    let mut complete = true;
    for root in &roots {
        let frame = data
            .contributions
            .iter()
            .find(|f| f.contribution == root.target)
            .ok_or_else(|| invariant(Stage::SetupRoot, "missing completed root body"))?;
        let capacity = u128::from(root.stack.end) - u128::from(root.stack.start);
        let mut peak = 0_u128;
        // Only final-rooted retained states/calls can demonstrate a capacity contradiction.
        // Partial coverage does not erase a known earlier violation.
        for instruction in machine
            .instructions()
            .iter()
            .filter(|w| w.contribution == root.target)
        {
            if let Some(state) = data.states[instruction.id].as_deref()
                && let Fact::EntrySpPlus(offset) = state.registers[2]
                && offset <= 0
            {
                let depth = (-i128::from(offset)) as u128;
                require(
                    depth <= capacity && depth <= u128::from(root.stack.end),
                    Stage::SetupRoot,
                    "root stack bound exceeds its actual reservation or wraps",
                    &machine,
                    instruction.id,
                )?;
                peak = peak.max(depth);
            }
        }
        for call in &data.calls {
            if machine.instructions()[call.caller].contribution == root.target {
                require(
                    call.combined_depth <= capacity
                        && call.combined_depth <= u128::from(root.stack.end),
                    Stage::SetupRoot,
                    "root call stack bound exceeds its actual reservation or wraps",
                    &machine,
                    call.caller,
                )?;
                peak = peak.max(call.combined_depth);
            }
        }
        if frame.local_depth_bound().is_none() {
            complete = false;
        }
        peaks[role_index(root.role)] = u64::try_from(peak)
            .map_err(|_| invariant(Stage::SetupRoot, "bounded root peak cannot narrow"))?;
    }
    let bounds = complete.then(|| ConditionalSetupStackBounds {
        boot: peaks[0],
        hardware: peaks[1],
        language: peaks[2],
        terminal: peaks[1].max(peaks[2]),
    });
    Ok(SetupStackInspection {
        emission,
        machine,
        joins: bound.joins,
        leaves,
        roots,
        data,
        bounds,
    })
}
