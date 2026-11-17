import ANL.MemorySimulationMatch
import ANL.MemorySimulationSites

namespace ANL.Memory.Simulation
open Lowering

theorem return_binaryLeft (notAnd : op ≠ .and) (notOr : op ≠ .or)
    (lowered : term offset locals ids right start = some (fragment, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.binaryLeft (left := left) notAnd notOr lowered code) before after a b)
    (atResult : AtResult b v (.captured left
      (plug fragment.instructions (.next d (.binary op left fragment.value) tail)) mk) ctrl actualKont)
    (notShort : APL.FlatProducts.shortCircuit op v = false) :
    Matched p q responses ⟨.ret v, a, .left op right :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.eval right, a, .right op v :: k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have facts := code.store_facts placed.storage.2.2.2
      have captured : CapturesHold b (.value left v :: captures) := by
        intro capture membership
        rcases List.mem_cons.mp membership with rfl | membership
        · exact lookup
        · exact facts.2.2 _ membership
      let continuation := KontCode.binaryRight (prior := v) (value := fragment.value) (left := left) notAnd notOr code
      have continued : Placed p continuation before next a b :=
        ⟨le.trans (term_supply lowered), ⟨facts.1, facts.2.1, captured, placed.storage.2.2.2⟩,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      apply Matched.silent (.rightEval notShort)
      exact Related.eval continuation lowered placed.sites.1 (continued.raise_before le (term_supply lowered))

theorem return_branch_true
    (yesLowered : term offset locals ids yes start = some (left, middle))
    (noLowered : term offset locals ids no middle = some (right, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.branch (condition := condition) yesLowered noLowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool true))
      (.captured condition (.next d (.branch condition left.block right.block) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool true)), a, .ifF yes no :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.eval yes, a, k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before next a b :=
        ⟨(le.trans (term_supply yesLowered)).trans (term_supply noLowered), placed.storage,
          placed.limits.2, placed.offsets, placed.sites.2.2, placed.currentOffset⟩
      obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
        destination yesLowered le placed.sites.1
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.branchTrue lookup) entered))
        (by decide) related

theorem return_branch_false
    (yesLowered : term offset locals ids yes start = some (left, middle))
    (noLowered : term offset locals ids no middle = some (right, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.branch (condition := condition) yesLowered noLowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool false))
      (.captured condition (.next d (.branch condition left.block right.block) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool false)), a, .ifF yes no :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.eval no, a, k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before middle := (placed.range.trans placed.limits.1).trans (term_supply yesLowered)
      have destination : Placed p (KontCode.destination code) before next a b :=
        ⟨le.trans (term_supply noLowered), placed.storage,
          placed.limits.2, placed.offsets, placed.sites.2.2, placed.currentOffset⟩
      obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
        destination noLowered le placed.sites.2.1
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.branchFalse lookup) entered))
        (by decide) related

theorem return_condition_true
    (conditionLowered : term offset locals ids condition start = some (cf, middle))
    (bodyLowered : term offset locals ids body middle = some (bf, next))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.condition conditionLowered bodyLowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool true)) (.returned (.condition cf.block bf.block :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool true)), a, .condition condition body :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.eval body, a, .body condition body :: k, w⟩ := by
  cases atResult
  have continued : Placed p (KontCode.body conditionLowered bodyLowered code) before after a b :=
    ⟨placed.range, placed.storage, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
  have le : SupplyLE before middle := (placed.range.trans placed.limits.1).trans (term_supply conditionLowered)
  obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
    continued bodyLowered le placed.sites.2.1
  exact Matched.positive (.succ Mir.Step.whileTrue entered) (by decide) related

theorem return_condition_false
    (conditionLowered : term offset locals ids condition start = some (cf, middle))
    (bodyLowered : term offset locals ids body middle = some (bf, next))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.condition conditionLowered bodyLowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool false)) (.returned (.condition cf.block bf.block :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool false)), a, .condition condition body :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.ret (.scalar .unit), a, k, w⟩ := by
  cases atResult
  have le : SupplyLE before next := ((placed.range.trans placed.limits.1).trans
    (term_supply conditionLowered)).trans (term_supply bodyLowered)
  have parent : Placed p code before next a b :=
    ⟨le, placed.storage.2.2.2, placed.limits.2, placed.offsets, placed.sites.2.2, placed.currentOffset⟩
  exact Matched.positive (.succ Mir.Step.whileFalse .zero) (by decide) (Related.ret code parent .returned)

theorem return_body_again
    (conditionLowered : term offset locals ids condition start = some (cf, middle))
    (bodyLowered : term offset locals ids body middle = some (bf, next))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.body conditionLowered bodyLowered code) before after a b)
    (atResult : AtResult b (.scalar .unit) (.returned (.body cf.block bf.block :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar .unit), a, .body condition body :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.eval condition, a, .condition condition body :: k, w⟩ := by
  cases atResult
  have continued : Placed p (KontCode.condition conditionLowered bodyLowered code) before after a b :=
    ⟨placed.range, placed.storage, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
  have le : SupplyLE before start := placed.range.trans placed.limits.1
  obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
    continued conditionLowered le placed.sites.1
  exact Matched.positive (.succ Mir.Step.whileAgain entered) (by decide) related

private theorem logical_placed {op : APL.BOp} {prior : Val}
    (logical : (op = .and ∧ prior = .scalar (.bool true)) ∨
      (op = .or ∧ prior = .scalar (.bool false)))
    {code : KontCode offset locals ids k result captures}
    (placed : Placed p code before after a b) :
    Placed p (KontCode.logicalRight logical code) before after a b := by
  have facts := code.store_facts placed.storage
  exact ⟨placed.range, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
    placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩

private theorem enter_yield {code : KontCode offset locals ids k (.returned mk) captures}
    (placed : Placed p code before after a b) (lookup : b.temp temp = some v) :
    ∃ last, MirStepsN q responses 1 ⟨.block (.yield temp), b, mk, w⟩ last ∧
      Related p ⟨.ret v, a, k, w⟩ last := by
  refine ⟨_, .succ Mir.Step.block .zero, ?_⟩
  exact Related.ret (KontCode.yield (KontCode.blockEnd placed.snapshot code))
    (placed.blockEnd.yield (value := temp)) (.captured lookup)

theorem return_andLeft_true
    (lowered : term offset locals ids right start = some (fragment, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.andLeft (left := left) lowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool true))
      (.captured left (.next d (.branch left fragment.block (.yield left)) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool true)), a, .left .and right :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.eval right, a, .right .and (.scalar (.bool true)) :: k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before next a b :=
        ⟨le.trans (term_supply lowered), placed.storage,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      have continued := logical_placed (Or.inl ⟨rfl, rfl⟩) destination
      obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
        continued lowered le placed.sites.1
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.branchTrue lookup) entered))
        (by decide) related

theorem return_andLeft_false
    (lowered : term offset locals ids right start = some (fragment, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.andLeft (left := left) lowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool false))
      (.captured left (.next d (.branch left fragment.block (.yield left)) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool false)), a, .left .and right :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.ret (.scalar (.bool false)), a, k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before next a b :=
        ⟨le.trans (term_supply lowered), placed.storage,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      obtain ⟨last, entered, related⟩ := enter_yield (q := q) (responses := responses) (w := w) destination lookup
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.branchFalse lookup) entered))
        (by decide) related

theorem return_orLeft_true
    (lowered : term offset locals ids right start = some (fragment, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.orLeft (left := left) lowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool true))
      (.captured left (.next d (.branch left (.yield left) fragment.block) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool true)), a, .left .or right :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.ret (.scalar (.bool true)), a, k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before next a b :=
        ⟨le.trans (term_supply lowered), placed.storage,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      obtain ⟨last, entered, related⟩ := enter_yield (q := q) (responses := responses) (w := w) destination lookup
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.branchTrue lookup) entered))
        (by decide) related

theorem return_orLeft_false
    (lowered : term offset locals ids right start = some (fragment, next))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.orLeft (left := left) lowered code) before after a b)
    (atResult : AtResult b (.scalar (.bool false))
      (.captured left (.next d (.branch left (.yield left) fragment.block) tail) mk) ctrl actualKont) :
    Matched p q responses ⟨.ret (.scalar (.bool false)), a, .left .or right :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.eval right, a, .right .or (.scalar (.bool false)) :: k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have le : SupplyLE before start := placed.range.trans placed.limits.1
      have destination : Placed p (KontCode.destination code) before next a b :=
        ⟨le.trans (term_supply lowered), placed.storage,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      have continued := logical_placed (Or.inr ⟨rfl, rfl⟩) destination
      obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
        continued lowered le placed.sites.1
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.branchFalse lookup) entered))
        (by decide) related

end ANL.Memory.Simulation
