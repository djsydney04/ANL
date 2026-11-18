import ANL.WordsSimulationMatch

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

theorem return_convert
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.convert (mode := mode) (target := target) (value := operand) code) before after a b)
    (atResult : AtResult b v (.captured operand (.next d (.convert mode target operand) tail) mk) ctrl actualKont)
    (valid : ANL.Words.convert mode target v ≠ .invalid) :
    Matched p q responses ⟨.ret v, a, .convert mode target :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      (ANL.Words.resume (ANL.Words.convert mode target v) a k w) := by
  cases atResult with
  | captured lookup =>
      have destination : Placed p (KontCode.destination code) before after a b :=
        ⟨placed.range, placed.storage, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.convertFound lookup) .zero)) (by decide)
      exact resume_related destination valid

theorem return_unary
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.unary (op := op) (value := operand) code) before after a b)
    (atResult : AtResult b v (.captured operand (.next d (.unary op operand) tail) mk) ctrl actualKont)
    (valid : ANL.Words.unary op v ≠ .invalid) :
    Matched p q responses ⟨.ret v, a, .unary op :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      (ANL.Words.resume (ANL.Words.unary op v) a k w) := by
  cases atResult with
  | captured lookup =>
      have destination : Placed p (KontCode.destination code) before after a b :=
        ⟨placed.range, placed.storage, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.unaryFound lookup) .zero)) (by decide)
      exact resume_related destination valid

theorem return_project
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.project (index := index) (value := operand) code) before after a b)
    (atResult : AtResult b v (.captured operand (.next d (.project operand index) tail) mk) ctrl actualKont)
    (valid : ANL.Words.project v index ≠ .invalid) :
    Matched p q responses ⟨.ret v, a, .project index :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      (ANL.Words.resume (ANL.Words.project v index) a k w) := by
  cases atResult with
  | captured lookup =>
      have destination : Placed p (KontCode.destination code) before after a b :=
        ⟨placed.range, placed.storage, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.projectFound lookup) .zero)) (by decide)
      exact resume_related destination valid

theorem return_binaryRight (notAnd : op ≠ (.legacy .and)) (notOr : op ≠ (.legacy .or))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.binaryRight (prior := prior) (value := operand) (left := left)
      notAnd notOr code) before after a b)
    (atResult : AtResult b v (.captured operand (.next d (.binary op left operand) tail) mk) ctrl actualKont)
    (valid : ANL.Words.binary op prior v ≠ .invalid) :
    Matched p q responses ⟨.ret v, a, .right op prior :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      (ANL.Words.resume (ANL.Words.binary op prior v) a k w) := by
  cases atResult with
  | captured lookup =>
      have leftLookup : b.temp left = some prior := placed.storage.2.2.1 (.value left prior) (.head _)
      have paired : b.pair left operand = some (prior, v) := by
        simp [Mir.Activation.pair, leftLookup, lookup]
      have facts := code.store_facts placed.storage.2.2.2
      have destination : Placed p (KontCode.destination code) before after a b :=
        ⟨placed.range, ⟨facts.1, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.binaryFound paired) .zero)) (by decide)
      exact resume_related destination valid

theorem return_assign
    (localLookup : locals[index]? = some (.mutable slot))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.assign (value := operand) localLookup code) before after a b)
    (atResult : AtResult b v (.captured operand (.next d (.store slot operand) tail) mk) ctrl actualKont)
    (assigned : ANL.Words.update a.env index v = some env) :
    Matched p q responses ⟨.ret v, a, .assign index :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      ⟨.ret (.scalar (.legacy .unit)), {a with env}, k, w⟩ := by
  cases atResult with
  | captured lookup =>
      have facts := code.store_facts placed.storage.2.2.2
      obtain ⟨prior, _, slotLookup⟩ := facts.1.values.lookup localLookup
      obtain ⟨slots, updated⟩ := updateId_exists (value := v) slotLookup
      have unique : (b.slots.map Prod.fst).Nodup := by rw [facts.1.slotKeys]; exact facts.1.slots
      have slotsEq := updateId_eq_replace updated unique
      have envEq : env = replaceLocals locals slot.id v a.env :=
        Option.some.inj (assigned.symm.trans (facts.1.values.assignment facts.1.slots localLookup))
      cases slotsEq
      cases envEq
      have storage := code.store_replace (rid := slot.id) (v := v) placed.storage.2.2.2
      have changed := code.store_facts storage
      have destination : Placed p (KontCode.destination code) before after
          {a with env := replaceLocals locals slot.id v a.env}
          {b with slots := replaceSlot slot.id v b.slots} :=
        ⟨placed.range, ⟨changed.1, changed.2.1, changed.2.2, storage⟩,
          placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      apply Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.storeSlot lookup updated) .zero)) (by decide)
      exact Related.ret (KontCode.destination code) destination .returned

theorem return_logicalRight
    (logical : (op = (.legacy .and) ∧ prior = .scalar (.legacy (.bool true))) ∨
      (op = (.legacy .or) ∧ prior = .scalar (.legacy (.bool false))))
    (code : KontCode offset locals ids k result captures)
    (placed : Placed p (KontCode.logicalRight logical code) before after a b)
    (atResult : AtResult b v result ctrl actualKont)
    (valid : ANL.Words.binary op prior v ≠ .invalid) :
    Matched p q responses ⟨.ret v, a, .right op prior :: k, w⟩ ⟨ctrl, b, actualKont, w⟩
      (ANL.Words.resume (ANL.Words.binary op prior v) a k w) := by
  have identity : ANL.Words.binary op prior v = .value v := by
    rcases logical with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      cases v with
      | scalar value =>
          cases value with
          | legacy value => cases value <;> simp_all [ANL.Words.binary, APL.binary, legacyResult]
          | word value => simp [ANL.Words.binary] at valid
      | tuple values => simp [ANL.Words.binary] at valid
  have kind : op = (.legacy .and) ∨ op = (.legacy .or) := logical.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have parent : Placed p code before after a b :=
    ⟨placed.range, placed.storage.2.2.2, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
  rw [identity]
  exact Matched.silent (.logicalReturn identity kind) (Related.ret code parent atResult)

end ANL.Words.Simulation
