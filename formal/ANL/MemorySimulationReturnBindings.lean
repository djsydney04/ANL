import ANL.MemorySimulationContext

namespace ANL.Memory.Simulation
open Lowering

theorem return_bindValue
    (lowered : term offset (.value input :: locals) ids body start = some (fragment, nextSupply))
    (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures)
    (placed : Placed p (KontCode.bindValue lowered code) before after a b)
    (atResult : AtResult b v (.captured input (plug fragment.instructions tail) mk) ctrl targetKont) :
    Matched p q responses ⟨.ret v, a, .bind false body :: k, w⟩ ⟨ctrl, b, targetKont, w⟩
      ⟨.eval body, {a with env := v :: a.env}, .scope :: k, w⟩ := by
  cases atResult with
  | captured found =>
      have facts := (KontCode.bindValue lowered code).store_facts placed.storage
      have beforeStart := placed.range.trans placed.limits.1
      let continuation := KontCode.scopeValue (value := input) code
      have nextPlaced : Placed p continuation before nextSupply {a with env := v :: a.env} b :=
        ⟨beforeStart.trans (term_supply lowered),
          ⟨facts.1.pushValue found, facts.2.1, facts.2.2, placed.storage.2.2.2⟩,
          placed.limits.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      exact Matched.silent CoreSilent.bindValue
        (Related.eval continuation lowered placed.sites.1
          (nextPlaced.raise_before beforeStart (term_supply lowered)))

theorem return_scopeValue
    (code : KontCode offset locals ids k result captures)
    (placed : Placed p (KontCode.scopeValue (value := input) code) before after a b)
    (atResult : AtResult b v result ctrl targetKont) (env : a.env = prior :: rest) :
    Matched p q responses ⟨.ret v, a, .scope :: k, w⟩ ⟨ctrl, b, targetKont, w⟩
      ⟨.ret v, {a with env := rest}, k, w⟩ := by
  have parentPlaced : Placed p code before after {a with env := rest} b := by
    refine ⟨placed.range, ?_, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
    have stored : code.StoreSafe before {a with env := a.env.tail} b := placed.storage.2.2.2
    simpa only [env, List.tail_cons] using stored
  exact Matched.silent (CoreSilent.scopeReturn env) (Related.ret code parentPlaced atResult)

theorem return_scopeMutable
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.scopeMutable (slot := slot) code) before after a b)
    (atResult : AtResult b v (.returned (.slotScope slot.id :: mk)) ctrl targetKont)
    (env : a.env = prior :: rest) :
    Matched p q responses ⟨.ret v, a, .scope :: k, w⟩ ⟨ctrl, b, targetKont, w⟩
      ⟨.ret v, {a with env := rest}, k, w⟩ := by
  cases atResult
  have facts := (KontCode.scopeMutable (slot := slot) code).store_facts placed.storage
  have keys := facts.1.slotKeys
  cases slotsEq : b.slots with
  | nil => simp [slotsEq, mutableIds] at keys
  | cons pair slots =>
      rcases pair with ⟨rid, old⟩
      have ridEq : rid = slot.id := by simpa [slotsEq, mutableIds] using congrArg List.head? keys
      subst rid
      have parentPlaced : Placed p code before after {a with env := rest} {b with slots} := by
        refine ⟨placed.range, ?_, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
        have stored : code.StoreSafe before {a with env := a.env.tail} {b with slots := b.slots.tail} := placed.storage.2.2.2
        simpa only [env, slotsEq, List.tail_cons] using stored
      exact Matched.positive (.succ (Mir.Step.slotReturn slotsEq) .zero) (by decide)
        (Related.ret code parentPlaced .returned)

theorem return_bindMutable
    (lowered : term offset (.mutable slot :: locals) ids body start = some (fragment, nextSupply))
    (code : KontCode offset locals ids k (.captured d tail mk) captures)
    (placed : Placed p (KontCode.bindMutable (value := input) lowered code) before after a b)
    (atResult : AtResult b v (.captured input (.next d (.mutableScope slot input fragment.block) tail) mk)
      ctrl targetKont) :
    Matched p q responses ⟨.ret v, a, .bind true body :: k, w⟩ ⟨ctrl, b, targetKont, w⟩
      ⟨.eval body, {a with env := v :: a.env}, .scope :: k, w⟩ := by
  cases atResult with
  | captured found =>
      have facts := (KontCode.bindMutable (value := input) lowered code).store_facts placed.storage
      have fresh : before.nextSlot ≤ slot.id := Nat.le_trans placed.range.2 placed.limits.2.1
      have slotBound : slot.id < start.nextSlot := by rw [placed.limits.2.2.1]; omega
      have beforeStart : SupplyLE before start :=
        ⟨Nat.le_trans placed.range.1 placed.limits.1, Nat.le_trans fresh (Nat.le_of_lt slotBound)⟩
      have parentStorage := code.store_weaken placed.storage.2.2.2 beforeStart
      have parentFacts := code.store_facts parentStorage
      have destinationStorage : (KontCode.destination code).StoreSafe start a b :=
        ⟨parentFacts.1, parentFacts.2.1, parentFacts.2.2, parentStorage⟩
      let continuation := KontCode.scopeMutable (slot := slot) (KontCode.destination code)
      have nextPlaced : Placed p continuation start nextSupply
          {a with env := v :: a.env} {b with slots := (slot.id, v) :: b.slots} :=
        ⟨term_supply lowered,
          ⟨facts.1.pushSlot facts.2.1 fresh, facts.2.1.pushSlot beforeStart slotBound,
            facts.2.2.pushSlot, destinationStorage⟩,
          placed.limits.2.2.2, placed.offsets, placed.sites.2, placed.currentOffset⟩
      obtain ⟨last, path, related⟩ := enter_block (world := w) nextPlaced lowered (SupplyLE.refl _) placed.sites.1
      exact Matched.positive (.succ Mir.Step.instruction (.succ (Mir.Step.mutableFound found) path)) (by decide) related

end ANL.Memory.Simulation
