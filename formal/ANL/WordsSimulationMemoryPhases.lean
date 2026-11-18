import ANL.WordsSimulationResources

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

theorem readCheck_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.readCheck resource value, a, k, w⟩ ty)
    (step : Step p responses ⟨.readCheck resource value, a, k, w⟩ next)
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before after a b) :
    Matched p q responses ⟨.readCheck resource value, a, k, w⟩
      ⟨.readCheck (binding resource) value, b, mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | readChecked checked =>
      exact Matched.positive (.succ (Mir.Step.readChecked checked) .zero) (by decide) (.readCell code placed)
  | readBounds bounds =>
      exact Matched.positive (.succ (Mir.Step.readBounds bounds) .zero) (by decide) (.trap code placed)
  | readWrong => exact False.elim (nextTyped.not_invalid rfl)

theorem readCell_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.readCell resource index, a, k, w⟩ ty)
    (step : Step p responses ⟨.readCell resource index, a, k, w⟩ next)
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before after a b) :
    Matched p q responses ⟨.readCell resource index, a, k, w⟩
      ⟨.readCell (binding resource) index, b, mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | readValue found =>
      exact Matched.positive (.succ (Mir.Step.readValue found) .zero) (by decide) (.ret code placed .returned)
  | readUnavailable => exact False.elim (nextTyped.not_invalid rfl)

theorem store_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.store resource index value, a, k, w⟩ ty)
    (step : Step p responses ⟨.store resource index value, a, k, w⟩ next)
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before after a b) :
    Matched p q responses ⟨.store resource index value, a, k, w⟩
      ⟨.store (binding resource) index value, b, mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | stored written =>
      exact Matched.positive (.succ (Mir.Step.stored written) .zero) (by decide) (.ret code placed .returned)
  | storeUnavailable => exact False.elim (nextTyped.not_invalid rfl)

theorem writeCheck_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.writeCheck resource index value, a, k, w⟩ ty)
    (step : Step p responses ⟨.writeCheck resource index value, a, k, w⟩ next)
    (lowered : term offset locals ids value start = some (fragment, nextSupply))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before nextSupply a b) (le : SupplyLE before start)
    (sites : ScopedSites offset ids value) :
    Matched p q responses ⟨.writeCheck resource index value, a, k, w⟩
      ⟨.writeCheck (binding resource) index fragment.block, b, mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | writeChecked checked =>
      rename_i i checkedValue
      let continuation := KontCode.writeValue (resource := resource) (index := i) code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before nextSupply a b :=
        ⟨placed.range, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
          placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      obtain ⟨last, path, related⟩ := enter_block (world := w) nextPlaced lowered le sites
      exact Matched.positive (.succ (Mir.Step.writeChecked checked) path) (by decide) related
  | writeBounds bounds =>
      exact Matched.positive (.succ (Mir.Step.writeBounds bounds) .zero) (by decide) (.trap code placed)
  | writeWrong => exact False.elim (nextTyped.not_invalid rfl)

theorem lengthReady_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.lengthReady site value initializer yes no, a, k, w⟩ ty)
    (step : Step p responses ⟨.lengthReady site value initializer yes no, a, k, w⟩ next)
    (initialLowered : term offset locals ids initializer start = some (initialCode, second))
    (yesLowered : term offset locals ((site.heap + offset) :: ids) yes second = some (yesCode, third))
    (noLowered : term offset locals ids no third = some (noCode, nextSupply))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before nextSupply a b) (le : SupplyLE before start)
    (fresh : site.heap + offset ∉ ids) (initialSites : ScopedSites offset ids initializer)
    (yesSites : ScopedSites offset ((site.heap + offset) :: ids) yes) (noSites : ScopedSites offset ids no) :
    Matched p q responses ⟨.lengthReady site value initializer yes no, a, k, w⟩
      ⟨.lengthReady site (site.heap + offset) value initialCode.block yesCode.block noCode.block, b, mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | negativeLength negative =>
      exact Matched.positive (.succ (Mir.Step.negativeLength negative) .zero) (by decide) (.trap code placed)
  | nonnegativeLength nonnegative =>
      rename_i n
      let continuation := KontCode.heapInitial (site := site) (length := n.val.toNat) yesLowered noLowered code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before before a b :=
        ⟨SupplyLE.refl _, ⟨facts.1, facts.2.1, facts.2.2, placed.storage⟩,
          ⟨le.trans (term_supply initialLowered), placed.limits⟩, placed.offsets,
          ⟨fresh, yesSites, noSites, placed.sites⟩, placed.currentOffset⟩
      obtain ⟨last, path, related⟩ := enter_block (world := w) nextPlaced initialLowered le initialSites
      exact Matched.positive (.succ (Mir.Step.nonnegativeLength nonnegative) path) (by decide) related
  | lengthWrong => exact False.elim (nextTyped.not_invalid rfl)

theorem allocate_step (profile : q.allocationProfile = p.profile)
    (step : Step p responses ⟨.allocate site length value yes no, a, k, w⟩ next)
    (yesLowered : term offset locals ((site.heap + offset) :: ids) yes start = some (yesCode, middle))
    (noLowered : term offset locals ids no middle = some (noCode, nextSupply))
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before nextSupply a b) (le : SupplyLE before start)
    (fresh : site.heap + offset ∉ ids)
    (yesSites : ScopedSites offset ((site.heap + offset) :: ids) yes) (noSites : ScopedSites offset ids no) :
    Matched p q responses ⟨.allocate site length value yes no, a, k, w⟩
      ⟨.allocate site (site.heap + offset) length value yesCode.block noCode.block, b, mk, w⟩ next := by
  cases step with
  | allocated allocated =>
      rename_i allocatedWorld allocatedRef
      let owner : ANL.Memory.Binding := ⟨.owner, allocatedRef, length⟩
      let continuation := KontCode.owner (rid := site.heap + offset) (resource := owner) (site := site) code
      have facts := code.store_facts placed.storage
      have nextPlaced : Placed p continuation before nextSupply
          {a with resources := owner :: a.resources}
          {b with resources := (site.heap + offset, binding owner) :: b.resources} :=
        ⟨placed.range,
          ⟨facts.1.pushResource fresh, facts.2.1.pushResource,
            facts.2.2.pushResource facts.1.resources fresh, placed.storage⟩,
          placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
      obtain ⟨last, path, related⟩ := enter_block (world := allocatedWorld) nextPlaced yesLowered le yesSites
      exact Matched.positive (.succ (Mir.Step.allocated (by simpa only [profile] using allocated)) path) (by decide) related
  | allocationRefused refused =>
      rename_i refusedWorld
      obtain ⟨last, path, related⟩ := enter_block (world := refusedWorld) placed noLowered
        (le.trans (term_supply yesLowered)) noSites
      exact Matched.positive (.succ (Mir.Step.allocationRefused (by simpa only [profile] using refused)) path) (by decide) related
  | allocationRejected rejected =>
      rename_i rejectedWorld
      obtain ⟨last, path, related⟩ := enter_block (world := rejectedWorld) placed noLowered
        (le.trans (term_supply yesLowered)) noSites
      exact Matched.positive (.succ (Mir.Step.allocationRejected (by simpa only [profile] using rejected)) path) (by decide) related

end ANL.Words.Simulation
