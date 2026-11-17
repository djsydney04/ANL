import ANL.MemorySimulationReturnMemory

namespace ANL.Memory.Simulation
open Lowering

theorem close_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.close resource site value, a, .owner resource site :: k, w⟩ ty)
    (step : Step p responses ⟨.close resource site value, a, .owner resource site :: k, w⟩ next)
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p (KontCode.owner (rid := rid) (resource := resource) (site := site) code) before after a b) :
    Matched p q responses ⟨.close resource site value, a, .owner resource site :: k, w⟩
      ⟨.close rid (binding resource) site value, b, .owner rid (binding resource) site :: mk, w⟩ next := by
  have nextTyped := preservation wf typed step
  cases step with
  | closed closed =>
      have facts := (KontCode.owner (rid := rid) (resource := resource) (site := site) code).store_facts placed.storage
      obtain ⟨sourceRest, sourceHead⟩ := typed_owner_head typed
      have paired : ResourcesRel (rid :: ids) (resource :: sourceRest) b.resources := by
        rw [← sourceHead]
        exact facts.1.resources
      obtain ⟨targetRest, targetHead, _⟩ := paired.head
      have parentStorage : code.StoreSafe before {a with resources := a.resources.tail}
          {b with resources := b.resources.tail} := placed.storage.2.2.2
      have parent : Placed p code before after {a with resources := a.resources.tail}
          {b with resources := targetRest} := by
        refine ⟨placed.range, ?_, placed.limits, placed.offsets, placed.sites, placed.currentOffset⟩
        simpa only [targetHead, List.tail_cons] using parentStorage
      exact Matched.positive (.succ (Mir.Step.closeFound targetHead closed) .zero) (by decide)
        (Related.ret code parent .returned)
  | closeUnavailable => exact False.elim (nextTyped.not_invalid rfl)
  | closeWrong => exact False.elim (nextTyped.not_invalid rfl)

end ANL.Memory.Simulation
