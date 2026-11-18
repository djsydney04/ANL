import ANL.WordsSimulationContext

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

theorem ActivationRel.pushResource (h : ActivationRel locals ids source target) (fresh : rid ∉ ids) :
    ActivationRel locals (rid :: ids) {source with resources := resource :: source.resources}
      {target with resources := (rid, binding resource) :: target.resources} :=
  ⟨h.function, h.values.retarget (fun entry _ => by cases entry <;> rfl), h.slots, h.slotKeys, .cons h.resources, List.nodup_cons.mpr ⟨fresh, h.resourceIds⟩⟩

theorem Below.pushResource (h : Below bound target) :
    Below bound {target with resources := (rid, resource) :: target.resources} := ⟨h.temps, h.slots⟩

theorem CapturesHold.pushResource (h : CapturesHold target captures)
    (resources : ResourcesRel ids sourceResources target.resources) (fresh : rid ∉ ids) :
    CapturesHold {target with resources := (rid, resource) :: target.resources} captures := by
  intro capture membership
  have hold := h capture membership
  cases capture with
  | value temp value => exact hold
  | arguments temps reversed => exact hold
  | resource key captured =>
      have present := lookupId_mem hold
      have keyIn : key ∈ ids := by
        rw [← resources.keys]
        exact List.mem_map.mpr ⟨_, present, rfl⟩
      have ne : key ≠ rid := by intro eq; exact fresh (eq ▸ keyIn)
      simpa only [Capture.Holds, Mir.Activation.resource, lookupId_cons_other ne] using hold

theorem Layout.owner_head (layout : Layout owners resources (.owner resource site :: k)) :
    ∃ rest, resources = resource :: rest := by
  cases layout with
  | plain no => simp [Frame.Plain] at no
  | owner => exact ⟨_, rfl⟩

theorem typed_owner_head (typed : State.Typed p ⟨ctrl, a, .owner resource site :: k, world⟩ ty) :
    ∃ rest, a.resources = resource :: rest := by
  cases typed with
  | intro env control kont layout valid => exact Layout.owner_head layout

theorem ResourcesRel.head (h : ResourcesRel (rid :: ids) (resource :: rest) target) :
    ∃ tail, target = (rid, binding resource) :: tail ∧ ResourcesRel ids rest tail := by
  cases h with
  | cons tail => exact ⟨_, rfl, tail⟩

end ANL.Words.Simulation
