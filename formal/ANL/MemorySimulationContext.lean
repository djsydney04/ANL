import ANL.MemorySimulationMatch

namespace ANL.Memory.Simulation
open Lowering

theorem CapturesHold.cons (head : capture.Holds target) (tail : CapturesHold target captures) :
    CapturesHold target (capture :: captures) := by
  intro item membership
  rcases List.mem_cons.mp membership with rfl | membership
  · exact head
  · exact tail item membership

theorem CapturesHold.tail (h : CapturesHold target (capture :: captures)) : CapturesHold target captures :=
  fun item member => h item (.tail _ member)

theorem CapturesHold.head (h : CapturesHold target (capture :: captures)) : capture.Holds target :=
  h capture (.head _)

@[simp] theorem CapturesHold.nil : CapturesHold target [] := by simp [CapturesHold]

theorem ActivationRel.resource_lookup {index : Nat} (h : ActivationRel locals ids source target)
    (indexId : ids[index]? = some rid) (sourceLookup : source.resources[index]? = some resource) :
    target.resource rid = some (binding resource) := by
  obtain ⟨found, sourceFound, targetFound⟩ := h.resources.lookup h.resourceIds indexId
  have same : found = resource := Option.some.inj (sourceFound.symm.trans sourceLookup)
  subst found
  exact targetFound

theorem ActivationRel.pushValue (h : ActivationRel locals ids source target)
    (found : target.temp temp = some value) :
    ActivationRel (.value temp :: locals) ids {source with env := value :: source.env} target :=
  ⟨h.function, .cons found h.values, h.slots, h.slotKeys, h.resources, h.resourceIds⟩

theorem CapturesHold.pushSlot (h : CapturesHold target captures) :
    CapturesHold {target with slots := (rid, value) :: target.slots} captures := by
  intro capture hc
  have hold := h capture hc
  cases capture <;> exact hold

theorem ActivationRel.pushSlot (h : ActivationRel locals ids source target)
    (hb : Below before target) (fresh : before.nextSlot ≤ slot.id) :
    ActivationRel (.mutable slot :: locals) ids {source with env := value :: source.env}
      {target with slots := (slot.id, value) :: target.slots} := by
  have localsBound := below_local h.values hb
  have absent : slot.id ∉ mutableIds locals := by
    intro membership
    rw [← h.slotKeys] at membership
    obtain ⟨⟨rid, prior⟩, hm, eq⟩ := List.mem_map.mp membership
    have lt := hb.slots _ _ hm
    change rid = slot.id at eq
    omega
  refine ⟨h.function, .cons (by simp [localValue, Mir.Activation.slot]) ?_,
    List.nodup_cons.mpr ⟨absent, h.slots⟩, by simpa [mutableIds] using congrArg (slot.id :: ·) h.slotKeys,
    h.resources, h.resourceIds⟩
  apply h.values.retarget
  intro entry membership
  cases entry with
  | value temp => rfl
  | mutable found =>
      have lt : found.id < before.nextSlot := localsBound _ membership
      have ne : found.id ≠ slot.id := by omega
      simp [localValue, Mir.Activation.slot, ne]

theorem Below.pushSlot (h : Below before target) (le : SupplyLE before after) (fresh : rid < after.nextSlot) :
    Below after {target with slots := (rid, value) :: target.slots} := by
  have widened := h.weaken le
  refine ⟨widened.temps, ?_⟩
  intro key prior membership
  rcases List.mem_cons.mp membership with eq | membership
  · have same := Prod.mk.inj eq |>.1
    omega
  · exact widened.slots _ _ membership

theorem Captured.append_value (captured : Captured target done prior) (found : target.temp input = some value) :
    Captured target (done ++ [input]) (value :: prior) := by
  change done.mapM target.temp = some prior.reverse at captured
  simp [Captured, Mir.Activation.capture, List.mapM_append, captured, found, List.reverse_cons]

theorem constructTuple_map (values : List APL.Val) :
    Mir.constructTuple (values.map APL.FlatProducts.Val.scalar) = APL.FlatProducts.construct values := by
  simp only [Mir.constructTuple, List.mapM_map, Function.comp_def]
  have collected : values.mapM (fun value => some value) = some values := by
    induction values <;> simp_all
  rw [collected]

end ANL.Memory.Simulation
