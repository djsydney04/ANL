import ANL.WordsSimulationBounds

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

/-- Proof-side description of an existing slot write; runtime uses updateId. -/
def replaceSlot (rid : Nat) (v : Val) (slots : Mir.Values) : Mir.Values :=
  slots.map (fun (key, prior) => (key, if key = rid then v else prior))

def replaceLocals (locals : Locals) (rid : Nat) (v : Val) : Env → Env
  | [] => []
  | prior :: values => match locals with
      | [] => prior :: values
      | entry :: rest =>
          (match entry with | .value _ => prior | .mutable s => if s.id = rid then v else prior) ::
            replaceLocals rest rid v values

@[simp] theorem replaceSlot_keys : (replaceSlot rid v slots).map Prod.fst = slots.map Prod.fst := by
  simp [replaceSlot, List.map_map, Function.comp_def]

@[simp] theorem replaceSlot_tail : (replaceSlot rid v slots).tail = replaceSlot rid v slots.tail := by
  cases slots <;> rfl

@[simp] theorem replaceLocals_tail :
    (replaceLocals (entry :: locals) rid v values).tail = replaceLocals locals rid v values.tail := by
  cases values <;> simp [replaceLocals]

theorem replaceLocals_absent (h : rid ∉ mutableIds locals) :
    replaceLocals locals rid v values = values := by
  induction values generalizing locals with
  | nil => simp [replaceLocals]
  | cons prior values ih =>
      cases locals with
      | nil => rfl
      | cons entry locals =>
          cases entry with
          | value temp => simp only [replaceLocals]; rw [ih (locals := locals) h]
          | mutable slot =>
              have hs : slot.id ≠ rid := by intro eq; exact h (by simp [mutableIds, eq])
              have ht : rid ∉ mutableIds locals := by intro hi; exact h (.tail _ hi)
              simp only [replaceLocals, ite_eq_right hs, ih ht]

theorem lookupId_replaceSlot : ANL.Memory.Mir.lookupId key (replaceSlot rid v slots) =
    (ANL.Memory.Mir.lookupId key slots).map (fun prior => if key = rid then v else prior) := by
  induction slots with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨found, prior⟩
      by_cases hk : key = found
      · subst found; simp [replaceSlot, ANL.Memory.Mir.lookupId]
      · simpa only [replaceSlot, List.map_cons, ANL.Memory.Mir.lookupId, ite_eq_right hk] using ih

theorem LocalsRel.replace (h : LocalsRel target locals values) :
    LocalsRel {target with slots := replaceSlot rid v target.slots} locals
      (replaceLocals locals rid v values) := by
  induction h with
  | nil => exact .nil
  | @cons entry prior locals values hv h ih =>
      cases entry with
      | value temp => exact .cons hv ih
      | mutable slot =>
          apply LocalsRel.cons _ ih
          change ANL.Memory.Mir.lookupId slot.id (replaceSlot rid v target.slots) = _
          rw [lookupId_replaceSlot]
          change ANL.Memory.Mir.lookupId slot.id target.slots = some prior at hv
          simp [hv]

theorem ActivationRel.replace (h : ActivationRel locals ids source target) :
    ActivationRel locals ids {source with env := replaceLocals locals rid v source.env}
      {target with slots := replaceSlot rid v target.slots} :=
  ⟨h.function, h.values.replace, h.slots, by simpa using h.slotKeys, h.resources, h.resourceIds⟩

theorem Below.replace (h : Below bound target) :
    Below bound {target with slots := replaceSlot rid v target.slots} := by
  refine ⟨h.temps, ?_⟩
  intro key prior hm
  obtain ⟨⟨found, old⟩, hi, eq⟩ := List.mem_map.mp hm
  cases Prod.mk.inj eq |>.1
  exact h.slots _ _ hi

theorem CapturesHold.replace (h : CapturesHold target captures) :
    CapturesHold {target with slots := replaceSlot rid v target.slots} captures := by
  intro c hc
  have holds := h c hc
  cases c <;> exact holds

theorem replaceSlot_absent (h : rid ∉ slots.map Prod.fst) : replaceSlot rid v slots = slots := by
  induction slots with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨key, prior⟩
      have hk : key ≠ rid := by intro eq; exact h (by simp [eq])
      have ht : rid ∉ rest.map Prod.fst := by intro hi; exact h (.tail _ hi)
      simp only [replaceSlot, List.map_cons, ite_eq_right hk]
      exact congrArg ((key, prior) :: ·) (ih ht)

theorem updateId_eq_replace (h : ANL.Memory.Mir.updateId rid v slots = some updated)
    (unique : (slots.map Prod.fst).Nodup) : updated = replaceSlot rid v slots := by
  induction slots generalizing updated with
  | nil => simp [ANL.Memory.Mir.updateId] at h
  | cons pair rest ih =>
      rcases pair with ⟨key, prior⟩
      have hn := List.nodup_cons.mp unique
      by_cases hk : rid = key
      · subst key
        simp only [ANL.Memory.Mir.updateId, ite_true, Option.some.injEq] at h
        subst updated
        change (rid, v) :: rest = (rid, if rid = rid then v else prior) :: replaceSlot rid v rest
        rw [ite_eq_left rfl, replaceSlot_absent hn.1]
      · simp only [ANL.Memory.Mir.updateId, ite_eq_right hk, Option.map_eq_some_iff] at h
        obtain ⟨tail, ht, rfl⟩ := h
        change (key, prior) :: tail = (key, if key = rid then v else prior) :: replaceSlot rid v rest
        rw [ite_eq_right (Ne.symm hk), ih ht hn.2]

theorem LocalsRel.assignment (h : LocalsRel target locals values)
    (unique : (mutableIds locals).Nodup) (lookup : locals[index]? = some (.mutable slot)) :
    ANL.Words.update values index v = some (replaceLocals locals slot.id v values) := by
  induction h generalizing index with
  | nil => simp at lookup
  | @cons entry prior locals values hv h ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst entry
          have hn := List.nodup_cons.mp unique
          simp [ANL.Words.update, replaceLocals, replaceLocals_absent hn.1]
      | succ index =>
          have hl : locals[index]? = some (.mutable slot) := by simpa using lookup
          cases entry with
          | value temp =>
              simpa [ANL.Words.update, replaceLocals] using
                congrArg (Option.map (prior :: ·)) (ih unique hl)
          | mutable found =>
              have hn := List.nodup_cons.mp unique
              have ne : found.id ≠ slot.id := by
                intro eq
                exact hn.1 (eq ▸ mutableIds_mem (List.mem_of_getElem? hl))
              simpa [ANL.Words.update, replaceLocals, ne] using
                congrArg (Option.map (prior :: ·)) (ih hn.2 hl)

theorem KontCode.store_weaken (code : KontCode offset locals ids k result captures)
    (h : code.StoreSafe before source target) (le : SupplyLE before after) :
    code.StoreSafe after source target := by
  induction code generalizing before after source target with
  | @nil offset locals ids =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, hp⟩
  | @yield offset locals ids k mk captures value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @destination offset locals ids k d tail mk captures parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ⟨hp.1, hp.2.1.trans le, hp.2.2⟩⟩
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @scopeValue offset locals ids k resultShape captures value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @convert offset locals ids k d tail mk captures mode target value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @logicalRight op prior offset locals ids k resultShape captures logical parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @project offset locals ids k d tail mk captures index value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, hp⟩
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha, hb.weaken le, hc, ih hp le⟩

theorem KontCode.store_replace (code : KontCode offset locals ids k result captures)
    (h : code.StoreSafe bound source target) :
    code.StoreSafe bound {source with env := replaceLocals locals rid v source.env}
      {target with slots := replaceSlot rid v target.slots} := by
  induction code generalizing bound source target with
  | @nil offset locals ids =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, hp⟩
  | @yield offset locals ids k mk captures value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @destination offset locals ids k d tail mk captures parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ⟨hp.1, hp.2.1, ih hp.2.2⟩⟩
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @scopeValue offset locals ids k resultShape captures value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      refine ⟨ha.replace, hb.replace, hc.replace, ?_⟩
      change parent.StoreSafe bound {source with env := (replaceLocals (.value value :: locals) rid v source.env).tail} {target with slots := replaceSlot rid v target.slots}
      simpa only [replaceLocals_tail, replaceSlot_tail] using ih hp
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      refine ⟨ha.replace, hb.replace, hc.replace, ?_⟩
      change parent.StoreSafe bound {source with env := (replaceLocals (.mutable slot :: locals) rid v source.env).tail} {target with slots := (replaceSlot rid v target.slots).tail}
      simpa only [replaceLocals_tail, replaceSlot_tail] using ih hp
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @convert offset locals ids k d tail mk captures mode target value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @logicalRight op prior offset locals ids k resultShape captures logical parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @project offset locals ids k d tail mk captures index value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, hp⟩
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.replace, hb.replace, hc.replace, ih hp⟩

end ANL.Words.Simulation
