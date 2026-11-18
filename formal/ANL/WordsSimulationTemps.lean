import ANL.WordsSimulationStore

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

theorem capture_retarget {a b : Mir.Activation} {temps : List Mir.Temp} {values : List Val} (h : a.capture temps = some values)
    (same : ∀ t v, a.temp t = some v → b.temp t = some v) : b.capture temps = some values := by
  induction temps generalizing values with
  | nil => simpa [Mir.Activation.capture] using h
  | cons t rest ih =>
      simp only [Mir.Activation.capture, List.mapM_cons, bind, Option.bind_eq_some_iff,
        Option.pure_def] at h
      obtain ⟨v, hv, vs, hvs, eq⟩ := h
      cases eq
      simp only [Mir.Activation.capture, List.mapM_cons]
      rw [same t v hv]
      change (b.capture rest).bind (fun vs => some (v :: vs)) = some (v :: vs)
      rw [ih hvs]
      rfl

theorem temp_extension_lookup (hb : Below before target) (fresh : before.nextTemp ≤ rid)
    (h : target.temp temp = some prior) :
    ({target with temps := (rid, v) :: target.temps} : Mir.Activation).temp temp = some prior := by
  have lt := hb.temps _ _ (lookupId_mem h)
  have ne : temp.id ≠ rid := by omega
  simpa [Mir.Activation.temp, ne] using h

theorem ActivationRel.extendTemp (h : ActivationRel locals ids source target)
    (hb : Below before target) (fresh : before.nextTemp ≤ rid) :
    ActivationRel locals ids source {target with temps := (rid, v) :: target.temps} := by
  refine ⟨h.function, ?_, h.slots, h.slotKeys, h.resources, h.resourceIds⟩
  apply h.values.retarget
  intro entry he
  cases entry with
  | value temp =>
      have lt := below_local h.values hb _ he
      have ne : temp.id ≠ rid := by change temp.id < before.nextTemp at lt; omega
      simp [localValue, Mir.Activation.temp, ne]
  | mutable slot => rfl

theorem CapturesHold.extendTemp (h : CapturesHold target captures)
    (hb : Below before target) (fresh : before.nextTemp ≤ rid) :
    CapturesHold {target with temps := (rid, v) :: target.temps} captures := by
  intro c hc
  have hold := h c hc
  cases c with
  | value temp prior => exact temp_extension_lookup hb fresh hold
  | arguments temps reversed =>
      exact capture_retarget hold (fun t prior hp => temp_extension_lookup hb fresh hp)
  | resource key b => exact hold

theorem Below.extendTemp (h : Below before target) (fresh : before.nextTemp ≤ temp.id) :
    Below (afterTemp before temp) {target with temps := (temp.id, v) :: target.temps} := by
  refine ⟨?_, h.slots⟩
  intro rid prior hi
  rcases List.mem_cons.mp hi with eq | hi
  · have idEq := Prod.mk.inj eq |>.1
    change rid < temp.id + 1
    omega
  · have lt := h.temps _ _ hi
    change rid < temp.id + 1
    omega

theorem SupplyLE.withTemp (h : SupplyLE before after) :
    SupplyLE (afterTemp before temp) (afterTemp after temp) := ⟨Nat.le_refl _, h.2⟩

theorem SupplyLE.to_afterTemp {temp : Mir.Temp} (fresh : before.nextTemp ≤ temp.id) :
    SupplyLE before (afterTemp before temp) := ⟨Nat.le_trans fresh (Nat.le_succ _), Nat.le_refl _⟩

theorem TempAgreement.extendTemp (h : TempAgreement bound target saved) (fresh : bound ≤ rid) :
    TempAgreement bound ((rid, v) :: target) saved := by
  intro key hk
  have ne : key ≠ rid := by omega
  simpa only [lookupId_cons_other ne] using h key hk

theorem KontCode.store_extendTemp (code : KontCode offset locals ids k result captures)
    (h : code.StoreSafe before source target) (fresh : before.nextTemp ≤ temp.id) :
    code.StoreSafe (afterTemp before temp) source
      {target with temps := (temp.id, v) :: target.temps} := by
  induction code generalizing before source target with
  | @nil offset locals ids =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, hp⟩
  | @yield offset locals ids k mk captures value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @destination offset locals ids k d tail mk captures parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ⟨hp.1.extendTemp (Nat.le_trans hp.2.1.1 fresh), hp.2.1.trans (SupplyLE.to_afterTemp fresh), hp.2.2⟩⟩
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @scopeValue offset locals ids k resultShape captures value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @convert offset locals ids k d tail mk captures mode target value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @logicalRight op prior offset locals ids k resultShape captures logical parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @project offset locals ids k d tail mk captures index value parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, hp⟩
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      rcases h with ⟨ha, hb, hc, hp⟩
      exact ⟨ha.extendTemp hb fresh, hb.extendTemp fresh, hc.extendTemp hb fresh, ih hp fresh⟩

end ANL.Words.Simulation
