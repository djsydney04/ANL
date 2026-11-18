import ANL.WordsSimulationRelation

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

def ResultTarget.kont : ResultTarget → List Mir.Frame
  | .captured _ _ k => k
  | .returned k => k

theorem KontCode.capabilities (code : KontCode offset locals ids k target captures) :
    CapabilityKontRel k target.kont := by
  induction code with
  | @nil offset locals ids =>
      exact .nil
  | @yield offset locals ids k mk captures value parent ih =>
      exact ih
  | @destination offset locals ids k d tail mk captures parent ih =>
      exact .targetPlain trivial ih
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      exact .targetPlain trivial ih
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      exact .sourcePlain trivial ih
  | @scopeValue offset locals ids k target captures value parent ih =>
      exact .sourcePlain trivial ih
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      exact .sourcePlain trivial ih
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      exact .sourcePlain trivial (.targetPlain trivial ih)
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      exact .sourcePlain trivial ih
  | @convert offset locals ids k d tail mk captures mode target value parent ih =>
      exact .sourcePlain trivial ih
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      exact .sourcePlain trivial ih
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      exact .sourcePlain trivial ih
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      exact .sourcePlain trivial ih
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact .sourcePlain trivial ih
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact .sourcePlain trivial ih
  | @logicalRight op prior offset locals ids k target captures logical parent ih =>
      exact .sourcePlain trivial ih
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      exact .sourcePlain trivial ih
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact .sourcePlain trivial (.targetPlain trivial ih)
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact .sourcePlain trivial (.targetPlain trivial ih)
  | @project offset locals ids k d tail mk captures index value parent ih =>
      exact .sourcePlain trivial ih
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      exact .sourcePlain trivial ih
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      exact .sourcePlain trivial (.targetPlain trivial ih)
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      exact .owner ih
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      exact .sourcePlain trivial ih
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      exact .sourcePlain trivial ih
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      exact .sourcePlain trivial (.targetPlain trivial ih)
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      exact .sourcePlain trivial ih
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      exact .sourcePlain trivial ih
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      exact .caller saved.represented ih
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      exact .sourcePlain trivial ih

theorem KontCode.store_facts (code : KontCode offset locals ids k result captures)
    (h : code.StoreSafe bound source target) :
    ActivationRel locals ids source target ∧ Below bound target ∧ CapturesHold target captures := by
  cases code <;> exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem Related.runtime (h : Related p source target) :
    ∃ locals ids, RuntimeRel locals ids source target := by
  cases h with
  | eval code _ _ placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | ret code placed resultAt =>
      cases resultAt <;> exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | lengthReady code _ _ _ _ _ _ _ _ placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | allocate code _ _ _ _ _ _ placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | readCheck code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | readCell code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | writeCheck code _ _ _ placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | store code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | invoke code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | grant code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | close code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | revoke code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | restore code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩
  | trap code placed => exact ⟨_, _, ⟨(code.store_facts placed.storage).1, code.capabilities, rfl⟩⟩

theorem Related.world (h : Related p source target) : source.world = target.world := by
  cases h <;> rfl

theorem Related.target_not_invalid (h : Related p source target) : target.control ≠ .invalid := by
  cases h with
  | ret _ _ resultAt => cases resultAt <;> simp
  | _ => simp

theorem initial_related (canonical : Canonical p q) :
    Related p (ANL.Words.initial p) (Mir.initial q) := by
  have lowered := canonical.2
  simp only [Lowering.program, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
  obtain ⟨functions, _, equality⟩ := lowered
  cases equality
  obtain ⟨fn, found, view, _, _⟩ := canonical.1.entry
  apply Related.invoke (before := ⟨0, 0⟩) (after := ⟨0, 0⟩) (KontCode.nil (offset := 0) (locals := []) (ids := []))
  refine ⟨?_, ?_, trivial, trivial, trivial, ?_⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨⟨rfl, .nil, List.nodup_nil, rfl, .nil, List.nodup_nil⟩,
      ⟨by simp, by simp⟩, by simp [CapturesHold], trivial⟩
  · exact ⟨fn, found, by simp [view, Lowering.viewOffset]⟩

end ANL.Words.Simulation
