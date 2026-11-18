import ANL.WordsSimulationTemps
import ANL.WordsSimulationInitial

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

/-- No leading destination, yield, or temporary-restoration adapter remains. -/
def KontCode.Ready (code : KontCode offset locals ids k result captures) : Prop :=
  match code with
  | .yield _ | .destination _ | .blockEnd _ _ => False
  | _ => True

/-- A finite actual MIR prefix reaches a concrete, adapter-free return context. -/
inductive ReturnPrepared (p : Program) (q : Mir.Program) (responses : Responses)
    (source : ANL.Words.Activation) (kont : List ANL.Words.Frame) (value : Val) (world : World) :
    Mir.State → Prop where
  | found (code : KontCode offset locals ids kont result captures) :
      code.Ready → Placed p code before after source target →
      AtResult target value result targetControl targetKont →
      MirStepsN q responses count first ⟨targetControl, target, targetKont, world⟩ →
      ReturnPrepared p q responses source kont value world first

theorem ReturnPrepared.prepend (h : Mir.Step q responses first middle)
    (prepared : ReturnPrepared p q responses source kont value world middle) :
    ReturnPrepared p q responses source kont value world first := by
  cases prepared with
  | found code ready placed atResult path => exact .found code ready placed atResult (.succ h path)

theorem prepare_return (code : KontCode offset locals ids k result captures)
    (placed : Placed p code before after a b) (atResult : AtResult b v result ctrl mk) :
    ReturnPrepared p q responses a k v w ⟨ctrl, b, mk, w⟩ := by
  induction code generalizing before after a b ctrl mk with
  | @nil offset locals ids =>
      exact .found (KontCode.nil ) (by simp [KontCode.Ready]) placed atResult .zero
  | @yield offset locals ids k mk captures value parent ih =>
      cases atResult with
      | captured lookup =>
          apply ReturnPrepared.prepend (.yieldFound lookup)
          exact ih ⟨placed.range, placed.storage.2.2.2, placed.limits,
            placed.offsets, placed.sites, placed.currentOffset⟩ .returned
  | @destination offset locals ids k d tail mk captures parent ih =>
      cases atResult with
      | returned =>
          have fresh : before.nextTemp ≤ d.id := Nat.le_trans placed.range.1 placed.limits.1
          have storage := parent.store_extendTemp placed.storage.2.2.2 fresh (v := v)
          have widened := parent.store_weaken storage placed.range.withTemp
          apply ReturnPrepared.prepend Mir.Step.instructionReturn
          exact ih ⟨SupplyLE.refl _, widened, placed.limits.2, placed.offsets,
            placed.sites, placed.currentOffset⟩ (.captured (by simp [Mir.Activation.temp]))
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      cases atResult with
      | returned =>
          apply ReturnPrepared.prepend Mir.Step.blockReturn
          exact ih ⟨SupplyLE.refl _, placed.storage.2.2.2.2.2, placed.limits.2,
            placed.offsets, placed.sites, placed.currentOffset⟩ .returned
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      exact .found (KontCode.bindValue lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @scopeValue offset locals ids k resultShape captures value parent ih =>
      exact .found (KontCode.scopeValue parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      exact .found (KontCode.bindMutable lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      exact .found (KontCode.scopeMutable parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      exact .found (KontCode.assign lookup parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @convert offset locals ids k d tail mk captures mode target value parent ih =>
      exact .found (KontCode.convert parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      exact .found (KontCode.unary parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      exact .found (KontCode.binaryLeft notAnd notOr lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      exact .found (KontCode.binaryRight notAnd notOr parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact .found (KontCode.andLeft lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact .found (KontCode.orLeft lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @logicalRight op prior offset locals ids k resultShape captures logical parent ih =>
      exact .found (KontCode.logicalRight logical parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      exact .found (KontCode.branch leftLowered rightLowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact .found (KontCode.condition conditionLowered bodyLowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact .found (KontCode.body conditionLowered bodyLowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @project offset locals ids k d tail mk captures index value parent ih =>
      exact .found (KontCode.project parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      exact .found (KontCode.heapLength initialLowered yesLowered noLowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      exact .found (KontCode.heapInitial yesLowered noLowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      exact .found (KontCode.owner parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      exact .found (KontCode.readIndex parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      exact .found (KontCode.writeIndex lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      exact .found (KontCode.writeValue parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      exact .found (KontCode.viewArguments lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      exact .found (KontCode.fields lowered parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      exact .found (KontCode.caller saved captured parent) (by simp [KontCode.Ready]) placed atResult .zero
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      exact .found (KontCode.arguments lowered parent) (by simp [KontCode.Ready]) placed atResult .zero

theorem ReturnPrepared.finish_value
    (h : ReturnPrepared p q responses source [] value world first) :
    ∃ last, Mir.Steps q responses first last ∧ Mir.Terminal last ∧
      FinalRelated p ⟨.ret value, source, [], world⟩ last := by
  cases h with
  | found code ready placed atResult path =>
      cases code with
      | nil =>
          cases atResult
          refine ⟨_, path.steps, rfl, Related.ret .nil placed .returned, rfl, Or.inl ?_⟩
          exact ⟨value, rfl, rfl, rfl, rfl⟩
      | yield => simp [KontCode.Ready] at ready
      | destination => simp [KontCode.Ready] at ready
      | blockEnd => simp [KontCode.Ready] at ready

/-- Every related completed core state has a constructively finite MIR completion. -/
theorem terminal_flush (related : Related p source target) (terminal : Terminal source) :
    ∃ last, Mir.Steps q responses target last ∧ Mir.Terminal last ∧ FinalRelated p source last := by
  cases terminal with
  | value =>
      cases related with
      | ret code placed atResult => exact (prepare_return code placed atResult).finish_value
  | trap =>
      cases related with
      | trap code placed =>
          refine ⟨_, .refl, True.intro, Related.trap code placed, True.intro, Or.inr ?_⟩
          exact ⟨_, rfl, rfl⟩

end ANL.Words.Simulation
