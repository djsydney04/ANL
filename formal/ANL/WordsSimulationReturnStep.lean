import ANL.WordsSimulationReturnBindings
import ANL.WordsSimulationReturnScalar
import ANL.WordsSimulationReturnControl
import ANL.WordsSimulationReturnArguments
import ANL.WordsSimulationReturnMemory
import ANL.WordsSimulationRetTyping

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

/-- Constructor-by-constructor matching after finite target return-adapter normalization. -/
theorem ready_return_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.ret v, a, k, w⟩ ty)
    (step : Step p responses ⟨.ret v, a, k, w⟩ successor)
    (code : KontCode offset locals ids k result captures) (ready : code.Ready)
    (placed : Placed p code before after a b) (atResult : AtResult b v result ctrl actualKont) :
    Matched p q responses ⟨.ret v, a, k, w⟩ ⟨ctrl, b, actualKont, w⟩ successor := by
  have nextTyped := preservation wf typed step
  cases code with
  | @nil offset locals ids =>
      cases step
  | @yield offset locals ids k mk captures value parent =>
      simp [KontCode.Ready] at ready
  | @destination offset locals ids k d tail mk captures parent =>
      simp [KontCode.Ready] at ready
  | @blockEnd locals offset ids k mk captures snapshot parent =>
      simp [KontCode.Ready] at ready
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent =>
      cases step with
      | bindReturn => exact return_bindValue lowered parent placed atResult
  | @scopeValue offset locals ids k resultShape captures value parent =>
      cases step with
      | scopeReturn env => exact return_scopeValue parent placed atResult env
      | scopeMissing => exact False.elim (nextTyped.not_invalid rfl)
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent =>
      cases step with
      | bindReturn => exact return_bindMutable lowered parent placed atResult
  | @scopeMutable offset locals ids k mk captures slot parent =>
      cases step with
      | scopeReturn env => exact return_scopeMutable parent placed atResult env
      | scopeMissing => exact False.elim (nextTyped.not_invalid rfl)
  | @assign locals index offset ids k d tail mk captures value slot lookup parent =>
      cases step with
      | assignReturn assigned => exact return_assign lookup parent placed atResult assigned
      | assignMissing => exact False.elim (nextTyped.not_invalid rfl)
  | @convert offset locals ids k d tail mk captures mode target value parent =>
      cases step with
      | convertReturn => exact return_convert parent placed atResult (resume_valid_of_typed nextTyped)
  | @unary offset locals ids k d tail mk captures op value parent =>
      cases step with
      | unaryReturn => exact return_unary parent placed atResult (resume_valid_of_typed nextTyped)
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent =>
      cases step with
      | short hs => simp [nonlogical_not_short notAnd notOr] at hs
      | rightEval hs => exact return_binaryLeft notAnd notOr lowered parent placed atResult hs
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent =>
      cases step with
      | binaryReturn => exact return_binaryRight notAnd notOr parent placed atResult (resume_valid_of_typed nextTyped)
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent =>
      obtain ⟨boolean, equality⟩ := typed_logical_left (.inl rfl) typed
      subst v
      cases boolean with
      | false =>
          cases step with
          | short => exact return_andLeft_false lowered parent placed atResult
          | rightEval impossible => simp [ANL.Words.shortCircuit, APL.shortCircuit] at impossible
      | true =>
          cases step with
          | rightEval => exact return_andLeft_true lowered parent placed atResult
          | short impossible => simp [ANL.Words.shortCircuit, APL.shortCircuit] at impossible
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent =>
      obtain ⟨boolean, equality⟩ := typed_logical_left (.inr rfl) typed
      subst v
      cases boolean with
      | false =>
          cases step with
          | rightEval => exact return_orLeft_false lowered parent placed atResult
          | short impossible => simp [ANL.Words.shortCircuit, APL.shortCircuit] at impossible
      | true =>
          cases step with
          | short => exact return_orLeft_true lowered parent placed atResult
          | rightEval impossible => simp [ANL.Words.shortCircuit, APL.shortCircuit] at impossible
  | @logicalRight op prior offset locals ids k resultShape captures logical parent =>
      cases step with
      | binaryReturn => exact return_logicalRight logical parent placed atResult (resume_valid_of_typed nextTyped)
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent =>
      cases step with
      | ifTrue => exact return_branch_true leftLowered rightLowered parent placed atResult
      | ifFalse => exact return_branch_false leftLowered rightLowered parent placed atResult
      | ifWrong => exact False.elim (nextTyped.not_invalid rfl)
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent =>
      cases step with
      | whileTrue => exact return_condition_true conditionLowered bodyLowered parent placed atResult
      | whileFalse => exact return_condition_false conditionLowered bodyLowered parent placed atResult
      | whileWrong => exact False.elim (nextTyped.not_invalid rfl)
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent =>
      cases step with
      | whileAgain => exact return_body_again conditionLowered bodyLowered parent placed atResult
      | bodyWrong => exact False.elim (nextTyped.not_invalid rfl)
  | @project offset locals ids k d tail mk captures index value parent =>
      cases step with
      | projectReturn => exact return_project parent placed atResult (resume_valid_of_typed nextTyped)
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent =>
      cases step with
      | heapLengthReturn => exact return_heapLength initialLowered yesLowered noLowered parent placed atResult (typed_heapLength_function typed)
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent =>
      cases step with
      | heapInitialReturn => exact return_heapInitial yesLowered noLowered parent placed atResult
      | heapInitialWrong => exact False.elim (nextTyped.not_invalid rfl)
  | @owner offset locals ids k mk captures rid resource site parent =>
      cases step with
      | ownerReturn => exact return_owner parent placed atResult
  | @readIndex offset locals ids k d tail mk captures resource index rid parent =>
      cases step with
      | readIndexReturn => exact return_readIndex parent placed atResult
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent =>
      cases step with
      | writeIndexReturn => exact return_writeIndex lowered parent placed atResult (typed_writeIndex_permission typed)
  | @writeValue offset locals ids k mk captures resource index parent =>
      cases step with
      | writeValueReturn => exact return_writeValue parent placed atResult
      | writeValueWrong => exact False.elim (nextTyped.not_invalid rfl)
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent =>
      cases step with
      | argumentReturn =>
          cases remaining with
          | nil => exact return_viewArguments_nil lowered parent placed atResult (typed_view_permission typed)
          | cons first rest => exact return_viewArguments_cons lowered parent placed atResult
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent =>
      cases step with
      | fieldNext => exact return_fields_cons lowered parent placed atResult
      | fieldsDone => exact return_fields_nil lowered parent placed atResult (resume_valid_of_typed nextTyped)
      | fieldTuple => exact False.elim (nextTyped.not_invalid rfl)
  | @caller captures k mk offset locals ids sourceLoan saved captured parent =>
      cases step with
      | callResult =>
          cases atResult
          exact Matched.positive (.succ Mir.Step.callReturn .zero) (by decide)
            (Related.revoke (KontCode.caller saved captured parent) placed)
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent =>
      cases step with
      | argumentReturn =>
          cases remaining with
          | nil => exact return_arguments_nil lowered parent placed atResult
          | cons first rest => exact return_arguments_cons lowered parent placed atResult

theorem return_step (wf : WellFormedProgram p)
    (typed : State.Typed p ⟨.ret v, a, k, w⟩ ty)
    (step : Step p responses ⟨.ret v, a, k, w⟩ successor)
    (code : KontCode offset locals ids k result captures)
    (placed : Placed p code before after a b) (atResult : AtResult b v result ctrl actualKont) :
    Matched p q responses ⟨.ret v, a, k, w⟩ ⟨ctrl, b, actualKont, w⟩ successor := by
  obtain prepared := prepare_return (q := q) (responses := responses) (w := w) code placed atResult
  cases prepared with
  | found parent ready continued found path =>
      exact Matched.prepend path (ready_return_step wf typed step parent ready continued found)

end ANL.Words.Simulation
