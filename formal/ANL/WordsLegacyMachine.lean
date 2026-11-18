import ANL.WordsLegacy
import ANL.WordsExecute
import ANL.MemoryExecute

namespace ANL.Words

open ANL.Memory

set_option linter.unusedSimpArgs false

def embedActivation (a : ANL.Memory.Activation) : Activation :=
  ⟨a.function, embedEnv a.env, a.resources⟩

def embedFrame : ANL.Memory.Frame → Frame
  | .bind m b => .bind m (embedTerm b)
  | .scope => .scope
  | .assign i => .assign i
  | .ifF y n => .ifF (embedTerm y) (embedTerm n)
  | .unary op => .unary (.legacy op)
  | .left op e => .left (.legacy op) (embedTerm e)
  | .right op v => .right (.legacy op) (embedVal v)
  | .arguments f loan rest values => .arguments f loan (rest.map embedTerm) (values.map embedVal)
  | .callReturn caller loan => .callReturn (embedActivation caller) loan
  | .condition c b => .condition (embedTerm c) (embedTerm b)
  | .body c b => .body (embedTerm c) (embedTerm b)
  | .fields rest values => .fields (rest.map embedTerm) (values.map ScalarVal.legacy)
  | .project i => .project i
  | .heapLength site init yes no => .heapLength site (embedTerm init) (embedTerm yes) (embedTerm no)
  | .heapInitial site n yes no => .heapInitial site n (embedTerm yes) (embedTerm no)
  | .owner binding site => .owner binding site
  | .readIndex binding => .readIndex binding
  | .writeIndex binding v => .writeIndex binding (embedTerm v)
  | .writeValue binding i => .writeValue binding i

def embedControl : ANL.Memory.Control → Control
  | .eval e => .eval (embedTerm e)
  | .ret v => .ret (embedVal v)
  | .lengthReady site v init yes no => .lengthReady site (embedVal v) (embedTerm init) (embedTerm yes) (embedTerm no)
  | .allocate site n init yes no => .allocate site n init (embedTerm yes) (embedTerm no)
  | .readCheck binding i => .readCheck binding (embedVal i)
  | .readCell binding i => .readCell binding i
  | .writeCheck binding i v => .writeCheck binding (embedVal i) (embedTerm v)
  | .store binding i v => .store binding i v
  | .invoke f loan values => .invoke f loan (values.map embedVal)
  | .grant f loan values => .grant f loan (values.map embedVal)
  | .close binding site v => .close binding site (embedVal v)
  | .revoke v => .revoke (embedVal v)
  | .restore v => .restore (embedVal v)
  | .trap kind => .trap (embedMemoryTrap kind)
  | .invalid => .invalid

def embedState (s : ANL.Memory.State) : State :=
  ⟨embedControl s.control, embedActivation s.current, s.kont.map embedFrame, s.world⟩

@[simp] theorem embedState_world : (embedState s).world = s.world := rfl
@[simp] theorem embedState_accessible : (embedState s).accessible = s.accessible := by
  cases s with | mk ctrl a k w => cases ctrl <;> rfl
@[simp] theorem embed_initial : embedState (ANL.Memory.initial p) = initial (embedProgram p) := rfl

theorem embed_resume : embedState (ANL.Memory.resume r a k w) =
    resume (embedResult r) (embedActivation a) (k.map embedFrame) w := by
  cases r <;> rfl

theorem embed_beginArguments : embedState (ANL.Memory.beginArguments f loan args values a k w) =
    beginArguments f loan (args.map embedTerm) (values.map embedVal) (embedActivation a) (k.map embedFrame) w := by
  cases args <;> rfl

theorem embed_update : update (embedEnv env) i (embedVal v) =
    (APL.FlatProducts.update env i v).map embedEnv := by
  induction env generalizing i with
  | nil => rfl
  | cons first rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (update (embedEnv rest) i (embedVal v)).map (fun xs => embedVal first :: xs) = _
      rw [ih]
      simp [APL.FlatProducts.update, Option.map_map, Function.comp_def, embedEnv]

theorem embed_legacy_type_ne (h : v.type ≠ .scalar t) :
    (embedVal v).type ≠ .scalar (.legacy t) := by
  rw [embedVal_type]
  change embedTy v.type ≠ embedTy (.scalar t)
  exact fun eq => h (embedTy_injective eq)

theorem embed_step_relation (h : ANL.Memory.Step p responses s next) :
    Step (embedProgram p) responses (embedState s) (embedState next) := by
  cases h
  all_goals try rw [embed_resume]
  all_goals try rw [embed_beginArguments]
  all_goals simp only [embedState, embedControl, embedFrame, embedActivation, embedTerm,
    List.map_cons, List.map_nil]
  case lit => apply Step.lit <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case localFound => apply Step.localFound <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case localMissing => apply Step.localMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case letEval => apply Step.letEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case letMutEval => apply Step.letMutEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case assignEval => apply Step.assignEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case whileEval => apply Step.whileEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case ifEval => apply Step.ifEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case unaryEval => apply Step.unaryEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case binaryEval => apply Step.binaryEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case call => apply Step.call <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case tupleEmpty => apply Step.tupleEmpty <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case tupleFirst => apply Step.tupleFirst <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case projectEval => apply Step.projectEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case heapEval => apply Step.heapEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case lengthFound => rw [← legacyResult_commutes]; apply Step.lengthFound <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case lengthMissing => apply Step.lengthMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readEval => apply Step.readEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readMissing => apply Step.readMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeEval => apply Step.writeEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeMissing => apply Step.writeMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeDenied => apply Step.writeDenied <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case callView => apply Step.callView <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case viewMissing => apply Step.viewMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case viewDenied => apply Step.viewDenied <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case bindReturn => apply Step.bindReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case scopeReturn cell rest v a k w he => apply Step.scopeReturn (cell := embedVal cell) <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case scopeMissing => apply Step.scopeMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case assignReturn => apply Step.assignReturn; simp_all only [embed_update, Option.map_some, Option.map_none]
  case assignMissing => apply Step.assignMissing; simp_all only [embed_update, Option.map_some, Option.map_none]
  case ifTrue => apply Step.ifTrue <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case ifFalse => apply Step.ifFalse <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case ifWrong => apply Step.ifWrong; apply embed_legacy_type_ne; assumption
  case unaryReturn => rw [← unary_commutes]; apply Step.unaryReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case short => apply Step.short <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case rightEval => apply Step.rightEval <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case binaryReturn => rw [← binary_commutes]; apply Step.binaryReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case argumentReturn => apply Step.argumentReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case callResult => apply Step.callResult <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case whileTrue => apply Step.whileTrue <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case whileFalse => apply Step.whileFalse <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case whileWrong => apply Step.whileWrong; apply embed_legacy_type_ne; assumption
  case whileAgain => apply Step.whileAgain <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case bodyWrong => apply Step.bodyWrong; apply embed_legacy_type_ne; assumption
  case fieldNext => apply Step.fieldNext <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case fieldsDone =>
    rw [← construct_commutes, List.map_reverse]
    apply Step.fieldsDone <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case fieldTuple => apply Step.fieldTuple <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case projectReturn => rw [← project_commutes]; apply Step.projectReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case heapLengthReturn => apply Step.heapLengthReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case heapInitialReturn => apply Step.heapInitialReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case heapInitialWrong => apply Step.heapInitialWrong; apply embed_legacy_type_ne; assumption
  case ownerReturn => apply Step.ownerReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readIndexReturn => apply Step.readIndexReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeIndexReturn => apply Step.writeIndexReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeValueReturn => apply Step.writeValueReturn <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeValueWrong => apply Step.writeValueWrong; apply embed_legacy_type_ne; assumption
  case negativeLength => apply Step.negativeLength <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case nonnegativeLength => apply Step.nonnegativeLength <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case lengthWrong => apply Step.lengthWrong; apply embed_legacy_type_ne; assumption
  case allocated => apply Step.allocated <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case allocationRefused => apply Step.allocationRefused <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case allocationRejected => apply Step.allocationRejected <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readChecked => apply Step.readChecked <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readBounds => apply Step.readBounds <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readWrong => apply Step.readWrong; apply embed_legacy_type_ne; assumption
  case readValue => apply Step.readValue <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case readUnavailable => apply Step.readUnavailable <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeChecked => apply Step.writeChecked <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeBounds => apply Step.writeBounds <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case writeWrong => apply Step.writeWrong; apply embed_legacy_type_ne; assumption
  case stored => apply Step.stored <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case storeUnavailable => apply Step.storeUnavailable <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case invoke f fn loan values a k w hf hm =>
    apply Step.invoke (fn := embedFunction fn) <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case invokeMissing => apply Step.invokeMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case invokeMode f fn loan values a k w hf hm =>
    apply Step.invokeMode (fn := embedFunction fn) <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case grant f fn loan values a k w hf =>
    apply Step.grant (fn := embedFunction fn) <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case grantMissing => apply Step.grantMissing <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case closed => apply Step.closed <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case closeUnavailable => apply Step.closeUnavailable <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case closeWrong kont binding site value a w bad =>
    apply Step.closeWrong <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
    cases kont with
    | nil => simp
    | cons frame rest =>
      cases frame <;> simp_all [embedFrame]

  case revoke => apply Step.revoke <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case revokeWrong kont value a w bad =>
    apply Step.revokeWrong <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
    cases kont with
    | nil => simp
    | cons frame rest =>
      cases frame <;> simp_all [embedFrame]

  case restore => apply Step.restore <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
  case restoreWrong kont value a w bad =>
    apply Step.restoreWrong <;> first | assumption | simp_all [embed_update, shortCircuit_commutes, embedVal_type, embedProgram, embedFunction, Array.getElem?_map, embedEnv, List.getElem?_map]
    cases kont with
    | nil => simp
    | cons frame rest =>
      cases frame <;> simp_all [embedFrame]


@[simp] theorem embed_isStopped : isStopped (embedState s) = ANL.Memory.isStopped s := by
  cases s with
  | mk ctrl a k w =>
    cases ctrl <;> simp [isStopped, ANL.Memory.isStopped, embedState, embedControl, List.isEmpty_map]

theorem embed_step : step (embedProgram p) responses (embedState s) =
    (ANL.Memory.step p responses s).map embedState := by
  cases hs : ANL.Memory.step p responses s with
  | none =>
    have stopped := ANL.Memory.isStopped_iff.mpr hs
    exact isStopped_iff.mp (by simpa only [embed_isStopped] using stopped)
  | some next =>
    exact step_complete (embed_step_relation (ANL.Memory.step_sound hs))

theorem embed_steps (h : ANL.Memory.Steps p responses s last) :
    Steps (embedProgram p) responses (embedState s) (embedState last) := by
  induction h with
  | refl => exact .refl
  | head first rest ih => exact .head (embed_step_relation first) ih

theorem embed_stepsN (h : ANL.Memory.StepsN p responses n s last) :
    StepsN (embedProgram p) responses n (embedState s) (embedState last) := by
  induction h with
  | zero => exact .zero
  | succ first rest ih => exact .succ (embed_step_relation first) ih

def embedRunResult : ANL.Memory.RunResult → RunResult
  | .completed s => .completed (embedState s)
  | .exhausted s => .exhausted (embedState s)

@[simp] theorem embedRunResult_state : (embedRunResult r).state = embedState r.state := by
  cases r <;> rfl

/-- Exact equal-transition-budget equality for the historical Core injection, including cutoffs. -/
theorem embed_execute : execute (embedProgram p) responses budget (embedState s) =
    embedRunResult (ANL.Memory.execute p responses budget s) := by
  induction budget generalizing s with
  | zero => simp only [execute, ANL.Memory.execute, embed_isStopped]; split <;> rfl
  | succ budget ih =>
    simp only [execute, ANL.Memory.execute, embed_step]
    cases ANL.Memory.step p responses s with
    | none => rfl
    | some next => exact ih

theorem embed_execute_world :
    (execute (embedProgram p) responses budget (embedState s)).state.world =
      (ANL.Memory.execute p responses budget s).state.world := by
  rw [embed_execute, embedRunResult_state, embedState_world]

theorem embed_execute_entry : execute (embedProgram p) responses budget (initial (embedProgram p)) =
    embedRunResult (ANL.Memory.execute p responses budget (ANL.Memory.initial p)) := by
  rw [← embed_initial, embed_execute]

end ANL.Words
