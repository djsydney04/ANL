import APL.FlatProductsSafety

namespace APL.FlatProducts

def embedTerm : LocalState.Term → Term
  | .lit v => .lit (.scalar v)
  | .local i => .local i
  | .letE a b => .letE (embedTerm a) (embedTerm b)
  | .letMut a b => .letMut (embedTerm a) (embedTerm b)
  | .assign i a => .assign i (embedTerm a)
  | .whileE c b => .whileE (embedTerm c) (embedTerm b)
  | .ifE c a b => .ifE (embedTerm c) (embedTerm a) (embedTerm b)
  | .unary op a => .unary op (embedTerm a)
  | .binary op a b => .binary op (embedTerm a) (embedTerm b)
  | .call f args => .call f (args.map embedTerm)

def embedEnv (env : APL.Env) : Env := env.map Val.scalar

def embedFrame : LocalState.Frame → Frame
  | .bind permission body => .bind permission (embedTerm body)
  | .scope => .scope
  | .assign i => .assign i
  | .ifF a b => .ifF (embedTerm a) (embedTerm b)
  | .unary op => .unary op
  | .left op b => .left op (embedTerm b)
  | .right op a => .right op (.scalar a)
  | .arguments f remaining values => .arguments f (remaining.map embedTerm) (embedEnv values)
  | .callReturn caller => .callReturn (embedEnv caller)
  | .condition c b => .condition (embedTerm c) (embedTerm b)
  | .body c b => .body (embedTerm c) (embedTerm b)

def embedState : LocalState.State → State
  | .eval e env k => .eval (embedTerm e) (embedEnv env) (k.map embedFrame)
  | .ret v env k => .ret (.scalar v) (embedEnv env) (k.map embedFrame)
  | .invoke f values caller k => .invoke f (embedEnv values) (embedEnv caller) (k.map embedFrame)
  | .trap kind => .trap kind
  | .invalid => .invalid

def embedFunction (fn : LocalState.Function) : Function :=
  ⟨fn.name, fn.params.map Ty.scalar, .scalar fn.result, embedTerm fn.body⟩

def embedFunctions (fs : LocalState.Functions) : Functions := fs.map embedFunction

def embedSignatures (sigs : LocalState.Signatures) : Signatures :=
  sigs.map fun (params, result) => (params.map Ty.scalar, Ty.scalar result)

def embedCtx (Γ : LocalState.Ctx) : Ctx := Γ.map fun (t, permission) => (Ty.scalar t, permission)

theorem embed_typed (h : LocalState.HasType sigs Γ e t) :
    HasType (embedSignatures sigs) (embedCtx Γ) (embedTerm e) (.scalar t) := by
  induction h using LocalState.HasType.rec
    (motive_2 := fun Γ es ts _ =>
      ArgsTyped (embedSignatures sigs) (embedCtx Γ) (es.map embedTerm) (ts.map Ty.scalar)) <;> (try simp only [embedTerm])
  case lit => exact .lit
  case «local» Γ index t permission hi => exact .local (permission := permission) (by simp [embedCtx, List.getElem?_map, hi])
  case letE _ _ ha hb => exact .letE ha hb
  case letMut _ _ ha hb => exact .letMut ha hb
  case assign hi _ ha => exact .assign (by simp [embedCtx, List.getElem?_map, hi]) ha
  case whileE _ _ hc hb => exact .whileE hc hb
  case ifE _ _ _ hc ha hb => exact .ifE hc ha hb
  case unary _ ha => exact .unary ha
  case binary _ _ hop ha hb => exact .binary ha hb (by simp [binaryType, hop])
  case call hf _ ha => exact .call (by simp [embedSignatures, Array.getElem?_map, hf]) ha
  case nil => exact .nil
  case cons _ _ ha hb => exact .cons ha hb

theorem embed_signatures : signatures (embedFunctions fs) = embedSignatures (LocalState.signatures fs) := by
  simp [signatures, embedFunctions, embedFunction, embedSignatures, LocalState.signatures, Array.map_map]

theorem embed_wellTyped (h : LocalState.WellTyped fs) : WellTyped (embedFunctions fs) := by
  intro f fn hf
  simp only [embedFunctions, Array.getElem?_map, Option.map_eq_some_iff] at hf
  obtain ⟨old, ho, rfl⟩ := hf
  simpa [embed_signatures, embedFunction, immutable, LocalState.immutable, embedCtx,
    List.map_map, List.map_reverse, Function.comp_def] using embed_typed (h f old ho)

theorem embed_update : update (embedEnv env) i (.scalar v) =
    (LocalState.update env i v).map embedEnv := by
  induction env generalizing i with
  | nil => rfl
  | cons a env ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (update (embedEnv env) i (.scalar v)).map (Val.scalar a :: ·) =
        ((LocalState.update env i v).map (a :: ·)).map embedEnv
      rw [ih]
      simp [Option.map_map, embedEnv, Function.comp_def]

theorem embed_resume : embedState (LocalState.resume r env k) =
    resume (embedResult r) (embedEnv env) (k.map embedFrame) := by
  cases r <;> rfl

theorem embed_step (h : LocalState.Step fs s s') :
    Step (embedFunctions fs) (embedState s) (embedState s') := by
  cases h <;> simp only [embedState, embedTerm, embedFrame, List.map_cons, List.map_nil]
  case lit => exact .lit
  case localFound hv => exact .localFound (by simp [embedEnv, List.getElem?_map, hv])
  case localMissing hv => exact .localMissing (by simp [embedEnv, List.getElem?_map, hv])
  case letEval => exact .letEval
  case letMutEval => exact .letMutEval
  case bindReturn => exact .bindReturn
  case scopeReturn => exact .scopeReturn
  case scopeMissing => exact .scopeMissing
  case assignEval => exact .assignEval
  case assignReturn hu => exact .assignReturn (by simp [embed_update, hu])
  case assignMissing hu => exact .assignMissing (by simp [embed_update, hu])
  case ifEval => exact .ifEval
  case ifTrue => exact .ifTrue
  case ifFalse => exact .ifFalse
  case ifInt => exact .ifInt
  case ifUnit => exact .ifUnit
  case unaryEval => exact .unaryEval
  case unaryReturn v env op k =>
    change Step _ _ (embedState (LocalState.resume (APL.unary op v) env k))
    rw [embed_resume]
    exact .unaryReturn
  case binaryEval => exact .binaryEval
  case short hs => exact .short hs
  case rightEval hs => exact .rightEval hs
  case binaryReturn v env op a k =>
    change Step _ _ (embedState (LocalState.resume (APL.binary op a v) env k))
    rw [embed_resume]
    exact .binaryReturn
  case callEmpty => exact .callEmpty
  case callFirst => exact .callFirst
  case argumentNext => exact .argumentNext
  case argumentsDone => exact .argumentsDone
  case invoke f fn values env k hf =>
    exact Step.invoke (fn := embedFunction fn) (by simp [embedFunctions, Array.getElem?_map, hf])
  case invalidFunction hf => exact .invalidFunction (by simp [embedFunctions, Array.getElem?_map, hf])
  case callReturn => exact .callReturn
  case whileEval => exact .whileEval
  case whileTrue => exact .whileTrue
  case whileFalse => exact .whileFalse
  case whileInt => exact .whileInt
  case whileUnit => exact .whileUnit
  case whileAgain => exact .whileAgain
  case bodyInt => exact .bodyInt
  case bodyBool => exact .bodyBool

theorem embed_steps (h : LocalState.Steps fs s last) :
    Steps (embedFunctions fs) (embedState s) (embedState last) := by
  induction h with
  | refl => exact .refl
  | head hs _ ih => exact .head (embed_step hs) ih

theorem embed_stopped (h : LocalState.step fs s = none) : step (embedFunctions fs) (embedState s) = none := by
  rcases LocalState.stopped_iff.mp h with terminal | invalid
  · cases terminal <;> rfl
  · subst s; rfl

theorem embed_finite_run (h : LocalState.run fs fuel s = some last) :
    ∃ budget, run (embedFunctions fs) budget (embedState s) = some (embedState last) := by
  obtain ⟨trace, stop⟩ := LocalState.run_sound h
  exact run_complete (embed_steps trace) (embed_stopped stop)

theorem embed_finite_value (h : LocalState.run fs fuel (.eval e env []) = some (.ret v final [])) :
    ∃ budget, run (embedFunctions fs) budget (.eval (embedTerm e) (embedEnv env) []) =
      some (.ret (.scalar v) (embedEnv final) []) := embed_finite_run h

theorem embed_finite_trap (h : LocalState.run fs fuel (.eval e env []) = some (.trap kind)) :
    ∃ budget, run (embedFunctions fs) budget (.eval (embedTerm e) (embedEnv env) []) =
      some (.trap kind) := embed_finite_run h

end APL.FlatProducts
