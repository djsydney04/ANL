import APL.VCGCalls
import APL.LocalStateRun

namespace APL.StateVCG
open VCG

/-- A continuation observes both the expression value and its current local state. -/
abbrev StatePost := SymTerm → List SymTerm → Option Formula

def StatePostHolds (model : Model) (post : StatePost) (v : Val) (env : Env) : Prop :=
  ∃ s syms formula, post s syms = some formula ∧ formula.Holds model ∧
    Denotes model s v ∧ EnvRep model syms env

def updateSymbols : List SymTerm → Nat → SymTerm → Option (List SymTerm)
  | [], _, _ => none
  | _ :: ss, 0, s => some (s :: ss)
  | a :: ss, i + 1, s => (updateSymbols ss i s).map (a :: ·)

def scopePost (post : StatePost) : StatePost
  | v, _ :: env => post v env
  | _, [] => none

def argumentsWP (generate : LocalState.Term → List SymTerm → StatePost → Option Formula) :
    List LocalState.Term → List SymTerm →
      (List SymTerm → List SymTerm → Option Formula) → Option Formula
  | [], env, post => post [] env
  | a :: args, env, post => generate a env fun v current =>
      argumentsWP generate args current (fun vs final => post (v :: vs) final)

def invokeWP (fs : LocalState.Functions) (preconditions : Preconditions)
    (generate : LocalState.Term → List SymTerm → StatePost → Option Formula)
    (function : Nat) (args caller : List SymTerm) (post : StatePost) : Option Formula := do
  let fn ← fs[function]?
  if args.length = fn.params.length then
    let (defined, truth) ← requiresVC args (preconditions function)
    let body ← generate fn.body args.reverse (fun value _ => post value caller)
    return .and defined (.and truth body)
  else none

/-- The height bounds syntax and inlined bodies, independently of machine fuel.
This operational generator does not check static binding permissions. -/
def wp (fs : LocalState.Functions) (preconditions : Preconditions) :
    Nat → LocalState.Term → List SymTerm → StatePost → Option Formula
  | 0, _, _, _ => none
  | height + 1, e, env, post =>
    match e with
    | .lit v => post (.lit (VCG.embed v)) env
    | .local i => env[i]?.bind (fun value => post value env)
    | .letE a b | .letMut a b => wp fs preconditions height a env fun v current =>
        wp fs preconditions height b (v :: current) (scopePost post)
    | .assign i a => wp fs preconditions height a env fun v current => do
        let updated ← updateSymbols current i v
        post (.lit .unit) updated
    | .whileE _ _ => none
    | .ifE c a b => wp fs preconditions height c env fun v current => do
        let yes ← wp fs preconditions height a current post
        let no ← wp fs preconditions height b current post
        return .and (.boolean v) (.and (.imp (.holds v) yes) (.imp (.holds (.unary .not v)) no))
    | .unary op a => wp fs preconditions height a env fun v current =>
        unaryWP op v (fun result => post result current)
    | .binary op a b => wp fs preconditions height a env fun va current =>
        let rhs := wp fs preconditions height b current fun vb final =>
          binaryWP op va vb (fun result => post result final)
        if shortable op then do
          let rest ← rhs
          let skip ← post va current
          return .and (.imp (shortGuard op va) skip) (.imp (.not (shortGuard op va)) rest)
        else rhs
    | .call f args => argumentsWP (wp fs preconditions height) args env
        (fun values current => invokeWP fs preconditions (wp fs preconditions height) f values current post)

theorem update_rep (h : EnvRep model syms env) (hv : Denotes model s v)
    (hu : updateSymbols syms i s = some syms') :
    ∃ env', LocalState.update env i v = some env' ∧ EnvRep model syms' env' := by
  induction h generalizing i syms' with
  | nil => simp [updateSymbols] at hu
  | cons hd _ ih =>
    cases i with
    | zero => simp only [updateSymbols, Option.some.injEq] at hu; subst syms'; exact ⟨_, rfl, .cons hv ‹_›⟩
    | succ i =>
      simp only [updateSymbols, Option.map_eq_some_iff] at hu
      obtain ⟨ss, hs, rfl⟩ := hu
      obtain ⟨vs, he, hr⟩ := ih hs
      exact ⟨_, by simp [LocalState.update, he], .cons hd hr⟩

private theorem lift_safe_value (h : Safe p (Program.liftResult r 0)) :
    ∃ v, r = .value v ∧ p v := by
  cases r with
  | value v => exact ⟨v, rfl, h⟩
  | trap kind | invalid => exact False.elim h

private theorem unary_value (h : unaryWP op a post = some formula)
    (hf : formula.Holds model) (ha : Denotes model a v) :
    ∃ result, unary op v = .value result ∧ PostHolds model post result :=
  lift_safe_value (unary_wp_sound h hf ha)

private theorem binary_value (h : binaryWP op a b post = some formula)
    (hf : formula.Holds model) (ha : Denotes model a va) (hb : Denotes model b vb)
    (hs : shortCircuit op va = false) :
    ∃ result, binary op va vb = .value result ∧ PostHolds model post result :=
  lift_safe_value (binary_wp_sound h hf ha hb hs)

private theorem steps_trans (h : LocalState.Steps fs s mid) (h' : LocalState.Steps fs mid last) :
    LocalState.Steps fs s last := by
  induction h with
  | refl => exact h'
  | head hs _ ih => exact .head hs (ih h')

private theorem stopped_unique (ha : LocalState.Steps fs s a) (hb : LocalState.Steps fs s b)
    (sa : LocalState.step fs a = none) (sb : LocalState.step fs b = none) : a = b := by
  induction ha generalizing b with
  | refl =>
    cases hb with
    | refl => rfl
    | head hs _ => rw [LocalState.step_complete hs] at sa; contradiction
  | head hs _ ih =>
    cases hb with
    | refl => rw [LocalState.step_complete hs] at sb; contradiction
    | head hs' rest =>
      have same := LocalState.deterministic hs hs'
      subst same
      exact ih rest sa sb

theorem run_result (hs : LocalState.Steps fs s (.ret v env []))
    (hr : LocalState.run fs fuel s = some last) : last = .ret v env [] := by
  obtain ⟨trace, stopped⟩ := LocalState.run_sound hr
  exact stopped_unique trace hs stopped rfl

private def ArgsPostHolds (model : Model)
    (post : List SymTerm → List SymTerm → Option Formula) (values env : Env) : Prop :=
  ∃ args syms formula, post args syms = some formula ∧ formula.Holds model ∧
    EnvRep model args values ∧ EnvRep model syms env

private def argStart (f : Nat) (args : List LocalState.Term) (previous : List Val)
    (env : Env) (k : List LocalState.Frame) : LocalState.State :=
  match args with
  | [] => .invoke f previous env k
  | a :: args => .eval a env (.arguments f args previous :: k)

private theorem argument_step : LocalState.Step fs
    (.ret v env (.arguments f args previous :: k)) (argStart f args (v :: previous) env k) := by
  cases args with
  | nil => exact .argumentsDone
  | cons a args => exact .argumentNext

private theorem args_trace
    (ih : ∀ {e syms post formula env k}, generate e syms post = some formula →
      EnvRep model syms env → formula.Holds model →
      ∃ v env', LocalState.Steps fs (.eval e env k) (.ret v env' k) ∧
        StatePostHolds model post v env')
    (hwp : argumentsWP generate args syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ∃ values finalEnv,
      LocalState.Steps fs (argStart f args previous env k)
        (.invoke f (values.reverse ++ previous) finalEnv k) ∧
      ArgsPostHolds model post values finalEnv := by
  induction args generalizing syms post formula env previous with
  | nil => exact ⟨[], env, .refl, [], syms, formula, hwp, hformula, .nil, henv⟩
  | cons a args ihArgs =>
    obtain ⟨v, env', trace, s, syms', q, hq, hqvalid, hd, he⟩ :=
      ih (k := .arguments f args previous :: k) hwp henv hformula
    obtain ⟨values, finalEnv, rest, ss, finalSyms, g, hg, hgvalid, hvs, hfinal⟩ :=
      ihArgs (previous := v :: previous) hq he hqvalid
    refine ⟨v :: values, finalEnv, ?_, s :: ss, finalSyms, g, hg, hgvalid, .cons hd hvs, hfinal⟩
    apply steps_trans trace
    apply LocalState.Steps.head argument_step
    simpa [List.reverse_cons, List.append_assoc] using rest

/-- A generated formula establishes a finite prefix through the current continuation. -/
theorem wp_trace (hwp : wp fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ∃ v env', LocalState.Steps fs (.eval e env k) (.ret v env' k) ∧
      StatePostHolds model post v env' := by
  induction height generalizing e syms post formula env k with
  | zero => simp [wp] at hwp
  | succ height ih =>
    cases e with
    | lit v => exact ⟨v, env, .head .lit .refl, .lit (VCG.embed v), syms, formula, hwp, hformula, rfl, henv⟩
    | «local» i =>
      simp only [wp, Option.bind_eq_some_iff] at hwp
      obtain ⟨s, hs, hq⟩ := hwp
      obtain ⟨v, hv, hd⟩ := EnvRep.lookup henv hs
      exact ⟨v, env, .head (.localFound hv) .refl, s, syms, formula, hq, hformula, hd, henv⟩
    | letE a b | letMut a b =>
      obtain ⟨v, env', trace, s, syms', q, hq, hqvalid, hd, he⟩ :=
        ih (k := .bind _ b :: k) hwp henv hformula
      obtain ⟨w, finalEnv, bodyTrace, result, finalSyms, g, hg, hgvalid, hw, hfinal⟩ :=
        ih (k := .scope :: k) hq (.cons hd he) hqvalid
      cases finalSyms with
      | nil => simp [scopePost] at hg
      | cons head tail =>
        cases hfinal with
        | cons _ hfinal =>
          refine ⟨w, _, ?_, result, tail, g, hg, hgvalid, hw, hfinal⟩
          apply LocalState.Steps.head (by first | exact .letEval | exact .letMutEval)
          apply steps_trans trace
          apply LocalState.Steps.head .bindReturn
          exact steps_trans bodyTrace (.head .scopeReturn .refl)
    | assign i a =>
      obtain ⟨v, env', trace, s, syms', q, hq, hqvalid, hd, he⟩ :=
        ih (k := .assign i :: k) hwp henv hformula
      simp only [bind, Option.bind_eq_some_iff] at hq
      obtain ⟨updated, hu, hp⟩ := hq
      obtain ⟨finalEnv, hupdate, hfinal⟩ := update_rep he hd hu
      exact ⟨.unit, finalEnv, .head .assignEval (steps_trans trace (.head (.assignReturn hupdate) .refl)),
        .lit .unit, updated, q, hp, hqvalid, rfl, hfinal⟩
    | whileE c b => simp [wp] at hwp
    | ifE c a b =>
      obtain ⟨v, env', trace, s, syms', q, hq, hqvalid, hd, he⟩ :=
        ih (k := .ifF a b :: k) hwp henv hformula
      simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hq
      obtain ⟨yes, hyes, no, hno, hq⟩ := hq
      cases hq
      obtain ⟨test, ht⟩ := hqvalid.1
      rw [hd] at ht
      cases v with
      | int _ | unit => simp [VCG.embed] at ht
      | bool test' =>
        cases ht
        unfold Denotes at hd
        cases test with
        | false =>
          have valid := hqvalid.2.2 (by simp [Formula.Holds, SymTerm.eval, hd, VCG.embed, mUnary])
          obtain ⟨w, finalEnv, branchTrace, hp⟩ := ih (k := k) hno he valid
          exact ⟨w, finalEnv, .head .ifEval (steps_trans trace (.head .ifFalse branchTrace)), hp⟩
        | true =>
          obtain ⟨w, finalEnv, branchTrace, hp⟩ := ih (k := k) hyes he (hqvalid.2.1 hd)
          exact ⟨w, finalEnv, .head .ifEval (steps_trans trace (.head .ifTrue branchTrace)), hp⟩
    | unary op a =>
      obtain ⟨v, env', trace, s, syms', q, hq, hqvalid, hd, he⟩ :=
        ih (k := .unary op :: k) hwp henv hformula
      obtain ⟨w, hw, result, g, hg, hgvalid, hresult⟩ := unary_value hq hqvalid hd
      refine ⟨w, env', .head .unaryEval (steps_trans trace ?_), result, syms', g, hg, hgvalid, hresult, he⟩
      have last := LocalState.Step.unaryReturn (fs := fs) (op := op) (v := v) (env := env') (k := k)
      rw [hw] at last
      exact .head last .refl
    | binary op a b =>
      obtain ⟨va, env', trace, sa, syms', q, hq, hqvalid, hd, he⟩ :=
        ih (k := .left op b :: k) hwp henv hformula
      have rightTrace {rest : Formula} (hrest : wp fs preconditions height b syms'
          (fun vb final => binaryWP op sa vb (fun result => post result final)) = some rest)
          (hvalid : rest.Holds model) (hs : shortCircuit op va = false) :
          ∃ w finalEnv, LocalState.Steps fs (.eval (.binary op a b) env k) (.ret w finalEnv k) ∧
            StatePostHolds model post w finalEnv := by
        obtain ⟨vb, finalEnv, btrace, sb, finalSyms, g, hg, hgvalid, hb, hfinal⟩ :=
          ih (k := .right op va :: k) hrest he hvalid
        obtain ⟨w, hw, result, q', hq', hqvalid', hresult⟩ := binary_value hg hgvalid hd hb hs
        refine ⟨w, finalEnv, .head .binaryEval (steps_trans trace (.head (.rightEval hs) (steps_trans btrace ?_))),
          result, finalSyms, q', hq', hqvalid', hresult, hfinal⟩
        have last := LocalState.Step.binaryReturn (fs := fs) (op := op) (a := va) (v := vb) (env := finalEnv) (k := k)
        rw [hw] at last
        exact .head last .refl
      cases hop : shortable op with
      | false =>
        simp only [hop, Bool.false_eq_true, ite_false] at hq
        exact rightTrace hq hqvalid (not_shortable hop)
      | true =>
        simp only [hop, ite_true, bind, Option.bind_eq_some_iff, Option.pure_def] at hq
        obtain ⟨rest, hrest, skip, hskip, hq⟩ := hq
        cases hq
        cases hs : shortCircuit op va with
        | true => exact ⟨va, env', .head .binaryEval (steps_trans trace (.head (.short hs) .refl)),
            sa, syms', skip, hskip, hqvalid.1 ((short_guard hd).mpr hs), hd, he⟩
        | false =>
          apply rightTrace hrest (hqvalid.2 ?_) hs
          intro hshort
          have hh := (short_guard hd).mp hshort
          rw [hs] at hh
          contradiction
    | call function args =>
      obtain ⟨values, caller, argTrace, symbols, callerSyms, q, hq, hqvalid, hargs, hcaller⟩ :=
        args_trace (fun h he hf => ih h he hf) (f := function) (previous := []) (k := k) hwp henv hformula
      simp only [List.append_nil] at argTrace
      simp only [invokeWP, bind, Option.bind_eq_some_iff, Option.pure_def] at hq
      obtain ⟨fn, hfn, hq⟩ := hq
      split at hq
      · simp only [Option.bind_eq_some_iff] at hq
        obtain ⟨⟨defined, truth⟩, _, body, hbody, hq⟩ := hq
        cases hq
        obtain ⟨w, calleeFinal, bodyTrace, result, finalSyms, g, hg, hgvalid, hw, _⟩ :=
          ih (k := .callReturn caller :: k) hbody (env_reverse hargs) hqvalid.2.2
        refine ⟨w, caller, ?_, result, callerSyms, g, hg, hgvalid, hw, hcaller⟩
        have first : LocalState.Step fs (.eval (.call function args) env k) (argStart function args [] env k) := by
          cases args with
          | nil => exact .callEmpty
          | cons a args => exact .callFirst
        exact .head first (steps_trans argTrace (.head (.invoke hfn) (steps_trans bodyTrace (.head .callReturn .refl))))
      · contradiction

/-- Exhausted transition budgets are allowed; every completed run must satisfy the post. -/
def RunSafe (post : Val → Env → Prop) : Option LocalState.State → Prop
  | none => True
  | some (.ret value env []) => post value env
  | _ => False

theorem wp_run_sound (hwp : wp fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    RunSafe (StatePostHolds model post) (LocalState.run fs fuel (.eval e env [])) := by
  obtain ⟨v, finalEnv, trace, hp⟩ := wp_trace (k := []) hwp henv hformula
  cases hr : LocalState.run fs fuel (.eval e env []) with
  | none => trivial
  | some last =>
    have same := run_result trace hr
    subst last
    exact hp

theorem wp_run_complete (hwp : wp fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ∃ fuel v finalEnv,
      LocalState.run fs fuel (.eval e env []) = some (.ret v finalEnv []) ∧
        StatePostHolds model post v finalEnv := by
  obtain ⟨v, finalEnv, trace, hp⟩ := wp_trace (k := []) hwp henv hformula
  obtain ⟨fuel, hr⟩ := LocalState.run_complete trace rfl
  exact ⟨fuel, v, finalEnv, hr, hp⟩

theorem wp_steps_value (hwp : wp fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model)
    (hs : LocalState.Steps fs (.eval e env []) (.ret v finalEnv [])) :
    StatePostHolds model post v finalEnv := by
  obtain ⟨w, finalEnv', trace, hp⟩ := wp_trace (k := []) hwp henv hformula
  have same := stopped_unique hs trace rfl rfl
  cases same
  exact hp

theorem wp_steps_no_trap (hwp : wp fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ¬ LocalState.Steps fs (.eval e env []) (.trap kind) := by
  intro hs
  obtain ⟨w, finalEnv, trace, _⟩ := wp_trace (k := []) hwp henv hformula
  have same := stopped_unique hs trace rfl rfl
  cases same

theorem wp_steps_no_invalid (hwp : wp fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ¬ LocalState.Steps fs (.eval e env []) .invalid := by
  intro hs
  obtain ⟨w, finalEnv, trace, _⟩ := wp_trace (k := []) hwp henv hformula
  have same := stopped_unique hs trace rfl rfl
  cases same

theorem invoke_preconditions (hwp : invokeWP fs preconditions generate function args caller post = some formula)
    (hargs : EnvRep model args values) (hformula : formula.Holds model) :
    RequiresDefined (values.map VCG.embed) (preconditions function) ∧
      RequiresHold (values.map VCG.embed) (preconditions function) := by
  simp only [invokeWP, bind, Option.bind_eq_some_iff, Option.pure_def] at hwp
  obtain ⟨fn, _, hwp⟩ := hwp
  split at hwp
  · simp only [Option.bind_eq_some_iff] at hwp
    obtain ⟨⟨defined, truth⟩, hreq, body, _, he⟩ := hwp
    cases he
    have hs := requires_vc_sound hreq hargs
    exact ⟨hs.1.mp hformula.1, hs.2.mp hformula.2.1⟩
  · contradiction

end APL.StateVCG
