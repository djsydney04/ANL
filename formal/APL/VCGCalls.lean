import APL.VCGContracts

namespace APL.VCG

abbrev Preconditions := Nat → List Spec

def wpArguments (generate : Program.Term → List SymTerm → Post → Option Formula) :
    List Program.Term → List SymTerm → (List SymTerm → Option Formula) → Option Formula
  | [], _, post => post []
  | a :: args, env, post => generate a env (fun v => wpArguments generate args env (fun vs => post (v :: vs)))

def invokeWP (fs : Program.Functions) (preconditions : Preconditions)
    (generate : Program.Term → List SymTerm → Post → Option Formula)
    (function : Nat) (args : List SymTerm) (post : Post) : Option Formula := do
  let fn ← fs[function]?
  if args.length = fn.params.length then
    let (defined, truth) ← requiresVC args (preconditions function)
    let body ← generate fn.body args.reverse post
    return .and defined (.and truth body)
  else none

-- The bound limits the expanded syntax tree, independently of execution resources.
def wpCalls (fs : Program.Functions) (preconditions : Preconditions) :
    Nat → Program.Term → List SymTerm → Post → Option Formula
  | 0, _, _, _ => none
  | height + 1, e, env, post =>
    match e with
    | .lit v => post (.lit (embed v))
    | .local i => env[i]?.bind post
    | .letE a b => wpCalls fs preconditions height a env (fun v => wpCalls fs preconditions height b (v :: env) post)
    | .ifE c a b => wpCalls fs preconditions height c env fun v => do
        let yes ← wpCalls fs preconditions height a env post
        let no ← wpCalls fs preconditions height b env post
        return .and (.boolean v) (.and (.imp (.holds v) yes) (.imp (.holds (.unary .not v)) no))
    | .unary op a => wpCalls fs preconditions height a env (fun v => unaryWP op v post)
    | .binary op a b => wpCalls fs preconditions height a env fun va =>
        let rhs := wpCalls fs preconditions height b env (fun vb => binaryWP op va vb post)
        if shortable op then do
          let rest ← rhs
          let skip ← post va
          return .and (.imp (shortGuard op va) skip) (.imp (.not (shortGuard op va)) rest)
        else rhs
    | .call f args => wpArguments (wpCalls fs preconditions height) args env
        (fun values => invokeWP fs preconditions (wpCalls fs preconditions height) f values post)

private def SafeResult (post : α → Prop) : Except Program.Error (α × Nat) → Prop
  | .ok (v, _) => post v
  | .error .resourceLimit => True
  | .error (.trap _) | .error .invalid => False

private theorem safe_result_iff : SafeResult p out ↔ Safe p out := by
  cases out with
  | ok pair => cases pair; rfl
  | error err => cases err <;> rfl

private theorem bind_apply (x : Program.EvalM α) (f : α → Program.EvalM β) (n : Nat) :
    (x >>= f) n = match x n with
    | .ok (v, n') => f v n'
    | .error err => .error err := by
  change (Except.bind (x n) _) = _
  cases x n with
  | error err => rfl
  | ok p => cases p; rfl

private theorem fuel_then (x : Program.EvalM α) : (Program.takeFuel >>= fun _ => x) (fuel+1) = x fuel := by
  rw [bind_apply]
  rfl

private theorem safe_bind (x : Program.EvalM α) (f : α → Program.EvalM β)
    (hx : SafeResult p (x fuel)) (hf : ∀ v n, p v → SafeResult q (f v n)) :
    SafeResult q ((x >>= f) fuel) := by
  rw [bind_apply]
  cases he : x fuel with
  | error err =>
    cases err with
    | resourceLimit => trivial
    | trap _ | invalid => simp only [he, SafeResult] at hx
  | ok pair =>
    obtain ⟨v, n⟩ := pair
    exact hf v n (by simpa only [he, SafeResult] using hx)

private def ArgsPostHolds (model : Model) (post : List SymTerm → Option Formula) (values : Env) : Prop :=
  ∃ syms formula, post syms = some formula ∧ formula.Holds model ∧ EnvRep model syms values

private theorem arguments_sound
    (ih : ∀ {e syms post formula env depth fuel}, generate e syms post = some formula →
      EnvRep model syms env → formula.Holds model →
      SafeResult (PostHolds model post) (Program.eval fs depth env e fuel))
    (hwp : wpArguments generate args syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    SafeResult (ArgsPostHolds model post) ((args.mapM (Program.eval fs depth env)) fuel) := by
  induction args generalizing post formula fuel with
  | nil => exact ⟨[], formula, hwp, hformula, .nil⟩
  | cons a args ihArgs =>
    rw [List.mapM_cons]
    apply safe_bind (Program.eval fs depth env a) _ (ih hwp henv hformula)
    intro v n hv
    obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
    apply safe_bind _ _ (ihArgs hf hvalid)
    intro vs n' hvs
    obtain ⟨ss, g, hg, hvalid', hrep⟩ := hvs
    exact ⟨s :: ss, g, hg, hvalid', .cons hdenotes hrep⟩

theorem invokeWP_preconditions (hwp : invokeWP fs preconditions generate function args post = some formula)
    (hargs : EnvRep model args values) (hformula : formula.Holds model) :
    RequiresDefined (values.map embed) (preconditions function) ∧
      RequiresHold (values.map embed) (preconditions function) := by
  simp only [invokeWP, bind, Option.bind_eq_some_iff, Option.pure_def] at hwp
  obtain ⟨fn, _, hwp⟩ := hwp
  split at hwp
  · simp only [Option.bind_eq_some_iff] at hwp
    obtain ⟨⟨defined, truth⟩, hreq, body, _, he⟩ := hwp
    cases he
    have hs := requires_vc_sound hreq hargs
    exact ⟨hs.1.mp hformula.1, hs.2.mp hformula.2.1⟩
  · contradiction

private theorem wpCalls_result_sound (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    SafeResult (PostHolds model post) (Program.eval fs depth env e fuel) := by
  induction height generalizing e syms post formula env depth fuel with
  | zero => simp [wpCalls] at hwp
  | succ height ih =>
    cases depth with
    | zero => trivial
    | succ depth =>
      cases fuel with
      | zero => rw [Program.eval.eq_def]; trivial
      | succ fuel =>
        rw [Program.eval.eq_def]
        dsimp only
        rw [fuel_then]
        cases e with
        | lit v => exact ⟨.lit (embed v), formula, hwp, hformula, rfl⟩
        | «local» i =>
          simp only [wpCalls, Option.bind_eq_some_iff] at hwp
          obtain ⟨s, hs, hq⟩ := hwp
          obtain ⟨v, hv, hd⟩ := EnvRep.lookup henv hs
          dsimp only
          rw [hv]
          exact ⟨s, formula, hq, hformula, hd⟩
        | letE a b =>
          apply safe_bind _ _ (ih hwp henv hformula)
          intro v n hv
          obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
          exact ih hf (.cons hdenotes henv) hvalid
        | ifE c a b =>
          apply safe_bind _ _ (ih hwp henv hformula)
          intro v n hv
          obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
          simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at hf
          obtain ⟨yes, hyes, no, hno, he⟩ := hf
          cases he
          obtain ⟨test, ht⟩ := hvalid.1
          rw [hdenotes] at ht
          cases v with
          | int _ | unit => simp [embed] at ht
          | bool test' =>
            cases ht
            unfold Denotes at hdenotes
            cases test with
            | false =>
              apply ih hno henv
              apply hvalid.2.2
              simp [Formula.Holds, SymTerm.eval, hdenotes, embed, mUnary]
            | true => exact ih hyes henv (hvalid.2.1 hdenotes)
        | unary op a =>
          apply safe_bind _ _ (ih hwp henv hformula)
          intro v n hv
          obtain ⟨s, f, hf, hvalid, hdenotes⟩ := hv
          exact safe_result_iff.mpr (unary_wp_sound hf hvalid hdenotes)
        | binary op a b =>
          apply safe_bind _ _ (ih hwp henv hformula)
          intro va n hv
          obtain ⟨sa, f, hf, hvalid, hdenotes⟩ := hv
          cases hop : shortable op with
          | false =>
            simp only [hop, Bool.false_eq_true, ite_false] at hf
            have hs := not_shortable (v := va) hop
            simp only [hs, Bool.false_eq_true, ite_false]
            apply safe_bind _ _ (ih hf henv hvalid)
            intro vb n' hv
            obtain ⟨sb, g, hg, hvalid', hdenotes'⟩ := hv
            exact safe_result_iff.mpr (binary_wp_sound hg hvalid' hdenotes hdenotes' hs)
          | true =>
            simp only [hop, ite_true, bind, Option.bind_eq_some_iff, Option.pure_def] at hf
            obtain ⟨rest, hrest, skip, hskip, he⟩ := hf
            cases he
            cases hs : shortCircuit op va with
            | true =>
              exact ⟨sa, skip, hskip, hvalid.1 ((short_guard hdenotes).mpr hs), hdenotes⟩
            | false =>
              apply safe_bind _ _ (ih hrest henv (hvalid.2 (by
                intro hshort
                have := (short_guard hdenotes).mp hshort
                rw [hs] at this
                contradiction)))
              intro vb n' hv
              obtain ⟨sb, g, hg, hvalid', hdenotes'⟩ := hv
              exact safe_result_iff.mpr (binary_wp_sound hg hvalid' hdenotes hdenotes' hs)
        | call function args =>
          apply safe_bind _ _ (arguments_sound (fun h he hf => ih h he hf) hwp henv hformula)
          intro values n hvalues
          obtain ⟨symbols, f, hf, hvalid, hrep⟩ := hvalues
          simp only [invokeWP, bind, Option.bind_eq_some_iff, Option.pure_def] at hf
          obtain ⟨fn, hfn, hf⟩ := hf
          rw [hfn]
          split at hf
          · simp only [Option.bind_eq_some_iff] at hf
            obtain ⟨⟨defined, truth⟩, _, body, hbody, he⟩ := hf
            cases he
            exact ih hbody (env_reverse hrep) hvalid.2.2
          · contradiction

theorem wpCalls_eval_sound (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    Safe (PostHolds model post) (Program.eval fs depth env e fuel) :=
  safe_result_iff.mp (wpCalls_result_sound hwp henv hformula)

theorem wpCalls_value (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model)
    (he : Program.eval fs depth env e fuel = .ok (v, remaining)) : PostHolds model post v := by
  have h := wpCalls_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp henv hformula
  simpa only [he, Safe] using h

theorem wpCalls_no_trap (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    Program.eval fs depth env e fuel ≠ .error (.trap kind) := by
  intro he
  have h := wpCalls_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp henv hformula
  simp only [he, Safe] at h

theorem wpCalls_no_invalid (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    Program.eval fs depth env e fuel ≠ .error .invalid := by
  intro he
  have h := wpCalls_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp henv hformula
  simp only [he, Safe] at h

theorem wpCalls_steps_value (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model)
    (hs : Program.Steps fs (.eval e env []) (.ret v [])) : PostHolds model post v := by
  obtain ⟨depth, fuel, remaining, he⟩ := Program.eval_value_complete hs
  exact wpCalls_value hwp henv hformula he

theorem wpCalls_steps_no_trap (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ¬ Program.Steps fs (.eval e env []) (.trap kind) := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_trap_complete hs
  exact wpCalls_no_trap hwp henv hformula he

theorem wpCalls_steps_no_invalid (hwp : wpCalls fs preconditions height e syms post = some formula)
    (henv : EnvRep model syms env) (hformula : formula.Holds model) :
    ¬ Program.Steps fs (.eval e env []) .invalid := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_invalid_complete hs
  exact wpCalls_no_invalid hwp henv hformula he

def generateCallsContract (fs : Program.Functions) (calleePreconditions : Preconditions) (height : Nat)
    (params : List Ty) (body : Program.Term) (preconditions : List Spec) (post : Spec) :
    Option ContractVC := do
  let syms := parameterSymbols params.length
  let (defined, truth) ← requiresVC syms preconditions
  let formula ← wpCalls fs calleePreconditions height body syms.reverse (specPost syms post)
  return ⟨defined, truth, formula⟩

private theorem safe_mono (h : Safe p out) (hp : ∀ v, p v → q v) : Safe q out := by
  cases out with
  | ok pair => exact hp pair.1 h
  | error err => cases err with
    | resourceLimit => trivial
    | trap _ | invalid => exact h

theorem calls_contract_eval_sound {params : Env} (hgen : generateCallsContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    Safe (fun v => post.eval (params.map embed) (some (embed v)) = some (.bool true))
      (Program.eval fs depth params.reverse body fuel) := by
  simp only [generateCallsContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  have hp := typed_parameters_rep ht
  have htruth := ((requires_vc_sound hrequires hp).2).mpr hpre
  have hvalid := ha.2.2 params ht htruth
  have hs := wpCalls_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hwp (env_reverse hp) hvalid
  exact safe_mono hs (fun _ h => spec_post_sound h hp)

theorem calls_contract_preconditions_defined {params : Env} (hgen : generateCallsContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types) :
    RequiresDefined (params.map embed) preconditions := by
  simp only [generateCallsContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  exact ((requires_vc_sound hrequires (typed_parameters_rep ht)).1).mp (ha.1 params ht)

theorem calls_contract_nonvacuous (hgen : generateCallsContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) : ∃ params : Env, params.map Val.type = types ∧ RequiresHold (params.map embed) preconditions := by
  obtain ⟨params, ht, htruth⟩ := ha.2.1
  simp only [generateCallsContract, bind, Option.bind_eq_some_iff, Option.pure_def] at hgen
  obtain ⟨⟨defined, truth⟩, hrequires, formula, hwp, hgen⟩ := hgen
  cases hgen
  exact ⟨params, ht, ((requires_vc_sound hrequires (typed_parameters_rep ht)).2).mp htruth⟩

theorem calls_contract_steps_value {params : Env}
    (hgen : generateCallsContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions)
    (hs : Program.Steps fs (.eval body params.reverse []) (.ret v [])) :
    post.eval (params.map embed) (some (embed v)) = some (.bool true) := by
  obtain ⟨depth, fuel, remaining, he⟩ := Program.eval_value_complete hs
  have h := calls_contract_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hgen ha ht hpre
  simpa only [he, Safe] using h

theorem calls_contract_steps_no_trap {params : Env}
    (hgen : generateCallsContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    ¬ Program.Steps fs (.eval body params.reverse []) (.trap kind) := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_trap_complete hs
  have h := calls_contract_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hgen ha ht hpre
  simp only [he, Safe] at h

theorem calls_contract_steps_no_invalid {params : Env}
    (hgen : generateCallsContract fs calleePreconditions height types body preconditions post = some vc)
    (ha : Accepted types vc) (ht : params.map Val.type = types)
    (hpre : RequiresHold (params.map embed) preconditions) :
    ¬ Program.Steps fs (.eval body params.reverse []) .invalid := by
  intro hs
  obtain ⟨depth, fuel, he⟩ := Program.eval_invalid_complete hs
  have h := calls_contract_eval_sound (fs := fs) (depth := depth) (fuel := fuel) hgen ha ht hpre
  simp only [he, Safe] at h

end APL.VCG
