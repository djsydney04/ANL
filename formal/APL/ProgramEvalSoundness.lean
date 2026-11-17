import APL.ProgramSafety
namespace APL.Program

private theorem bind_apply (x : EvalM α) (f : α → EvalM β) (n : Nat) :
    (x >>= f) n = match x n with
    | .ok (v, n') => f v n'
    | .error err => .error err := by
  change (Except.bind (x n) _) = _
  cases x n with
  | error err => rfl
  | ok p => cases p; rfl

private theorem fuel_succ : takeFuel (f+1) = .ok ((), f) := by rfl

private theorem fuel_then (x : EvalM α) : (takeFuel >>= fun _ => x) (f+1) = x f := by
  rw [bind_apply, fuel_succ]

private theorem steps_trans (h : Steps fs s mid) (h' : Steps fs mid last) : Steps fs s last := by
  induction h with
  | refl => exact h'
  | head hs _ ih => exact .head hs (ih h')

private def Follows (fs : Functions) (s : State) (out : Except Error (α × Nat))
    (done : α → State) : Prop :=
  match out with
  | .ok (v, _) => Steps fs s (done v)
  | .error (.trap kind) => Steps fs s (.trap kind)
  | .error .invalid => Steps fs s .invalid
  | .error .resourceLimit => True

private theorem follows_prefix (hs : Steps fs s s') (h : Follows fs s' out done) :
    Follows fs s out done := by
  cases out with
  | ok p => exact steps_trans hs h
  | error err => cases err with
    | trap kind => exact steps_trans hs h
    | invalid => exact steps_trans hs h
    | resourceLimit => trivial

private theorem follows_step (hs : Step fs s s') (h : Follows fs s' out done) :
    Follows fs s out done := follows_prefix (.head hs .refl) h

private theorem follows_bind (x : EvalM α) (f : α → EvalM β)
    (hx : Follows fs s (x fuel) mid)
    (hf : ∀ a n, Follows fs (mid a) (f a n) done) :
    Follows fs s ((x >>= f) fuel) done := by
  rw [bind_apply]
  cases he : x fuel with
  | error err =>
    cases err with
    | trap kind => simpa only [he, Follows] using hx
    | invalid => simpa only [he, Follows] using hx
    | resourceLimit => trivial
  | ok p =>
    obtain ⟨a, n⟩ := p
    exact follows_prefix (by simpa only [he, Follows] using hx) (hf a n)

private def argStart (f : Nat) (env : Env) (args : List Term) (values : List Val) (k : List Frame) : State :=
  match args with
  | [] => .invoke f values k
  | a :: args => .eval a env (.arguments f env args values :: k)

private theorem arg_step : Step fs (.ret v (.arguments f env args values :: k))
    (argStart f env args (v :: values) k) := by
  cases args with
  | nil => exact .argumentsDone
  | cons a args => exact .argumentNext

private theorem args_follow (ih : ∀ env e fuel k,
    Follows fs (.eval e env k) (eval fs depth env e fuel) (fun v => .ret v k))
    (args : List Term) (values : List Val) (fuel : Nat) :
    Follows fs (argStart f env args values k) ((args.mapM (eval fs depth env)) fuel)
      (fun vs => .invoke f (vs.reverse ++ values) k) := by
  induction args generalizing values fuel with
  | nil => exact .refl
  | cons a args ihArgs =>
    rw [List.mapM_cons]
    apply follows_bind _ _ (ih env a fuel (.arguments f env args values :: k))
    intro v n
    apply follows_step arg_step
    apply follows_bind _ _ (ihArgs (v :: values) n)
    intro vs n'
    change Steps fs (.invoke f (vs.reverse ++ v :: values) k)
      (.invoke f ((v :: vs).reverse ++ values) k)
    simpa [List.reverse_cons, List.append_assoc] using
      (Steps.refl : Steps fs (.invoke f (vs.reverse ++ v :: values) k) _)

private theorem lift_follow : Follows fs (resume r k) (liftResult r fuel) (fun v => .ret v k) := by
  cases r <;> exact .refl

private theorem eval_follow : Follows fs (.eval e env k) (eval fs depth env e fuel)
    (fun v => .ret v k) := by
  induction depth generalizing e env k fuel with
  | zero => trivial
  | succ depth ih =>
    cases fuel with
    | zero =>
      rw [eval.eq_def]
      trivial
    | succ fuel =>
      rw [eval.eq_def]
      dsimp only
      rw [fuel_then]
      cases e with
      | lit v => exact .head .lit .refl
      | «local» i =>
        dsimp only
        cases hv : env[i]? with
        | none => exact .head (.localMissing hv) .refl
        | some v => exact .head (.localFound hv) .refl
      | letE a b =>
        apply follows_step .letEval
        apply follows_bind _ _ (ih (e := a))
        intro v n
        exact follows_step .letReturn (ih (e := b))
      | ifE c a b =>
        apply follows_step .ifEval
        apply follows_bind _ _ (ih (e := c))
        intro v n
        cases v with
        | int v => exact .head .ifInt .refl
        | unit => exact .head .ifUnit .refl
        | bool test =>
          cases test
          · exact follows_step .ifFalse (ih (e := b))
          · exact follows_step .ifTrue (ih (e := a))
      | unary op a =>
        apply follows_step .unaryEval
        apply follows_bind _ _ (ih (e := a))
        intro v n
        exact follows_step .unaryReturn lift_follow
      | binary op a b =>
        apply follows_step .binaryEval
        apply follows_bind _ _ (ih (e := a))
        intro va n
        cases hs : shortCircuit op va with
        | true => exact .head (.short hs) .refl
        | false =>
          apply follows_step (.rightEval hs)
          apply follows_bind _ _ (ih (e := b))
          intro vb n'
          exact follows_step .binaryReturn lift_follow
      | call f args =>
        have start : Step fs (.eval (.call f args) env k) (argStart f env args [] k) := by
          cases args with
          | nil => exact .callEmpty
          | cons a args => exact .callFirst
        apply follows_step start
        apply follows_bind _ _ (args_follow (fun env e fuel k => ih) args [] fuel)
        intro vs n
        simp only [List.append_nil]
        cases hf : fs[f]? with
        | none => exact .head (.invalidFunction hf) .refl
        | some fn => exact follows_step (.invoke hf) ih

theorem eval_value_sound (h : eval fs depth env e fuel = .ok (v, remaining)) :
    Steps fs (.eval e env k) (.ret v k) := by
  have trace := eval_follow (fs := fs) (depth := depth) (e := e) (env := env) (k := k) (fuel := fuel)
  simpa only [h, Follows] using trace

theorem eval_trap_sound (h : eval fs depth env e fuel = .error (.trap kind)) :
    Steps fs (.eval e env k) (.trap kind) := by
  have trace := eval_follow (fs := fs) (depth := depth) (e := e) (env := env) (k := k) (fuel := fuel)
  simpa only [h, Follows] using trace

theorem eval_invalid_sound (h : eval fs depth env e fuel = .error .invalid) :
    Steps fs (.eval e env k) .invalid := by
  have trace := eval_follow (fs := fs) (depth := depth) (e := e) (env := env) (k := k) (fuel := fuel)
  simpa only [h, Follows] using trace

theorem eval_value_typed (wf : WellTyped fs) (ht : HasType (signatures fs) (env.map Val.type) e t)
    (h : eval fs depth env e fuel = .ok (v, remaining)) : v.type = t := by
  have initial : State.Typed (signatures fs) (.eval e env []) t := .eval ht .nil
  have final := steps_preserve wf initial (eval_value_sound h)
  cases final with
  | ret hk => cases hk; rfl

theorem eval_ne_invalid (wf : WellTyped fs) (ht : HasType (signatures fs) (env.map Val.type) e t) :
    eval fs depth env e fuel ≠ .error .invalid := by
  intro h
  have initial : State.Typed (signatures fs) (.eval e env []) t := .eval ht .nil
  exact no_invalid wf initial (eval_invalid_sound h)

end APL.Program
