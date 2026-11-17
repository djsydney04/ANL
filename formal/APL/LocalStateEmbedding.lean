import APL.LocalStateSafety

namespace APL.LocalState

def embed : Program.Term → Term
  | .lit v => .lit v
  | .local i => .local i
  | .letE a b => .letE (embed a) (embed b)
  | .ifE c a b => .ifE (embed c) (embed a) (embed b)
  | .unary op a => .unary op (embed a)
  | .binary op a b => .binary op (embed a) (embed b)
  | .call f args => .call f (args.map embed)

def embedFunction (fn : Program.Function) : Function :=
  { name := fn.name, params := fn.params, result := fn.result, body := embed fn.body }

def embedFunctions (fs : Program.Functions) : Functions := fs.map embedFunction

theorem embed_typed (h : Program.HasType sigs Γ e t) :
    HasType sigs (immutable Γ) (embed e) t := by
  induction h using Program.HasType.rec
    (motive_2 := fun Γ es ts _ => ArgsTyped sigs (immutable Γ) (es.map embed) ts) with
  | lit => simpa only [embed] using (HasType.lit (sigs := sigs) (Γ := immutable _))
  | «local» hi =>
    simp only [embed]
    exact .local (permission := false) (by simp [immutable, List.getElem?_map, hi])
  | letE _ _ ha hb => simpa only [embed, immutable, List.map_cons] using HasType.letE ha hb
  | ifE _ _ _ hc ha hb => simpa only [embed] using HasType.ifE hc ha hb
  | unary _ ha => simpa only [embed] using HasType.unary ha
  | binary _ _ hop ha hb => simpa only [embed] using HasType.binary ha hb hop
  | call hf _ ha => simpa only [embed] using HasType.call hf ha
  | nil => exact .nil
  | cons _ _ ha hb => exact .cons ha hb

theorem embed_signatures : signatures (embedFunctions fs) = Program.signatures fs := by
  simp [signatures, Program.signatures, embedFunctions, embedFunction, Array.map_map]

theorem embed_wellTyped (h : Program.WellTyped fs) : WellTyped (embedFunctions fs) := by
  intro f fn hf
  simp only [embedFunctions, Array.getElem?_map, Option.map_eq_some_iff] at hf
  obtain ⟨old, ho, rfl⟩ := hf
  simpa only [embed_signatures, embedFunction] using embed_typed (h f old ho)

private theorem embed_lookup {f : Nat} (h : fs[f]? = some fn) : (embedFunctions fs)[f]? = some (embedFunction fn) := by
  simp [embedFunctions, Array.getElem?_map, h]

private theorem embed_missing {f : Nat} (h : fs[f]? = none) : (embedFunctions fs)[f]? = none := by
  simp [embedFunctions, Array.getElem?_map, h]


private theorem bind_apply (x : Program.EvalM α) (f : α → Program.EvalM β) (n : Nat) :
    (x >>= f) n = match x n with
    | .ok (v, n') => f v n'
    | .error err => .error err := by
  change (Except.bind (x n) _) = _
  cases x n with
  | error err => rfl
  | ok p => cases p; rfl

private theorem fuel_succ : Program.takeFuel (f+1) = .ok ((), f) := by rfl

private theorem fuel_then (x : Program.EvalM α) : (Program.takeFuel >>= fun _ => x) (f+1) = x f := by
  rw [bind_apply, fuel_succ]

private theorem steps_trans (h : Steps fs s mid) (h' : Steps fs mid last) : Steps fs s last := by
  induction h with
  | refl => exact h'
  | head hs _ ih => exact .head hs (ih h')

private def Follows (fs : Functions) (s : State) (out : Except Program.Error (α × Nat))
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

private theorem follows_post (h : Follows fs s out mid)
    (tail : ∀ v, Steps fs (mid v) (done v)) : Follows fs s out done := by
  cases out with
  | ok p => exact steps_trans h (tail p.1)
  | error err => cases err <;> exact h

private theorem follows_step (hs : Step fs s s') (h : Follows fs s' out done) :
    Follows fs s out done := follows_prefix (.head hs .refl) h

private theorem follows_bind (x : Program.EvalM α) (f : α → Program.EvalM β)
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

private def argStart (f : Nat) (env : Env) (args : List Program.Term) (values : List Val) (k : List Frame) : State :=
  match args with
  | [] => .invoke f values env k
  | a :: args => .eval (embed a) env (.arguments f (args.map embed) values :: k)

private theorem arg_step : Step fs (.ret v env (.arguments f (args.map embed) values :: k))
    (argStart f env args (v :: values) k) := by
  cases args with
  | nil => exact .argumentsDone
  | cons a args => exact .argumentNext

private theorem args_follow (ih : ∀ env e fuel k,
    Follows (embedFunctions fs) (.eval (embed e) env k) (Program.eval fs depth env e fuel) (fun v => .ret v env k))
    (args : List Program.Term) (values : List Val) (fuel : Nat) :
    Follows (embedFunctions fs) (argStart f env args values k) ((args.mapM (Program.eval fs depth env)) fuel)
      (fun vs => .invoke f (vs.reverse ++ values) env k) := by
  induction args generalizing values fuel with
  | nil => exact .refl
  | cons a args ihArgs =>
    rw [List.mapM_cons]
    apply follows_bind _ _ (ih env a fuel (.arguments f (args.map embed) values :: k))
    intro v n
    apply follows_step arg_step
    apply follows_bind _ _ (ihArgs (v :: values) n)
    intro vs n'
    change Steps (embedFunctions fs) (.invoke f (vs.reverse ++ v :: values) env k)
      (.invoke f ((v :: vs).reverse ++ values) env k)
    simpa [List.reverse_cons, List.append_assoc] using
      (Steps.refl : Steps (embedFunctions fs) (.invoke f (vs.reverse ++ v :: values) env k) _)

private theorem lift_follow : Follows fs (resume r env k) (Program.liftResult r fuel) (fun v => .ret v env k) := by
  cases r <;> exact .refl

private theorem eval_follow : Follows (embedFunctions fs) (.eval (embed e) env k) (Program.eval fs depth env e fuel)
    (fun v => .ret v env k) := by
  induction depth generalizing e env k fuel with
  | zero => trivial
  | succ depth ih =>
    cases fuel with
    | zero =>
      rw [Program.eval.eq_def]
      trivial
    | succ fuel =>
      rw [Program.eval.eq_def]
      dsimp only
      rw [fuel_then]
      cases e <;> simp only [embed]
      case lit v => exact .head .lit .refl
      case «local» i =>
        cases hv : env[i]? with
        | none => exact .head (.localMissing hv) .refl
        | some v => exact .head (.localFound hv) .refl
      case letE a b =>
        apply follows_step .letEval
        apply follows_bind _ _ (ih (e := a))
        intro v n
        apply follows_step .bindReturn
        apply follows_post (ih (e := b) (k := .scope :: k))
        intro w
        exact .head .scopeReturn .refl
      case ifE c a b =>
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
      case unary op a =>
        apply follows_step .unaryEval
        apply follows_bind _ _ (ih (e := a))
        intro v n
        exact follows_step .unaryReturn lift_follow
      case binary op a b =>
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
      case call f args =>
        have start : Step (embedFunctions fs) (.eval (.call f (args.map embed)) env k) (argStart f env args [] k) := by
          cases args with
          | nil => exact .callEmpty
          | cons a args => exact .callFirst
        apply follows_step start
        apply follows_bind _ _ (args_follow (fun env e fuel k => ih) args [] fuel)
        intro vs n
        simp only [List.append_nil]
        cases hf : fs[f]? with
        | none => exact .head (.invalidFunction (embed_missing hf)) .refl
        | some fn =>
          apply follows_step (.invoke (embed_lookup hf))
          apply follows_post (ih (e := fn.body) (env := vs.reverse) (k := .callReturn env :: k))
          intro w
          exact .head .callReturn .refl

theorem embed_value_steps (h : Program.eval fs depth env e fuel = .ok (v, remaining)) :
    Steps (embedFunctions fs) (.eval (embed e) env k) (.ret v env k) := by
  have trace := eval_follow (fs := fs) (depth := depth) (e := e) (env := env) (k := k) (fuel := fuel)
  simpa only [h, Follows] using trace

theorem embed_trap_steps (h : Program.eval fs depth env e fuel = .error (.trap kind)) :
    Steps (embedFunctions fs) (.eval (embed e) env k) (.trap kind) := by
  have trace := eval_follow (fs := fs) (depth := depth) (e := e) (env := env) (k := k) (fuel := fuel)
  simpa only [h, Follows] using trace

theorem embed_invalid_steps (h : Program.eval fs depth env e fuel = .error .invalid) :
    Steps (embedFunctions fs) (.eval (embed e) env k) .invalid := by
  have trace := eval_follow (fs := fs) (depth := depth) (e := e) (env := env) (k := k) (fuel := fuel)
  simpa only [h, Follows] using trace

theorem embed_value_run (h : Program.eval fs depth env e fuel = .ok (v, remaining)) :
    ∃ budget, run (embedFunctions fs) budget (.eval (embed e) env []) = some (.ret v env []) :=
  run_complete (embed_value_steps h) rfl

theorem embed_trap_run (h : Program.eval fs depth env e fuel = .error (.trap kind)) :
    ∃ budget, run (embedFunctions fs) budget (.eval (embed e) env []) = some (.trap kind) :=
  run_complete (embed_trap_steps h) rfl

end APL.LocalState
