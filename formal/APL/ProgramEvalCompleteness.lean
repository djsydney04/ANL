import APL.ProgramEvalSoundness
namespace APL.Program

private theorem step_deterministic (ha : Step fs s a) (hb : Step fs s b) : a = b := by
  cases ha <;> cases hb <;> try rfl
  all_goals simp_all

private inductive CountSteps (fs : Functions) : Nat → State → State → Prop where
  | refl : CountSteps fs 0 s s
  | head : Step fs s s' → CountSteps fs n s' last → CountSteps fs (n+1) s last

private theorem count_trans (h : CountSteps fs n s mid) (h' : CountSteps fs m mid last) :
    CountSteps fs (n + m) s last := by
  induction h with
  | refl => simpa using h'
  | head hs _ ih =>
    simpa only [Nat.add_right_comm] using CountSteps.head hs (ih h')

private theorem count_of_steps (h : Steps fs s last) : ∃ n, CountSteps fs n s last := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | head hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n+1, .head hs h⟩

private theorem count_bound (h : CountSteps fs n s last) (stop : ¬ ∃ next, Step fs last next)
    (hp : CountSteps fs m s mid) : m ≤ n := by
  induction h generalizing m mid with
  | refl =>
    cases hp with
    | refl => omega
    | head hs _ => exact False.elim (stop ⟨_, hs⟩)
  | head hs _ ih =>
    cases hp with
    | refl => omega
    | head hs' hp =>
      cases step_deterministic hs hs'
      have := ih stop hp
      omega

private theorem terminal_unique (h : Steps fs s a) (stop : ¬ ∃ next, Step fs a next)
    (h' : Steps fs s b) (stop' : ¬ ∃ next, Step fs b next) : a = b := by
  induction h generalizing b with
  | refl =>
    cases h' with
    | refl => rfl
    | head hs _ => exact False.elim (stop ⟨_, hs⟩)
  | head hs _ ih =>
    cases h' with
    | refl => exact False.elim (stop' ⟨_, hs⟩)
    | head hs' tail =>
      cases step_deterministic hs hs'
      exact ih stop tail stop'

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

private def Accounts (fs : Functions) (s : State) (out : Except Error (α × Nat))
    (done : α → State) (depth fuel : Nat) : Prop :=
  match out with
  | .ok (v, remaining) => ∃ n, CountSteps fs n s (done v) ∧ fuel ≤ remaining + n ∧ remaining ≤ fuel
  | .error .resourceLimit => ∃ n last, CountSteps fs n s last ∧ min depth fuel ≤ n
  | .error (.trap _) | .error .invalid => True

private theorem accounts_prefix (hs : CountSteps fs n s s')
    (h : Accounts fs s' out done depth fuel) : Accounts fs s out done depth fuel := by
  cases out with
  | ok p =>
    obtain ⟨v, remaining⟩ := p
    obtain ⟨m, hm, hcost, hrem⟩ := h
    exact ⟨n+m, count_trans hs hm, by omega, hrem⟩
  | error err =>
    cases err with
    | trap _ | invalid => trivial
    | resourceLimit =>
      obtain ⟨m, last, hm, hcost⟩ := h
      exact ⟨n+m, last, count_trans hs hm, by omega⟩

private theorem accounts_step (hs : Step fs s s')
    (h : Accounts fs s' out done depth fuel) : Accounts fs s out done depth fuel :=
  accounts_prefix (.head hs .refl) h

private theorem accounts_advance (hs : Step fs s s')
    (h : Accounts fs s' out done depth fuel) : Accounts fs s out done (depth+1) (fuel+1) := by
  cases out with
  | ok p =>
    obtain ⟨v, remaining⟩ := p
    obtain ⟨m, hm, hcost, hrem⟩ := h
    exact ⟨m+1, .head hs hm, by omega, by omega⟩
  | error err =>
    cases err with
    | trap _ | invalid => trivial
    | resourceLimit =>
      obtain ⟨m, last, hm, hcost⟩ := h
      exact ⟨m+1, last, .head hs hm, by omega⟩

private theorem accounts_bind (x : EvalM α) (f : α → EvalM β)
    (hx : Accounts fs s (x fuel) mid depth fuel)
    (hf : ∀ a n, Accounts fs (mid a) (f a n) done depth n) :
    Accounts fs s ((x >>= f) fuel) done depth fuel := by
  rw [bind_apply]
  cases he : x fuel with
  | error err =>
    cases err with
    | trap _ | invalid => trivial
    | resourceLimit => simpa only [he, Accounts] using hx
  | ok p =>
    obtain ⟨a, n⟩ := p
    obtain ⟨m, hm, hcost, hrem⟩ : ∃ m, CountSteps fs m s (mid a) ∧ fuel ≤ n+m ∧ n ≤ fuel := by
      simpa only [he, Accounts] using hx
    have hf' := hf a n
    dsimp only
    cases hout : f a n with
    | error err =>
      cases err with
      | trap _ | invalid => trivial
      | resourceLimit =>
        obtain ⟨l, last, hl, hcost'⟩ : ∃ l last, CountSteps fs l (mid a) last ∧ min depth n ≤ l := by
          simpa only [hout, Accounts] using hf'
        exact ⟨m+l, last, count_trans hm hl, by omega⟩
    | ok p =>
      obtain ⟨b, remaining⟩ := p
      obtain ⟨l, hl, hcost', hrem'⟩ : ∃ l, CountSteps fs l (mid a) (done b) ∧ n ≤ remaining+l ∧ remaining ≤ n := by
        simpa only [hout, Accounts] using hf'
      exact ⟨m+l, count_trans hm hl, by omega, by omega⟩

private def argStart (f : Nat) (env : Env) (args : List Term) (values : List Val) (k : List Frame) : State :=
  match args with
  | [] => .invoke f values k
  | a :: args => .eval a env (.arguments f env args values :: k)

private theorem arg_step : Step fs (.ret v (.arguments f env args values :: k))
    (argStart f env args (v :: values) k) := by
  cases args with
  | nil => exact .argumentsDone
  | cons a args => exact .argumentNext

private theorem args_accounts (ih : ∀ env e fuel k,
    Accounts fs (.eval e env k) (eval fs depth env e fuel) (fun v => .ret v k) depth fuel)
    (args : List Term) (values : List Val) (fuel : Nat) :
    Accounts fs (argStart f env args values k) ((args.mapM (eval fs depth env)) fuel)
      (fun vs => .invoke f (vs.reverse ++ values) k) depth fuel := by
  induction args generalizing values fuel with
  | nil => exact ⟨0, .refl, by omega, by omega⟩
  | cons a args ihArgs =>
    rw [List.mapM_cons]
    apply accounts_bind _ _ (ih env a fuel (.arguments f env args values :: k))
    intro v n
    apply accounts_step arg_step
    apply accounts_bind _ _ (ihArgs (v :: values) n)
    intro vs n'
    change ∃ m, CountSteps fs m (.invoke f (vs.reverse ++ v :: values) k)
      (.invoke f ((v :: vs).reverse ++ values) k) ∧ n' ≤ n'+m ∧ n' ≤ n'
    refine ⟨0, ?_, by omega, by omega⟩
    simpa [List.reverse_cons, List.append_assoc] using
      (CountSteps.refl : CountSteps fs 0 (.invoke f (vs.reverse ++ v :: values) k) _)

private theorem lift_accounts : Accounts fs (resume r k) (liftResult r fuel)
    (fun v => .ret v k) depth fuel := by
  cases r with
  | value v => exact ⟨0, .refl, by omega, by omega⟩
  | trap _ | invalid => trivial

private theorem eval_accounts : Accounts fs (.eval e env k) (eval fs depth env e fuel)
    (fun v => .ret v k) depth fuel := by
  induction depth generalizing e env k fuel with
  | zero => exact ⟨0, _, .refl, by omega⟩
  | succ depth ih =>
    cases fuel with
    | zero =>
      rw [eval.eq_def]
      exact ⟨0, _, .refl, by omega⟩
    | succ fuel =>
      rw [eval.eq_def]
      dsimp only
      rw [fuel_then]
      cases e with
      | lit v => exact ⟨1, .head .lit .refl, by omega, by omega⟩
      | «local» i =>
        dsimp only
        cases hv : env[i]? with
        | none => trivial
        | some v => exact ⟨1, .head (.localFound hv) .refl, by omega, by omega⟩
      | letE a b =>
        apply accounts_advance .letEval
        apply accounts_bind _ _ (ih (e := a))
        intro v n
        exact accounts_step .letReturn (ih (e := b))
      | ifE c a b =>
        apply accounts_advance .ifEval
        apply accounts_bind _ _ (ih (e := c))
        intro v n
        cases v with
        | int _ | unit => trivial
        | bool test =>
          cases test
          · exact accounts_step .ifFalse (ih (e := b))
          · exact accounts_step .ifTrue (ih (e := a))
      | unary op a =>
        apply accounts_advance .unaryEval
        apply accounts_bind _ _ (ih (e := a))
        intro v n
        exact accounts_step .unaryReturn lift_accounts
      | binary op a b =>
        apply accounts_advance .binaryEval
        apply accounts_bind _ _ (ih (e := a))
        intro va n
        cases hs : shortCircuit op va with
        | true => exact ⟨1, .head (.short hs) .refl, by omega, by omega⟩
        | false =>
          apply accounts_step (.rightEval hs)
          apply accounts_bind _ _ (ih (e := b))
          intro vb n'
          exact accounts_step .binaryReturn lift_accounts
      | call f args =>
        have start : Step fs (.eval (.call f args) env k) (argStart f env args [] k) := by
          cases args with
          | nil => exact .callEmpty
          | cons a args => exact .callFirst
        apply accounts_advance start
        apply accounts_bind _ _ (args_accounts (fun env e fuel k => ih) args [] fuel)
        intro vs n
        simp only [List.append_nil]
        cases hf : fs[f]? with
        | none => trivial
        | some fn => exact accounts_step (.invoke hf) ih

private theorem finite_budget (h : Steps fs (.eval e env []) last)
    (stop : ¬ ∃ next, Step fs last next) :
    ∃ depth fuel, eval fs depth env e fuel ≠ .error .resourceLimit := by
  obtain ⟨n, hn⟩ := count_of_steps h
  refine ⟨n+1, n+1, ?_⟩
  intro he
  have accounts := eval_accounts (fs := fs) (depth := n+1) (fuel := n+1)
    (e := e) (env := env) (k := [])
  obtain ⟨m, mid, hm, bound⟩ : ∃ m mid, CountSteps fs m (.eval e env []) mid ∧ min (n+1) (n+1) ≤ m := by
    simpa only [he, Accounts] using accounts
  have := count_bound hn stop hm
  omega

theorem eval_value_complete (h : Steps fs (.eval e env []) (.ret v [])) :
    ∃ depth fuel remaining, eval fs depth env e fuel = .ok (v, remaining) := by
  have stop : ¬ ∃ next, Step fs (.ret v []) next := by
    rintro ⟨_, hs⟩
    cases hs
  obtain ⟨depth, fuel, hf⟩ := finite_budget h stop
  cases he : eval fs depth env e fuel with
  | ok p =>
    obtain ⟨v', remaining⟩ := p
    have stop' : ¬ ∃ next, Step fs (.ret v' []) next := by
      rintro ⟨_, hs⟩
      cases hs
    have eq := terminal_unique h stop (eval_value_sound he) stop'
    cases eq
    exact ⟨depth, fuel, remaining, he⟩
  | error err =>
    cases err with
    | resourceLimit => exact False.elim (hf he)
    | trap kind =>
      have stop' : ¬ ∃ next, Step fs (.trap kind) next := by
        rintro ⟨_, hs⟩
        cases hs
      have eq := terminal_unique h stop (eval_trap_sound he) stop'
      cases eq
    | invalid =>
      have stop' : ¬ ∃ next, Step fs .invalid next := by
        rintro ⟨_, hs⟩
        cases hs
      have eq := terminal_unique h stop (eval_invalid_sound he) stop'
      cases eq

theorem eval_trap_complete (h : Steps fs (.eval e env []) (.trap kind)) :
    ∃ depth fuel, eval fs depth env e fuel = .error (.trap kind) := by
  have stop : ¬ ∃ next, Step fs (.trap kind) next := by
    rintro ⟨_, hs⟩
    cases hs
  obtain ⟨depth, fuel, hf⟩ := finite_budget h stop
  cases he : eval fs depth env e fuel with
  | ok p =>
    obtain ⟨v, remaining⟩ := p
    have stop' : ¬ ∃ next, Step fs (.ret v []) next := by
      rintro ⟨_, hs⟩
      cases hs
    have eq := terminal_unique h stop (eval_value_sound he) stop'
    cases eq
  | error err =>
    cases err with
    | resourceLimit => exact False.elim (hf he)
    | trap kind' =>
      have stop' : ¬ ∃ next, Step fs (.trap kind') next := by
        rintro ⟨_, hs⟩
        cases hs
      have eq := terminal_unique h stop (eval_trap_sound he) stop'
      cases eq
      exact ⟨depth, fuel, he⟩
    | invalid =>
      have stop' : ¬ ∃ next, Step fs .invalid next := by
        rintro ⟨_, hs⟩
        cases hs
      have eq := terminal_unique h stop (eval_invalid_sound he) stop'
      cases eq

theorem eval_invalid_complete (h : Steps fs (.eval e env []) .invalid) :
    ∃ depth fuel, eval fs depth env e fuel = .error .invalid := by
  have stop : ¬ ∃ next, Step fs .invalid next := by
    rintro ⟨_, hs⟩
    cases hs
  obtain ⟨depth, fuel, hf⟩ := finite_budget h stop
  cases he : eval fs depth env e fuel with
  | ok p =>
    obtain ⟨v, remaining⟩ := p
    have stop' : ¬ ∃ next, Step fs (.ret v []) next := by
      rintro ⟨_, hs⟩
      cases hs
    have eq := terminal_unique h stop (eval_value_sound he) stop'
    cases eq
  | error err =>
    cases err with
    | resourceLimit => exact False.elim (hf he)
    | trap kind =>
      have stop' : ¬ ∃ next, Step fs (.trap kind) next := by
        rintro ⟨_, hs⟩
        cases hs
      have eq := terminal_unique h stop (eval_trap_sound he) stop'
      cases eq
    | invalid => exact ⟨depth, fuel, he⟩

end APL.Program
