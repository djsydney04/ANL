import ANL.BootOriginProgress

namespace ANL.Boot.Origin
open ANL.Words
set_option linter.unusedSimpArgs false

/-- Entry at an authored body, never at the carrier's synthetic entry or primitive dummy. -/
def rootState (function : Nat) (body : Term) (values : Env) : State :=
  ⟨.eval body, ⟨function, values, []⟩, [], .initial⟩

def rootMetadata (function : Nat) : Metadata := ⟨.root function, []⟩

inductive Root (p : ANL.Boot.Program) (function : Nat) (values : Env) : State → Metadata → Prop where
  | defined : p.functions[function]? = some (.defined d) →
      Root p function values (rootState function d.function.body values) (rootMetadata function)

 theorem root_aligned (root : Root p f values s m) : Aligned p s m := by
  cases root with
  | defined found => exact ⟨rfl, .eval (.root found), .nil⟩

 theorem root_typed {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext) :
    State.Typed p.carrier (rootState f d.function.body values) d.function.result := by
  apply typed_eval (Γ := d.function.valueContext)
  · simpa [resourceModes] using carrier_typing (wf.at found).typed
  · exact env
  · exact .nil
  · exact .nil
  · exact ANL.Memory.World.initial_valid (carrier_wellFormed wf).profile

/-- Every finite edge contains the actual admitted Words step and structural metadata movement. -/
inductive Steps (p : ANL.Boot.Program) (responses : ANL.Memory.Responses) :
    Nat → State → Metadata → State → Metadata → Prop where
  | zero : Steps p responses 0 s m s m
  | succ : Step p responses s m middle mid → Steps p responses n middle mid last finish →
      Steps p responses (n + 1) s m last finish

 theorem Steps.erase (h : Steps p responses n s m last finish) :
    ANL.Words.StepsN p.carrier responses n s last := by
  induction h with
  | zero => exact .zero
  | succ step _ ih => exact .succ step.erase ih

 theorem Steps.erase_finite (h : Steps p responses n s m last finish) :
    ANL.Words.Steps p.carrier responses s last := by
  induction h with
  | zero => exact .refl
  | succ step _ ih => exact .head step.erase ih

 theorem Steps.preserve (wf : WellFormedProgram p) (typed : State.Typed p.carrier s t)
    (aligned : Aligned p s m) (h : Steps p responses n s m last finish) :
    State.Typed p.carrier last t ∧ Aligned p last finish := by
  induction h with
  | zero => exact ⟨typed, aligned⟩
  | succ step _ ih =>
    exact ih (ANL.Words.preservation (carrier_wellFormed wf) typed step.erase)
      (Origin.preserve wf typed aligned step)

 theorem Steps.deterministic (h : Steps p responses n s m last finish)
    (h' : Steps p responses n s m last' finish') : last = last' ∧ finish = finish' := by
  induction h generalizing last' finish' with
  | zero => cases h'; exact ⟨rfl, rfl⟩
  | succ first tail ih =>
    cases h' with
    | succ first' tail' =>
      obtain ⟨rfl, rfl⟩ := first.deterministic first'
      exact ih tail'

 theorem root_prefix {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext)
    (h : Steps p responses n (rootState f d.function.body values) (rootMetadata f) last finish) :
    State.Typed p.carrier last d.function.result ∧ Aligned p last finish :=
  h.preserve wf (root_typed wf found env) (root_aligned (.defined found))

 theorem root_prefix_defined {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext)
    (h : Steps p responses n (rootState f d.function.body values) (rootMetadata f) last finish) :
    ∃ body, p.functions[last.current.function]? = some (.defined body) :=
  (root_prefix wf found env h).2.current_defined

 theorem Located.unique (h : Located p o a) (h' : Located p o b) : a = b := by
  exact Option.some.inj ((lookup_iff.mpr h).symm.trans (lookup_iff.mpr h'))

 theorem aligned_eval_lookup (h : Aligned p s m) (control : s.control = .eval e) :
    lookup p m.control = some e := by
  have hc := h.control
  rw [control] at hc
  cases hc with | eval occurrence => exact lookup_iff.mpr occurrence

 theorem selected_eval {p : ANL.Boot.Program} (found : p.functions[f]? = some (.defined d))
    (selected : designatedTail d.function.body = some path) (aligned : Aligned p s m)
    (origin : m.control = ⟨f, tailPath path⟩) (control : s.control = .eval e) : e = park := by
  have here := aligned_eval_lookup aligned control
  rw [origin] at here
  exact (lookup_iff.mp here).unique (designatedTail_located found selected)

 theorem root_prefix_selected {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext)
    (h : Steps p responses n (rootState f d.function.body values) (rootMetadata f) last finish)
    (selected : designatedTail d.function.body = some path)
    (origin : finish.control = ⟨f, tailPath path⟩) (control : last.control = .eval e) : e = park :=
  selected_eval found selected (root_prefix wf found env h).2 origin control

 theorem root_prefix_stop {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext)
    (h : Steps p responses n (rootState f d.function.body values) (rootMetadata f) last finish) :
    step p responses last finish = none ↔ PrimitiveFrontier p last ∨ Terminal last := by
  have safe := root_prefix wf found env h
  exact stopped_iff wf safe.1 safe.2

 theorem root_prefix_no_primitive {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext)
    (h : Steps p responses n (rootState f d.function.body values) (rootMetadata f) last finish) :
    p.functions[last.current.function]? ≠ some (.primitive op) := by
  obtain ⟨body, actual⟩ := root_prefix_defined wf found env h
  simp [actual]

 theorem root_prefix_no_synthetic {p : ANL.Boot.Program} (wf : WellFormedProgram p)
    (found : p.functions[f]? = some (.defined d)) (env : EnvTyped values d.function.valueContext)
    (h : Steps p responses n (rootState f d.function.body values) (rootMetadata f) last finish) :
    last.current.function < p.functions.length := by
  obtain ⟨body, actual⟩ := root_prefix_defined wf found env h
  exact List.getElem?_eq_some_iff.mp actual |>.1

 theorem primitive_capture (aligned : Aligned p s m) (frontier : PrimitiveFrontier p s) :
    ∃ f values op ty args, s.control = .invoke f none values ∧
      p.functions[f]? = some (.primitive op) ∧ Located p m.control (.call ty f args) ∧
      values.length = args.length := by
  obtain ⟨f, values, op, ctl, found⟩ := frontier
  have hc := aligned.control
  rw [ctl] at hc
  cases hc with
  | invoke occurrence arity => exact ⟨f, values, op, _, _, ctl, found, occurrence, arity⟩

 theorem while_entry : Step p responses
    ⟨.eval (.whileE ty condition body), a, k, w⟩ ⟨o, origins⟩
    ⟨.eval condition, a, .condition condition body :: k, w⟩
    ⟨o.child .whileCondition, o :: origins⟩ :=
  .ordinary trivial .whileEval .whileEval .push

/-- Spinning revisits child occurrences of the same loop; it does not fabricate a new loop entry. -/
 theorem park_round : Steps p responses 4
    ⟨.eval (.lit (.scalar (.legacy .bool)) (.bool true)), a,
      .condition (.lit (.scalar (.legacy .bool)) (.bool true)) (.lit unitTy .unit) :: k, w⟩
    ⟨o.child .whileCondition, o :: origins⟩
    ⟨.eval (.lit (.scalar (.legacy .bool)) (.bool true)), a,
      .condition (.lit (.scalar (.legacy .bool)) (.bool true)) (.lit unitTy .unit) :: k, w⟩
    ⟨o.child .whileCondition, o :: origins⟩ := by
  exact .succ (.ordinary trivial .lit .lit .keep)
    (.succ (.ordinary trivial .whileTrue .whileTrue .within)
      (.succ (.ordinary trivial .lit .lit .keep)
        (.succ (.ordinary trivial .whileAgain .whileAgain .within) .zero)))

end ANL.Boot.Origin
