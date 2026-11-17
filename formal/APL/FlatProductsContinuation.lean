import APL.FlatProductsFrame

/-! Continuation specifications over the actual flat-product transition-budget
runner. The invariant rule permits divergence and proves safety at every finite
budget. A concrete generator soundness proof must establish the rule premises. -/

namespace APL.FlatProducts.LoopVerification

variable {invariant : Env → Prop} {guard : Bool → Env → Prop}

/-- Exhausted budgets are inconclusive. Every completed run satisfies the post. -/
def RunSafe (post : Val → Env → Prop) : Option State → Prop
  | none => True
  | some (.ret value env []) => post value env
  | _ => False

def Safe (fs : Functions) (budget : Nat) (s : State) (post : Val → Env → Prop) : Prop :=
  RunSafe post (run fs budget s)

-- Internal induction interface for a subexpression, not an accepted VC or an
-- assumption of whole-program safety. A concrete generator must establish it.
def EvalSpec (fs : Functions) (e : Term) (entry : Env) (result : Val → Env → Prop) : Prop :=
  ∀ budget suffix post,
    (∀ remaining, remaining ≤ budget → ∀ value final, result value final →
      Safe fs remaining (.ret value final suffix) post) →
    Safe fs budget (.eval e entry suffix) post

theorem spec_mono (h : EvalSpec fs e env result)
    (weaken : ∀ value final, result value final → result' value final) :
    EvalSpec fs e env result' := by
  intro budget suffix post continuation
  apply h budget suffix post
  intro remaining hr value final hout
  exact continuation remaining hr value final (weaken value final hout)

theorem literal_rule : EvalSpec fs (.lit value) env
    (fun actual final => actual = value ∧ final = env) := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    exact continuation budget (Nat.le_succ _) value env ⟨rfl, rfl⟩

theorem local_rule (lookup : env[index]? = some value) :
    EvalSpec fs (.local index) env (fun actual final => actual = value ∧ final = env) := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    simpa only [Safe, run, step, lookup] using
      continuation budget (Nat.le_succ _) value env ⟨rfl, rfl⟩

theorem assignment_rule
    (h : EvalSpec fs rhs env (fun value current =>
      ∃ final, update current index value = some final ∧ result (.scalar .unit) final)) :
    EvalSpec fs (.assign index rhs) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    change Safe fs budget (.eval rhs env (.assign index :: suffix)) post
    apply h
    intro remaining hr value current hout
    obtain ⟨final, updated, hresult⟩ := hout
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      simpa only [Safe, run, step, updated] using
        continuation remaining (by omega) (.scalar .unit) final hresult

theorem binding_rule {permission : Bool}
    (ha : EvalSpec fs a env middle)
    (hb : ∀ value current, middle value current →
      EvalSpec fs b (value :: current) (fun value final =>
        ∃ cell rest, final = cell :: rest ∧ result value rest)) :
    EvalSpec fs (if permission then .letMut a b else .letE a b) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => cases permission <;> simp [Safe, run, step, RunSafe]
  | succ budget =>
    have first : Safe fs budget (.eval a env (.bind permission b :: suffix)) post := by
      apply ha
      intro remaining hr value current hout
      cases remaining with
      | zero => simp [Safe, run, step, RunSafe]
      | succ remaining =>
        change Safe fs remaining (.eval b (value :: current) (.scope :: suffix)) post
        apply hb value current hout
        intro left hl value final hfinal
        obtain ⟨cell, rest, rfl, hresult⟩ := hfinal
        cases left with
        | zero => simp [Safe, run, step, RunSafe]
        | succ left => exact continuation left (by omega) value rest hresult
    cases permission <;> exact first

theorem conditional_rule {branch : Bool → Env → Prop}
    (hc : EvalSpec fs condition env (fun value final =>
      ∃ test, value = (.scalar (.bool test)) ∧ branch test final))
    (hb : ∀ test current, branch test current →
      EvalSpec fs (if test then yes else no) current result) :
    EvalSpec fs (.ifE condition yes no) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    change Safe fs budget (.eval condition env (.ifF yes no :: suffix)) post
    apply hc
    intro remaining hr value current hout
    obtain ⟨test, rfl, hbranch⟩ := hout
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      have next := hb test current hbranch remaining suffix post
        (fun left hl value final hresult => continuation left (by omega) value final hresult)
      cases test <;> exact next

theorem unary_rule
    (ha : EvalSpec fs arg env (fun value final =>
      ∃ actual, unary op value = .value actual ∧ result actual final)) :
    EvalSpec fs (.unary op arg) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    change Safe fs budget (.eval arg env (.unary op :: suffix)) post
    apply ha
    intro remaining hr value final hout
    obtain ⟨actual, hactual, hresult⟩ := hout
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      simpa only [Safe, run, step, hactual, resume] using
        continuation remaining (by omega) actual final hresult

theorem binary_rule
    (hl : EvalSpec fs left env middle)
    (skip : ∀ value current, middle value current → shortCircuit op value = true → result value current)
    (hr : ∀ value current, middle value current → shortCircuit op value = false →
      EvalSpec fs right current (fun other final =>
        ∃ actual, binary op value other = .value actual ∧ result actual final)) :
    EvalSpec fs (.binary op left right) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    change Safe fs budget (.eval left env (.left op right :: suffix)) post
    apply hl
    intro remaining hrem value current hmiddle
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      cases hshort : shortCircuit op value with
      | true =>
        simpa only [Safe, run, step, hshort, ↓reduceIte] using
          continuation remaining (by omega) value current (skip value current hmiddle hshort)
      | false =>
        have next : Safe fs remaining (.eval right current (.right op value :: suffix)) post := by
          apply hr value current hmiddle hshort
          intro left hleft other final hout
          obtain ⟨actual, hactual, hresult⟩ := hout
          cases left with
          | zero => simp [Safe, run, step, RunSafe]
          | succ left =>
            simpa only [Safe, run, step, hactual, resume] using
              continuation left (by omega) actual final hresult
        simpa only [Safe, run, step, hshort, Bool.false_eq_true, ↓reduceIte] using next

private theorem invocation_rule {result : Val → Env → Prop} (hf : fs[function]? = some fn)
    (hb : EvalSpec fs fn.body reversed (fun value _ => result value caller))
    (continuation : ∀ remaining, remaining ≤ budget → ∀ value final,
      result value final → Safe fs remaining (.ret value final suffix) post) :
    Safe fs budget (.invoke function reversed caller suffix) post := by
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    have next : Safe fs budget (.eval fn.body reversed (.callReturn caller :: suffix)) post := by
      apply hb
      intro remaining hr value final hresult
      cases remaining with
      | zero => simp [Safe, run, step, RunSafe]
      | succ remaining => exact continuation remaining (by omega) value caller hresult
    simpa only [Safe, run, step, hf] using next

def ArgsSpec (fs : Functions) : List Term → Env → (Env → Env → Prop) → Prop
  | [], env, result => result [] env
  | arg :: args, env, result => EvalSpec fs arg env (fun value current =>
      ArgsSpec fs args current (fun values final => result (value :: values) final))

theorem args_spec_mono (h : ArgsSpec fs args env result)
    (weaken : ∀ values final, result values final → result' values final) :
    ArgsSpec fs args env result' := by
  induction args generalizing env result result' with
  | nil => exact weaken [] env h
  | cons arg args ih =>
    apply spec_mono h
    intro value current hrest
    exact ih hrest (fun values final hout => weaken (value :: values) final hout)

private def argumentStart (function : Nat) (args : List Term) (previous : Env)
    (env : Env) (suffix : List Frame) : State :=
  match args with
  | [] => .invoke function previous env suffix
  | arg :: args => .eval arg env (.arguments function args previous :: suffix)

private theorem arguments_rule (hargs : ArgsSpec fs args env result)
    (continuation : ∀ values final, result values final → ∀ remaining, remaining ≤ budget →
      Safe fs remaining (.invoke function (values.reverse ++ previous) final suffix) post) :
    Safe fs budget (argumentStart function args previous env suffix) post := by
  induction args generalizing env result previous budget with
  | nil => exact continuation [] env hargs budget (Nat.le_refl _)
  | cons arg args ih =>
    apply hargs
    intro remaining hr value current hrest
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      have next : Safe fs remaining (argumentStart function args (value :: previous) current suffix) post := by
        apply ih hrest
        intro values final hresult left hl
        have accepted := continuation (value :: values) final hresult left (by omega)
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using accepted
      cases args <;> exact next

theorem call_rule
    (hargs : ArgsSpec fs args env (fun values caller => ∃ fn,
      fs[function]? = some fn ∧ EvalSpec fs fn.body values.reverse
        (fun value _ => result value caller))) :
    EvalSpec fs (.call function args) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    have next : Safe fs budget (argumentStart function args [] env suffix) post := by
      apply arguments_rule hargs
      intro values caller hbody remaining hr
      obtain ⟨fn, hf, hb⟩ := hbody
      simp only [List.append_nil]
      apply invocation_rule hf hb
      intro left hl value final hresult
      exact continuation left (by omega) value final hresult
    cases args <;> exact next

/-- Fields are captured as scalar values after each complete, ordered evaluation. -/
def FieldsSpec (fs : Functions) : List Term → Env → (List APL.Val → Env → Prop) → Prop
  | [], env, result => result [] env
  | field :: fields, env, result => EvalSpec fs field env (fun value current =>
      ∃ scalar, value = .scalar scalar ∧
        FieldsSpec fs fields current (fun values final => result (scalar :: values) final))

theorem fields_spec_mono (h : FieldsSpec fs fields env result)
    (weaken : ∀ values final, result values final → result' values final) :
    FieldsSpec fs fields env result' := by
  induction fields generalizing env result result' with
  | nil => exact weaken [] env h
  | cons field fields ih =>
    apply spec_mono h
    intro value current hrest
    obtain ⟨scalar, rfl, hrest⟩ := hrest
    exact ⟨scalar, rfl, ih hrest (fun values final hout => weaken (scalar :: values) final hout)⟩

private def fieldStart (fields : List Term) (previous : List APL.Val)
    (env : Env) (suffix : List Frame) : State :=
  match fields with
  | [] => resume (construct previous.reverse) env suffix
  | field :: fields => .eval field env (.fields fields previous :: suffix)

private theorem fields_rule (hfields : FieldsSpec fs fields env result)
    (continuation : ∀ values final, result values final → ∀ remaining, remaining ≤ budget →
      Safe fs remaining (resume (construct (previous.reverse ++ values)) final suffix) post) :
    Safe fs budget (fieldStart fields previous env suffix) post := by
  induction fields generalizing env result previous budget with
  | nil => simpa [fieldStart] using continuation [] env hfields budget (Nat.le_refl _)
  | cons field fields ih =>
    apply hfields
    intro remaining hr value current hrest
    obtain ⟨scalar, rfl, hrest⟩ := hrest
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      have next : Safe fs remaining (fieldStart fields (scalar :: previous) current suffix) post := by
        apply ih hrest
        intro values final hresult left hl
        have accepted := continuation (scalar :: values) final hresult left (by omega)
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using accepted
      cases fields <;> exact next

/-- Construction runs every field before checking and packaging the complete list. -/
theorem tuple_rule
    (hfields : FieldsSpec fs fields env (fun values final => ∃ actual,
      construct values = .value actual ∧ result actual final)) :
    EvalSpec fs (.tuple fields) env result := by
  cases fields with
  | nil => simp [FieldsSpec, construct, Flat.make] at hfields
  | cons field fields =>
    intro budget suffix post continuation
    cases budget with
    | zero => simp [Safe, run, step, RunSafe]
    | succ budget =>
      change Safe fs budget (.eval field env (.fields fields [] :: suffix)) post
      apply fields_rule (previous := []) hfields
      intro values final hresult remaining hr
      obtain ⟨actual, hactual, hresult⟩ := hresult
      simpa only [List.reverse_nil, List.nil_append, hactual, resume] using
        continuation remaining (by omega) actual final hresult

/-- Projection evaluates its complete base once, including unselected fields. -/
theorem projection_rule
    (hbase : EvalSpec fs base env (fun value final => ∃ actual,
      project value index = .value actual ∧ result actual final)) :
    EvalSpec fs (.project base index) env result := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    change Safe fs budget (.eval base env (.project index :: suffix)) post
    apply hbase
    intro remaining hr value final hout
    obtain ⟨actual, hactual, hresult⟩ := hout
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      simpa only [Safe, run, step, hactual, resume] using
        continuation remaining (by omega) actual final hresult

/-- A captured tuple never short-circuits evaluation of the right operand. -/
theorem tuple_binary_rule {middle : Flat APL.Val → Env → Prop}
    (hl : EvalSpec fs left env (fun value current => ∃ captured : Flat APL.Val,
      value = .tuple captured ∧ middle captured current))
    (hr : ∀ captured current, middle captured current →
      EvalSpec fs right current (fun other final => ∃ actual,
        binary op (.tuple captured) other = .value actual ∧ result actual final)) :
    EvalSpec fs (.binary op left right) env result := by
  apply binary_rule hl
  · intro value current hmiddle hshort
    obtain ⟨captured, rfl, _⟩ := hmiddle
    simp [shortCircuit] at hshort
  · intro value current hmiddle _
    obtain ⟨captured, rfl, hmiddle⟩ := hmiddle
    exact hr captured current hmiddle

private theorem condition_rule
    (conditionSpec : ∀ env, invariant env → EvalSpec fs condition env
      (fun value final => ∃ test, value = (.scalar (.bool test)) ∧ guard test final))
    (bodySpec : ∀ env, guard true env → EvalSpec fs body env
      (fun value final => value = (.scalar .unit) ∧ invariant final)) :
    ∀ budget env, invariant env → ∀ suffix post,
      (∀ remaining, remaining ≤ budget → ∀ value final,
        value = (.scalar .unit) ∧ guard false final → Safe fs remaining (.ret value final suffix) post) →
      Safe fs budget (.eval condition env (.condition condition body :: suffix)) post := by
  intro budget
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
    intro env hentry suffix post continuation
    apply conditionSpec env hentry
    intro remaining hr value final hresult
    obtain ⟨test, rfl, hguard⟩ := hresult
    cases remaining with
    | zero => simp [Safe, run, step, RunSafe]
    | succ remaining =>
      cases test with
      | false =>
        simpa only [Safe, run, step] using
          continuation remaining (by omega) (.scalar .unit) final ⟨rfl, hguard⟩
      | true =>
        change Safe fs remaining (.eval body final (.body condition body :: suffix)) post
        apply bodySpec final hguard
        intro left hl value last hbody
        obtain ⟨rfl, hinvariant⟩ := hbody
        cases left with
        | zero => simp [Safe, run, step, RunSafe]
        | succ left =>
          change Safe fs left (.eval condition last (.condition condition body :: suffix)) post
          apply ih left (by omega) last hinvariant suffix post
          intro rest hrest value final hout
          exact continuation rest (by omega) value final hout

theorem invariant_loop_rule
    (conditionSpec : ∀ env, invariant env → EvalSpec fs condition env
      (fun value final => ∃ test, value = (.scalar (.bool test)) ∧ guard test final))
    (bodySpec : ∀ env, guard true env → EvalSpec fs body env
      (fun value final => value = (.scalar .unit) ∧ invariant final))
    (initial : invariant entry) :
    EvalSpec fs (.whileE condition body) entry
      (fun value final => value = (.scalar .unit) ∧ guard false final) := by
  intro budget suffix post continuation
  cases budget with
  | zero => simp [Safe, run, step, RunSafe]
  | succ budget =>
    change Safe fs budget (.eval condition entry (.condition condition body :: suffix)) post
    apply condition_rule conditionSpec bodySpec budget entry initial suffix post
    intro remaining hr value final hout
    exact continuation remaining (by omega) value final hout

theorem closed_run (h : EvalSpec fs e env result) :
    RunSafe result (run fs budget (.eval e env [])) := by
  apply h budget [] result
  intro remaining _ value final hresult
  cases remaining <;> simpa [Safe, run, step, RunSafe] using hresult

private def appendSuffix (suffix : List Frame) : State → State
  | .eval e env k => .eval e env (k ++ suffix)
  | .ret v env k => .ret v env (k ++ suffix)
  | .invoke f values env k => .invoke f values env (k ++ suffix)
  | .trap kind => .trap kind
  | .invalid => .invalid

private theorem append_resume : appendSuffix suffix (resume r env k) =
    resume r env (k ++ suffix) := by cases r <;> rfl

private theorem append_step (hs : Step fs s s') :
    Step fs (appendSuffix suffix s) (appendSuffix suffix s') := by
  apply step_sound
  cases hs <;> simp_all [step, appendSuffix]
  all_goals exact append_resume.symm

private theorem stopped_lift (hs : step fs s = none)
    (h : Safe fs budget s result)
    (continuation : ∀ remaining, remaining ≤ budget → ∀ value final,
      result value final → Safe fs remaining (.ret value final suffix) post) :
    Safe fs budget (appendSuffix suffix s) post := by
  rcases stopped_iff.mp hs with terminal | invalid
  · cases terminal with
    | @value value final =>
      have hr : result value final := by
        cases budget <;> simpa [Safe, run, step, RunSafe] using h
      exact continuation budget (Nat.le_refl _) value final hr
    | trap => cases budget <;> simp [Safe, run, step, RunSafe] at h
  · subst s
    cases budget <;> simp [Safe, run, step, RunSafe] at h

-- A closed checked run can be composed with any safe continuation at the exact
-- remaining budget. This follows actual steps; it adds no evaluation relation.
private theorem safe_lift (h : Safe fs budget s result)
    (continuation : ∀ remaining, remaining ≤ budget → ∀ value final,
      result value final → Safe fs remaining (.ret value final suffix) post) :
    Safe fs budget (appendSuffix suffix s) post := by
  induction budget generalizing s with
  | zero =>
    cases hs : step fs s with
    | none => exact stopped_lift hs h continuation
    | some next =>
      have lifted := step_complete (append_step (suffix := suffix) (step_sound hs))
      simp [Safe, run, lifted, RunSafe]
  | succ budget ih =>
    cases hs : step fs s with
    | none => exact stopped_lift hs h continuation
    | some next =>
      have lifted := step_complete (append_step (suffix := suffix) (step_sound hs))
      have htail : Safe fs budget next result := by simpa only [Safe, run, hs] using h
      have result := ih htail (fun remaining hr value final hv =>
        continuation remaining (by omega) value final hv)
      simpa only [Safe, run, lifted] using result

theorem closed_to_spec
    (h : ∀ budget, RunSafe result (run fs budget (.eval e env []))) :
    EvalSpec fs e env result := by
  intro budget suffix post continuation
  exact safe_lift (h budget) continuation

theorem spec_frame (h : EvalSpec fs e env result) (wf : WellTyped fs)
    (ht : HasType (signatures fs) Γ e t) (hen : EnvTyped env Γ) :
    EvalSpec fs e env (fun value final => result value final ∧
      Frozen Γ env final ∧ EnvTyped final Γ ∧ value.type = t) := by
  apply closed_to_spec
  intro budget
  have safe := closed_run (budget := budget) h
  cases hr : run fs budget (.eval e env []) with
  | none => trivial
  | some last =>
    rw [hr] at safe
    cases last with
    | eval _ _ _ | invoke _ _ _ _ | trap _ | invalid => exact False.elim safe
    | ret value final k =>
      cases k with
      | cons _ _ => exact False.elim safe
      | nil => exact ⟨safe, evaluation_frame wf ht hen (run_sound hr).1⟩

theorem no_finite_trap (h : EvalSpec fs e env result) :
    ¬ Steps fs (.eval e env []) (.trap kind) := by
  intro trace
  obtain ⟨budget, hr⟩ := run_complete trace rfl
  have safe := closed_run (budget := budget) h
  simp only [hr, RunSafe] at safe

theorem no_finite_invalid (h : EvalSpec fs e env result) :
    ¬ Steps fs (.eval e env []) .invalid := by
  intro trace
  obtain ⟨budget, hr⟩ := run_complete trace rfl
  have safe := closed_run (budget := budget) h
  simp only [hr, RunSafe] at safe

/-- Every finite normal trace satisfies the result and final-environment relation. -/
theorem normal_result (h : EvalSpec fs e env result)
    (trace : Steps fs (.eval e env []) (.ret value final [])) : result value final := by
  obtain ⟨budget, hr⟩ := run_complete trace rfl
  have safe := closed_run (budget := budget) h
  simpa only [hr, RunSafe] using safe

end APL.FlatProducts.LoopVerification
