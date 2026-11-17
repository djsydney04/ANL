import APL.Machine

namespace APL

inductive Step : State → State → Prop where
  | lit : Step (.eval (.lit v) env k) (.ret v k)
  | localFound : env[i]? = some v → Step (.eval (.local i) env k) (.ret v k)
  | localMissing : env[i]? = none → Step (.eval (.local i) env k) .invalid
  | letEval : Step (.eval (.letE a b) env k) (.eval a env (.letF env b :: k))
  | ifEval : Step (.eval (.ifE c a b) env k) (.eval c env (.ifF env a b :: k))
  | unaryEval : Step (.eval (.unary op a) env k) (.eval a env (.unary op :: k))
  | binaryEval : Step (.eval (.binary op a b) env k) (.eval a env (.left op env b :: k))
  | letReturn : Step (.ret v (.letF env b :: k)) (.eval b (v :: env) k)
  | ifTrue : Step (.ret (.bool true) (.ifF env a b :: k)) (.eval a env k)
  | ifFalse : Step (.ret (.bool false) (.ifF env a b :: k)) (.eval b env k)
  | ifInt : Step (.ret (.int n) (.ifF env a b :: k)) .invalid
  | ifUnit : Step (.ret .unit (.ifF env a b :: k)) .invalid
  | unaryReturn : Step (.ret v (.unary op :: k)) (resume (unary op v) k)
  | short : shortCircuit op v = true → Step (.ret v (.left op env b :: k)) (.ret v k)
  | rightEval : shortCircuit op v = false →
      Step (.ret v (.left op env b :: k)) (.eval b env (.right op v :: k))
  | binaryReturn : Step (.ret v (.right op a :: k)) (resume (binary op a v) k)

theorem step_complete (h : Step s s') : step s = some s' := by
  cases h <;> simp_all [step]

theorem step_sound (h : step s = some s') : Step s s' := by
  cases s with
  | eval e env k =>
    cases e with
    | lit v => cases h; exact .lit
    | «local» i =>
      cases he : env[i]? with
      | none => simp [step, he] at h; subst s'; exact .localMissing he
      | some v => simp [step, he] at h; subst s'; exact .localFound he
    | letE a b => cases h; exact .letEval
    | ifE c a b => cases h; exact .ifEval
    | unary op a => cases h; exact .unaryEval
    | binary op a b => cases h; exact .binaryEval
  | ret v k =>
    cases k with
    | nil => simp [step] at h
    | cons f k =>
      cases f with
      | letF env b => cases h; exact .letReturn
      | ifF env a b =>
        cases v with
        | int n => cases h; exact .ifInt
        | unit => cases h; exact .ifUnit
        | bool v =>
          cases v <;> cases h
          · exact .ifFalse
          · exact .ifTrue
      | unary op => cases h; exact .unaryReturn
      | left op env b =>
        cases hs : shortCircuit op v <;> simp [step, hs] at h <;> subst s'
        · exact .rightEval hs
        · exact .short hs
      | right op a => cases h; exact .binaryReturn
  | trap kind => simp [step] at h
  | invalid => simp [step] at h

theorem preservation (h : s.Typed t) (hs : Step s s') : s'.Typed t :=
  step_preserves h (step_complete hs)

theorem relational_progress (h : s.Typed t) : Terminal s ∨ ∃ s', Step s s' := by
  rcases progress h with ht | ⟨s', hs⟩
  · exact Or.inl ht
  · exact Or.inr ⟨s', step_sound hs⟩

inductive Steps : State → State → Prop where
  | refl : Steps s s
  | head : Step s s' → Steps s' last → Steps s last

def run : Nat → State → Option State
  | 0, _ => none
  | fuel + 1, s => match step s with
    | none => some s
    | some s' => run fuel s'

theorem run_sound (h : run fuel s = some last) : Steps s last ∧ step last = none := by
  induction fuel generalizing s with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step s with
    | none => simp [run, hs] at h; subst last; exact ⟨.refl, hs⟩
    | some s' =>
      simp [run, hs] at h
      obtain ⟨steps, final⟩ := ih h
      exact ⟨.head (step_sound hs) steps, final⟩

theorem run_complete (h : Steps s last) (ht : step last = none) :
    ∃ fuel, run fuel s = some last := by
  induction h with
  | refl => exact ⟨1, by simp [run, ht]⟩
  | head hs _ ih =>
    obtain ⟨fuel, hf⟩ := ih ht
    exact ⟨fuel + 1, by simp [run, step_complete hs, hf]⟩

theorem steps_preserve (h : s.Typed t) (hs : Steps s last) : last.Typed t := by
  induction hs with
  | refl => exact h
  | head hs _ ih => exact ih (preservation h hs)

theorem run_safety (h : s.Typed t) (hr : run fuel s = some last) :
    last.Typed t ∧ Terminal last := by
  obtain ⟨steps, stop⟩ := run_sound hr
  have typed := steps_preserve h steps
  refine ⟨typed, ?_⟩
  rcases progress typed with terminal | ⟨next, hn⟩
  · exact terminal
  · rw [stop] at hn; contradiction

theorem closed_safety (h : HasType [] e t) (hr : run fuel (.eval e [] []) = some last) :
    (∃ v, last = .ret v [] ∧ v.type = t) ∨ (∃ trap, last = .trap trap) := by
  have initial : State.Typed (.eval e [] []) t := .eval h .nil
  obtain ⟨ht, final⟩ := run_safety initial hr
  cases final with
  | @value v =>
    cases ht with
    | ret hk => cases hk; exact Or.inl ⟨v, rfl, rfl⟩
  | @trap kind => exact Or.inr ⟨kind, rfl⟩

end APL
