import APL.LocalState

namespace APL.LocalState

theorem step_complete (h : Step fs s s') : step fs s = some s' := by
  cases h <;> simp_all [step]

theorem step_sound (h : step fs s = some s') : Step fs s s' := by
  cases s with
  | eval e env k =>
    cases e with
    | lit v => simp only [step, Option.some.injEq] at h; subst s'; exact .lit
    | «local» i =>
      cases hi : env[i]? with
      | none => simp only [step, hi, Option.some.injEq] at h; subst s'; exact .localMissing hi
      | some v => simp only [step, hi, Option.some.injEq] at h; subst s'; exact .localFound hi
    | letE a b => simp only [step, Option.some.injEq] at h; subst s'; exact .letEval
    | letMut a b => simp only [step, Option.some.injEq] at h; subst s'; exact .letMutEval
    | assign i a => simp only [step, Option.some.injEq] at h; subst s'; exact .assignEval
    | whileE c b => simp only [step, Option.some.injEq] at h; subst s'; exact .whileEval
    | ifE c a b => simp only [step, Option.some.injEq] at h; subst s'; exact .ifEval
    | unary op a => simp only [step, Option.some.injEq] at h; subst s'; exact .unaryEval
    | binary op a b => simp only [step, Option.some.injEq] at h; subst s'; exact .binaryEval
    | call f args =>
      cases args with
      | nil => simp only [step, Option.some.injEq] at h; subst s'; exact .callEmpty
      | cons a args => simp only [step, Option.some.injEq] at h; subst s'; exact .callFirst
  | ret v env k =>
    cases k with
    | nil => simp [step] at h
    | cons f k =>
      cases f with
      | bind permission b => simp only [step, Option.some.injEq] at h; subst s'; exact .bindReturn
      | scope =>
        cases env with
        | nil => simp only [step, Option.some.injEq] at h; subst s'; exact .scopeMissing
        | cons a env => simp only [step, Option.some.injEq] at h; subst s'; exact .scopeReturn
      | assign i =>
        cases hi : update env i v with
        | none => simp only [step, hi, Option.some.injEq] at h; subst s'; exact .assignMissing hi
        | some env' => simp only [step, hi, Option.some.injEq] at h; subst s'; exact .assignReturn hi
      | ifF a b =>
        cases v with
        | int n => simp only [step, Option.some.injEq] at h; subst s'; exact .ifInt
        | unit => simp only [step, Option.some.injEq] at h; subst s'; exact .ifUnit
        | bool test =>
          cases test
          · simp only [step, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst s'; exact .ifFalse
          · simp only [step, ↓reduceIte, Option.some.injEq] at h; subst s'; exact .ifTrue
      | unary op => simp only [step, Option.some.injEq] at h; subst s'; exact .unaryReturn
      | left op b =>
        cases hs : shortCircuit op v
        · simp only [step, hs, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst s'; exact .rightEval hs
        · simp only [step, hs, ↓reduceIte, Option.some.injEq] at h; subst s'; exact .short hs
      | right op a => simp only [step, Option.some.injEq] at h; subst s'; exact .binaryReturn
      | arguments f remaining values =>
        cases remaining with
        | nil => simp only [step, Option.some.injEq] at h; subst s'; exact .argumentsDone
        | cons a args => simp only [step, Option.some.injEq] at h; subst s'; exact .argumentNext
      | callReturn caller => simp only [step, Option.some.injEq] at h; subst s'; exact .callReturn
      | condition c b =>
        cases v with
        | int n => simp only [step, Option.some.injEq] at h; subst s'; exact .whileInt
        | unit => simp only [step, Option.some.injEq] at h; subst s'; exact .whileUnit
        | bool test =>
          cases test
          · simp only [step, Option.some.injEq] at h; subst s'; exact .whileFalse
          · simp only [step, Option.some.injEq] at h; subst s'; exact .whileTrue
      | body c b =>
        cases v with
        | int n => simp only [step, Option.some.injEq] at h; subst s'; exact .bodyInt
        | bool test => simp only [step, Option.some.injEq] at h; subst s'; exact .bodyBool
        | unit => simp only [step, Option.some.injEq] at h; subst s'; exact .whileAgain
  | invoke f values caller k =>
    cases hf : fs[f]? with
    | none => simp only [step, hf, Option.some.injEq] at h; subst s'; exact .invalidFunction hf
    | some fn => simp only [step, hf, Option.some.injEq] at h; subst s'; exact .invoke hf
  | trap kind => simp [step] at h
  | invalid => simp [step] at h

theorem step_iff : step fs s = some s' ↔ Step fs s s' := ⟨step_sound, step_complete⟩

theorem deterministic (ha : Step fs s a) (hb : Step fs s b) : a = b :=
  Option.some.inj ((step_complete ha).symm.trans (step_complete hb))

theorem stopped_iff : step fs s = none ↔ Terminal s ∨ s = .invalid := by
  cases s with
  | eval e env k => simp [step]; intro h; cases h
  | ret v env k =>
    cases k with
    | nil => simp [step]; exact .value
    | cons f k => simp [step]; intro h; cases h
  | invoke f values caller k => simp [step]; intro h; cases h
  | trap kind => simp [step]; exact .trap
  | invalid => simp [step]

theorem run_sound (h : run fs fuel s = some last) : Steps fs s last ∧ step fs last = none := by
  induction fuel generalizing s with
  | zero =>
    simp only [run] at h
    split at h
    next stop =>
      have stop : step fs s = none := Option.isNone_iff_eq_none.mp stop
      cases h
      exact ⟨.refl, stop⟩
    · contradiction
  | succ fuel ih =>
    simp only [run] at h
    cases hs : step fs s with
    | none => simp only [hs] at h; cases h; exact ⟨.refl, hs⟩
    | some s' =>
      simp only [hs] at h
      obtain ⟨rest, stop⟩ := ih h
      exact ⟨.head (step_sound hs) rest, stop⟩

theorem run_complete (h : Steps fs s last) (stop : step fs last = none) :
    ∃ fuel, run fs fuel s = some last := by
  induction h with
  | refl => exact ⟨0, by simp [run, stop]⟩
  | head hs _ ih =>
    obtain ⟨fuel, hf⟩ := ih stop
    exact ⟨fuel + 1, by simp [run, step_complete hs, hf]⟩

theorem run_iff : (∃ fuel, run fs fuel s = some last) ↔ Steps fs s last ∧ step fs last = none := by
  constructor
  · rintro ⟨fuel, h⟩; exact run_sound h
  · rintro ⟨hs, stop⟩; exact run_complete hs stop

end APL.LocalState
