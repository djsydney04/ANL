import ANL.BootTail
import ANL.WordsRunProofs

namespace ANL.Boot

open ANL.Words

abbrev trueTerm : Term := .lit boolTy (.bool true)
abbrev emptyTerm : Term := .lit unitTy .unit

/-- A pending nonreturning body protects every continuation below this binding. -/
def KontBarrier (depth : Nat) : List Frame → Prop
  | [] => False
  | .bind _ body :: rest => (HasTail body ∧ depth ≤ rest.length) ∨ KontBarrier depth rest
  | _ :: rest => KontBarrier depth rest

theorem KontBarrier.push (h : KontBarrier depth k) : KontBarrier depth (frame :: k) := by
  cases frame <;> simp only [KontBarrier] <;> first | exact h | exact Or.inr h

theorem KontBarrier.length (h : KontBarrier depth k) : depth < k.length := by
  induction k with
  | nil => contradiction
  | cons frame k ih =>
    cases frame <;> simp only [KontBarrier] at h
    all_goals first
      | have := ih h; simp only [List.length_cons]; omega
      | rcases h with ⟨_, bound⟩ | h
        · simp only [List.length_cons]; omega
        · have := ih h; simp only [List.length_cons]; omega

/-- A concrete continuation invariant; trap/invalid remain stopped, without cleanup. -/
inductive ReturnShield (depth : Nat) : State → Prop where
  | kont : KontBarrier depth k → ReturnShield depth ⟨ctl, a, k, w⟩
  | eval : HasTail body → depth ≤ k.length → ReturnShield depth ⟨.eval body, a, k, w⟩
  | condition : depth ≤ k.length →
      ReturnShield depth ⟨.eval trueTerm, a, .condition trueTerm emptyTerm :: k, w⟩
  | trueValue : depth ≤ k.length →
      ReturnShield depth ⟨.ret (.scalar (.legacy (.bool true))), a, .condition trueTerm emptyTerm :: k, w⟩
  | body : depth ≤ k.length →
      ReturnShield depth ⟨.eval emptyTerm, a, .body trueTerm emptyTerm :: k, w⟩
  | unitValue : depth ≤ k.length →
      ReturnShield depth ⟨.ret (.scalar (.legacy .unit)), a, .body trueTerm emptyTerm :: k, w⟩
  | trap : ReturnShield depth ⟨.trap kind, a, k, w⟩
  | invalid : ReturnShield depth ⟨.invalid, a, k, w⟩

theorem shield_resume (h : KontBarrier depth k) : ReturnShield depth (resume result a k w) := by
  cases result <;> exact .kont h

theorem shield_arguments (h : KontBarrier depth k) :
    ReturnShield depth (beginArguments f loan args values a k w) := by
  cases args
  · exact .kont h
  · exact .kont h.push

theorem kontBarrier_step (hs : Step p responses s next) (barrier : KontBarrier depth s.kont) :
    ReturnShield depth next := by
  cases hs <;> simp only [KontBarrier] at barrier
  all_goals try first
    | exact .kont barrier
    | exact .kont barrier.push
    | exact shield_resume barrier
    | exact shield_arguments barrier
  rcases barrier with ⟨tail, bound⟩ | barrier
  · exact .eval tail (by simpa only [List.length_cons] using Nat.le_succ_of_le bound)
  · exact .kont barrier.push

theorem tail_eval_step (tail : HasTail body) (bound : depth ≤ k.length)
    (hs : Step p responses ⟨.eval body, a, k, w⟩ next) : ReturnShield depth next := by
  cases tail with
  | park =>
    have eq := deterministic hs (Step.whileEval (p := p) (responses := responses)
      (a := a) (k := k) (w := w) (t := unitTy) (c := trueTerm) (b := emptyTerm))
    cases eq
    exact .condition bound
  | letValue tail =>
    have eq := deterministic hs Step.letEval
    cases eq
    exact .eval tail (Nat.le_succ_of_le bound)
  | letBody tail =>
    have eq := deterministic hs Step.letEval
    cases eq
    exact .kont (Or.inl ⟨tail, bound⟩)
  | mutValue tail =>
    have eq := deterministic hs Step.letMutEval
    cases eq
    exact .eval tail (Nat.le_succ_of_le bound)
  | mutBody tail =>
    have eq := deterministic hs Step.letMutEval
    cases eq
    exact .kont (Or.inl ⟨tail, bound⟩)

theorem ReturnShield.step (shield : ReturnShield depth s) (hs : Step p responses s next) :
    ReturnShield depth next := by
  cases shield with
  | kont barrier => exact kontBarrier_step hs barrier
  | eval tail bound => exact tail_eval_step tail bound hs
  | condition bound =>
    have eq := deterministic hs (Step.lit (v := .bool true))
    cases eq
    exact .trueValue bound
  | trueValue bound =>
    have eq := deterministic hs Step.whileTrue
    cases eq
    exact .body bound
  | body bound =>
    have eq := deterministic hs (Step.lit (v := .unit))
    cases eq
    exact .unitValue bound
  | unitValue bound =>
    have eq := deterministic hs Step.whileAgain
    cases eq
    exact .condition bound
  | trap => cases hs
  | invalid => cases hs

theorem ReturnShield.steps (shield : ReturnShield depth s) (steps : Steps p responses s last) :
    ReturnShield depth last := by
  induction steps with
  | refl => exact shield
  | head step _ ih => exact ih (shield.step step)

theorem ReturnShield.return_depth (shield : ReturnShield depth ⟨.ret value, a, k, w⟩) :
    depth < k.length := by
  cases shield with
  | kont barrier => exact barrier.length
  | trueValue bound | unitValue bound => simp only [List.length_cons]; omega

theorem HasTail.no_normal_return (tail : HasTail body)
    (steps : Steps p responses ⟨.eval body, a, k, w⟩ ⟨.ret value, finalActivation, finalKont, finalWorld⟩) :
    k.length < finalKont.length :=
  ((ReturnShield.eval tail (Nat.le_refl k.length)).steps steps).return_depth

theorem NoNormalReturn.no_normal_return (h : NoNormalReturn sigs Γ R body t)
    (steps : Steps p responses ⟨.eval body, a, k, w⟩ last) :
    ∀ value finalActivation finalWorld, last ≠ ⟨.ret value, finalActivation, k, finalWorld⟩ := by
  intro value finalActivation finalWorld eq
  subst last
  have := h.tail.no_normal_return steps
  omega

theorem NoNormalReturn.no_value_terminal (h : NoNormalReturn sigs Γ R body t)
    (steps : Steps p responses ⟨.eval body, a, k, w⟩ ⟨.ret value, finalActivation, [], finalWorld⟩) : False := by
  have := h.tail.no_normal_return steps
  simp at this

end ANL.Boot
