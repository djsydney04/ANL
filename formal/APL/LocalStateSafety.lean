import APL.LocalStateTyping
import APL.LocalStateRun

namespace APL.LocalState

theorem resume_typed (h : r.Typed a) (he : EnvTyped env Γ) (hk : KontTyped sigs Γ k a t) :
    (resume r env k).Typed sigs t := by
  cases r with
  | value v => exact .ret he (by simpa [Result.Typed] using h ▸ hk)
  | trap kind => exact .trap
  | invalid => exact False.elim h

theorem preservation (wf : WellTyped fs) (h : s.Typed (signatures fs) t)
    (hs : Step fs s s') : s'.Typed (signatures fs) t := by
  cases hs with
  | lit => cases h with | eval he hen hk => cases he; exact .ret hen hk
  | localFound hv =>
    cases h with
    | eval he hen hk =>
      cases he with
      | «local» ht =>
        obtain ⟨v, hv', ht⟩ := env_lookup hen ht
        rw [hv] at hv'
        cases hv'
        exact .ret hen (ht ▸ hk)
  | localMissing hv =>
    cases h with
    | eval he hen hk =>
      cases he with
      | «local» ht =>
        obtain ⟨v, hv', _⟩ := env_lookup hen ht
        rw [hv] at hv'
        contradiction
  | letEval =>
    cases h with | eval he hen hk => cases he with | letE ha hb => exact .eval ha hen (.cons (.bind hb) hk)
  | letMutEval =>
    cases h with | eval he hen hk => cases he with | letMut ha hb => exact .eval ha hen (.cons (.bind hb) hk)
  | bindReturn =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | bind hb => exact .eval hb (env_cons hen) (.cons .scope hk)
  | scopeReturn =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf; exact .ret (env_tail hen) hk
  | scopeMissing =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf; simp [EnvTyped] at hen
  | assignEval =>
    cases h with | eval he hen hk => cases he with | assign hi ha => exact .eval ha hen (.cons (.assign hi) hk)
  | assignReturn hu =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | assign hi =>
      obtain ⟨env', hu', ht⟩ := update_typed hen hi
      rw [hu] at hu'
      cases hu'
      exact .ret ht hk
  | assignMissing hu =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | assign hi =>
      obtain ⟨env', hu', _⟩ := update_typed hen hi
      rw [hu] at hu'
      contradiction
  | ifEval =>
    cases h with | eval he hen hk => cases he with | ifE hc ha hb => exact .eval hc hen (.cons (.ifF ha hb) hk)
  | unaryEval =>
    cases h with | eval he hen hk => cases he with | unary ha => exact .eval ha hen (.cons .unary hk)
  | binaryEval =>
    cases h with | eval he hen hk => cases he with | binary ha hb hop => exact .eval ha hen (.cons (.left hb hop) hk)
  | ifTrue =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with | ifF ha hb => exact .eval ha hen hk
  | ifFalse =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with | ifF ha hb => exact .eval hb hen hk
  | ifInt => cases h with | ret hen hk => cases hk with | cons hf hk => cases hf
  | ifUnit => cases h with | ret hen hk => cases hk with | cons hf hk => cases hf
  | unaryReturn =>
    cases h with
    | ret hen hk =>
      generalize hv : Val.type _ = a at hk
      cases hk with
      | cons hf hk => cases hf; exact resume_typed (unary_typed hv) hen hk
  | short hs =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | left hb hop => exact .ret hen ((shortCircuit_typed hop hs) ▸ hk)
  | rightEval =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | left hb hop => exact .eval hb hen (.cons (.right hop) hk)
  | binaryReturn =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | right hop => exact resume_typed (binary_typed hop) hen hk
  | callEmpty =>
    cases h with | eval he hen hk => cases he with | call hf ha => cases ha; exact .invoke hf hen hk
  | callFirst =>
    cases h with | eval he hen hk => cases he with | call hf ha => cases ha with
    | cons ha hs => exact .eval ha hen (.cons (.arguments hs hf) hk)
  | argumentNext =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | arguments ha hf =>
      cases ha with
      | cons ha hs =>
        exact .eval ha hen (.cons (.arguments hs (by simpa [List.reverse_cons, List.append_assoc] using hf)) hk)
  | argumentsDone =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | arguments ha hf =>
      cases ha
      exact .invoke (by simpa [List.reverse_cons] using hf) hen hk
  | invoke hf =>
    cases h with
    | invoke hs hen hk =>
      have sig := signatures_lookup hf
      rw [sig] at hs
      have eq := (Prod.mk.inj (Option.some.inj hs)).1
      have result := (Prod.mk.inj (Option.some.inj hs)).2
      have body := wf _ _ hf
      rw [eq, List.reverse_reverse, result] at body
      exact .eval body (by simp [EnvTyped, immutable, List.map_map]) (.cons (.callReturn hen) hk)
  | invalidFunction hf =>
    cases h with
    | invoke hs hen hk =>
      obtain ⟨fn, hf', _, _⟩ := signatures_lookup_inv hs
      rw [hf] at hf'
      contradiction
  | callReturn =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | callReturn hcaller => exact .ret hcaller hk
  | whileEval =>
    cases h with | eval he hen hk => cases he with | whileE hc hb => exact .eval hc hen (.cons (.condition hc hb) hk)
  | whileTrue =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | condition hc hb => exact .eval hb hen (.cons (.body hc hb) hk)
  | whileFalse =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | condition hc hb => exact .ret hen hk
  | whileInt => cases h with | ret hen hk => cases hk with | cons hf hk => cases hf
  | whileUnit => cases h with | ret hen hk => cases hk with | cons hf hk => cases hf
  | whileAgain =>
    cases h with | ret hen hk => cases hk with | cons hf hk => cases hf with
    | body hc hb => exact .eval hc hen (.cons (.condition hc hb) hk)
  | bodyInt => cases h with | ret hen hk => cases hk with | cons hf hk => cases hf
  | bodyBool => cases h with | ret hen hk => cases hk with | cons hf hk => cases hf

theorem progress (h : s.Typed (signatures fs) t) : Terminal s ∨ ∃ s', Step fs s s' := by
  cases hs : step fs s with
  | some s' => exact .inr ⟨s', step_sound hs⟩
  | none =>
    rcases stopped_iff.mp hs with final | invalid
    · exact .inl final
    · subst s; cases h

theorem steps_preserve (wf : WellTyped fs) (h : s.Typed (signatures fs) t)
    (hs : Steps fs s last) : last.Typed (signatures fs) t := by
  induction hs with
  | refl => exact h
  | head hs _ ih => exact ih (preservation wf h hs)

theorem safety (wf : WellTyped fs) (h : s.Typed (signatures fs) t)
    (hs : Steps fs s last) :
    last.Typed (signatures fs) t ∧ (Terminal last ∨ ∃ next, Step fs last next) := by
  have ht := steps_preserve wf h hs
  exact ⟨ht, progress ht⟩

theorem no_invalid (wf : WellTyped fs) (h : s.Typed (signatures fs) t) :
    ¬ Steps fs s .invalid := by
  intro hs
  cases steps_preserve wf h hs

theorem finite_run_safe (wf : WellTyped fs) (h : s.Typed (signatures fs) t)
    (hr : run fs fuel s = some last) :
    (∃ v env, last = .ret v env [] ∧ v.type = t) ∨ (∃ kind, last = .trap kind) := by
  obtain ⟨hs, stop⟩ := run_sound hr
  have ht := steps_preserve wf h hs
  rcases stopped_iff.mp stop with final | invalid
  · cases final with
    | @value v env =>
      cases ht with
      | ret hen hk => cases hk; exact .inl ⟨v, env, rfl, rfl⟩
    | @trap kind => exact .inr ⟨kind, rfl⟩
  · subst last; cases ht

theorem entry_typed {fs : Functions} {f : Nat} {fn : Function}
    (hf : fs[f]? = some fn) (arity : fn.params = []) :
    State.Typed (signatures fs) (.invoke f [] [] []) fn.result := by
  exact .invoke (by simpa [arity] using signatures_lookup hf) (Γ := []) rfl .nil

theorem entry_safety {fs : Functions} {f : Nat} {fn : Function}
    (wf : WellTyped fs) (hf : fs[f]? = some fn) (arity : fn.params = [])
    (hs : Steps fs (.invoke f [] [] []) last) :
    last.Typed (signatures fs) fn.result ∧ (Terminal last ∨ ∃ next, Step fs last next) :=
  safety wf (entry_typed hf arity) hs

end APL.LocalState
