import APL.ProgramTyping

namespace APL.Program

theorem resume_typed (h : r.Typed a) (hk : KontTyped sigs k a t) : (resume r k).Typed sigs t := by
  cases r with
  | value v => exact .ret (by simpa [Result.Typed] using h ▸ hk)
  | trap kind => exact .trap
  | invalid => exact False.elim h

theorem preservation (wf : WellTyped fs) (h : s.Typed (signatures fs) t)
    (hs : Step fs s s') : s'.Typed (signatures fs) t := by
  cases hs with
  | lit => cases h with | eval he hk => cases he; exact .ret hk
  | localFound hv =>
    cases h with
    | eval he hk =>
      cases he with
      | «local» ht =>
        obtain ⟨v, hv', ht⟩ := lookup_typed ht
        rw [hv] at hv'
        cases hv'
        exact .ret (ht ▸ hk)
  | localMissing hv =>
    cases h with
    | eval he hk =>
      cases he with
      | «local» ht =>
        obtain ⟨v, hv', _⟩ := lookup_typed ht
        rw [hv] at hv'
        contradiction
  | letEval =>
    cases h with | eval he hk => cases he with | letE ha hb => exact .eval ha (.cons (.letF hb) hk)
  | ifEval =>
    cases h with | eval he hk => cases he with | ifE hc ha hb => exact .eval hc (.cons (.ifF ha hb) hk)
  | unaryEval =>
    cases h with | eval he hk => cases he with | unary ha => exact .eval ha (.cons .unary hk)
  | binaryEval =>
    cases h with | eval he hk => cases he with | binary ha hb hop => exact .eval ha (.cons (.left hb hop) hk)
  | letReturn =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with | letF hb => exact .eval hb hk
  | ifTrue =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with | ifF ha hb => exact .eval ha hk
  | ifFalse =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with | ifF ha hb => exact .eval hb hk
  | ifInt => cases h with | ret hk => cases hk with | cons hf hk => cases hf
  | ifUnit => cases h with | ret hk => cases hk with | cons hf hk => cases hf
  | unaryReturn =>
    cases h with
    | ret hk =>
      generalize hv : Val.type _ = a at hk
      cases hk with
      | cons hf hk => cases hf; exact resume_typed (unary_typed hv) hk
  | short hs =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with
    | left hb hop => exact .ret ((shortCircuit_typed hop hs) ▸ hk)
  | rightEval =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with
    | left hb hop => exact .eval hb (.cons (.right hop) hk)
  | binaryReturn =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with
    | right hop => exact resume_typed (binary_typed hop) hk
  | callEmpty =>
    cases h with | eval he hk => cases he with | call hf ha => cases ha; exact .invoke hf hk
  | callFirst =>
    cases h with | eval he hk => cases he with | call hf ha => cases ha with
    | cons ha hs => exact .eval ha (.cons (.arguments hs hf) hk)
  | argumentNext =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with
    | arguments ha hf =>
      cases ha with
      | cons ha hs =>
        exact .eval ha (.cons (.arguments hs (by simpa [List.reverse_cons, List.append_assoc] using hf)) hk)
  | argumentsDone =>
    cases h with | ret hk => cases hk with | cons hf hk => cases hf with
    | arguments ha hf =>
      cases ha
      exact .invoke (by simpa [List.reverse_cons] using hf) hk
  | invoke hf =>
    cases h with
    | invoke hs hk =>
      have sig := signatures_lookup hf
      rw [sig] at hs
      have eq := (Prod.mk.inj (Option.some.inj hs)).1
      have result := (Prod.mk.inj (Option.some.inj hs)).2
      have body := wf _ _ hf
      rw [eq, List.reverse_reverse, result] at body
      exact .eval body hk
  | invalidFunction hf =>
    cases h with
    | invoke hs hk =>
      obtain ⟨fn, hf', _, _⟩ := signatures_lookup_inv hs
      rw [hf] at hf'
      contradiction

theorem progress (h : s.Typed (signatures fs) t) : Terminal s ∨ ∃ s', Step fs s s' := by
  cases h with
  | eval he hk =>
    cases he with
    | lit => exact Or.inr ⟨_, .lit⟩
    | «local» ht =>
      obtain ⟨v, hv, _⟩ := lookup_typed ht
      exact Or.inr ⟨_, .localFound hv⟩
    | letE => exact Or.inr ⟨_, .letEval⟩
    | ifE => exact Or.inr ⟨_, .ifEval⟩
    | unary => exact Or.inr ⟨_, .unaryEval⟩
    | binary => exact Or.inr ⟨_, .binaryEval⟩
    | @call Γ f params result args hf ha =>
      cases args with
      | nil => exact Or.inr ⟨_, .callEmpty⟩
      | cons a args => exact Or.inr ⟨_, .callFirst⟩
  | @ret k t v hk =>
    generalize hv : v.type = a at hk
    cases hk with
    | nil => exact Or.inl .value
    | cons hf hk =>
      cases hf with
      | letF => exact Or.inr ⟨_, .letReturn⟩
      | ifF =>
        cases v with
        | int n | unit => contradiction
        | bool b =>
          cases b
          · exact Or.inr ⟨_, .ifFalse⟩
          · exact Or.inr ⟨_, .ifTrue⟩
      | unary => exact Or.inr ⟨_, .unaryReturn⟩
      | @left e b op a t env he hop =>
        cases hs : shortCircuit op v
        · exact Or.inr ⟨_, .rightEval hs⟩
        · exact Or.inr ⟨_, .short hs⟩
      | right => exact Or.inr ⟨_, .binaryReturn⟩
      | @arguments remaining rest f a result caller values ha hf =>
        cases remaining with
        | nil => exact Or.inr ⟨_, .argumentsDone⟩
        | cons e es => exact Or.inr ⟨_, .argumentNext⟩
  | invoke hf hk =>
    obtain ⟨fn, hf, _, _⟩ := signatures_lookup_inv hf
    exact Or.inr ⟨_, .invoke hf⟩
  | trap => exact Or.inl .trap

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

theorem closed_safety (wf : WellTyped fs) (h : HasType (signatures fs) [] e t)
    (hs : Steps fs (.eval e [] []) last) (stop : ¬ ∃ next, Step fs last next) :
    (∃ v, last = .ret v [] ∧ v.type = t) ∨ (∃ kind, last = .trap kind) := by
  have initial : State.Typed (signatures fs) (.eval e [] []) t := .eval h .nil
  obtain ⟨ht, final | next⟩ := safety wf initial hs
  · cases final with
    | @value v =>
      cases ht with
      | ret hk => cases hk; exact Or.inl ⟨v, rfl, rfl⟩
    | @trap kind => exact Or.inr ⟨kind, rfl⟩
  · exact False.elim (stop next)

theorem entry_typed {fs : Functions} {f : Nat} {fn : Function}
    (hf : fs[f]? = some fn) (arity : fn.params = []) :
    State.Typed (signatures fs) (.invoke f [] []) fn.result := by
  exact .invoke (by simpa [arity] using signatures_lookup hf) .nil

theorem entry_safety {fs : Functions} {f : Nat} {fn : Function}
    (wf : WellTyped fs) (hf : fs[f]? = some fn) (arity : fn.params = [])
    (hs : Steps fs (.invoke f [] []) last) :
    last.Typed (signatures fs) fn.result ∧ (Terminal last ∨ ∃ next, Step fs last next) :=
  safety wf (entry_typed hf arity) hs

end APL.Program

namespace APL.Program.Examples

private def recursiveFunctions : Functions := #[
  { name := "first", params := [.bool, .i64], result := .bool,
    body := .call 1 [.local 1, .local 0] },
  { name := "second", params := [.bool, .i64], result := .bool,
    body := .ifE (.local 1) (.lit (.bool true)) (.call 0 [.local 1, .local 0]) }
]

example : WellTyped recursiveFunctions := by
  apply checked_functions
  intro f fn hf
  cases f with
  | zero => simp [recursiveFunctions] at hf; subst fn; simp [signatures, recursiveFunctions, infer, List.mapM_cons]
  | succ f =>
    cases f with
    | zero => simp [recursiveFunctions] at hf; subst fn; simp [signatures, recursiveFunctions, infer, List.mapM_cons, Val.type]
    | succ f => simp [recursiveFunctions] at hf

example : infer (signatures recursiveFunctions) []
    (.call 0 [.lit (.bool false), .lit (.int ⟨0, by decide⟩)]) = some .bool := by simp [signatures, recursiveFunctions, infer, List.mapM_cons, Val.type]

example : infer (signatures recursiveFunctions) []
    (.call 0 [.lit (.int ⟨0, by decide⟩), .lit (.bool false)]) = none := by simp [signatures, recursiveFunctions, infer, List.mapM_cons, Val.type]

example : infer (signatures recursiveFunctions) [] (.call 0 [.lit (.bool false)]) = none := by simp [signatures, recursiveFunctions, infer, List.mapM_cons, Val.type]

example : infer (signatures recursiveFunctions) [] (.call 2 []) = none := by simp [signatures, recursiveFunctions, infer]

end APL.Program.Examples
