import APL.ProductFlowSoundness

namespace APL.ProductFlow
open ProductLogic ProductAnnotations

theorem group_cons : (group (check :: checks)).Holds model ↔
    (check.guard.Holds model → check.required.Holds model) ∧ (group checks).Holds model := Iff.rfl

structure EntryChecks where
  checks : List Check
  path : Formula

def entryChecks (params : List SymValue) : List Spec → Formula → Nat → Option EntryChecks
  | [], path, _ => some ⟨[], path⟩
  | clause :: clauses, path, index => do
      let first ← clause.clause params none []
      let rest ← entryChecks params clauses (.and path first.truth) (index + 1)
      return ⟨⟨.precondition index, path, first.defined⟩ :: rest.checks, rest.path⟩

def postChecks (params : List SymValue) (value : SymValue) (path : Formula) :
    List Spec → Nat → Option (List Check)
  | [], _ => some []
  | clause :: clauses, index => do
      let first ← clause.clause params (some value) []
      let rest ← postChecks params value path clauses (index + 1)
      return ⟨.postcondition index, path, first.truth⟩ :: rest

theorem entry_checks_sound
    (hg : entryChecks symbols clauses path index = some output)
    (hr : EnvRep model symbols params) :
    ((group output.checks).Holds model ↔ (path.Holds model → RequiresDefined params clauses)) ∧
    (output.path.Holds model ↔ path.Holds model ∧ RequiresHold params clauses) := by
  induction clauses generalizing path index output with
  | nil => cases hg; simp [group, Formula.Holds, RequiresDefined, RequiresHold]
  | cons clause clauses ih =>
    simp only [entryChecks, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hrs, heq⟩ := hg
    cases heq
    have hc := clause.clause_sound (result := none) hf hr trivial .nil
    have hrest := ih hrs
    simp only [group_cons, hrest.1, hrest.2, Formula.Holds, hc.1, hc.2,
      RequiresDefined, RequiresHold]
    constructor
    · constructor
      · rintro ⟨defined, tail⟩ hp
        exact ⟨defined hp, fun truth => tail ⟨hp, truth⟩⟩
      · intro h
        exact ⟨fun hp => (h hp).1, fun ⟨hp, truth⟩ => (h hp).2 truth⟩
    · constructor
      · rintro ⟨⟨hp, first⟩, rest⟩; exact ⟨hp, first, rest⟩
      · rintro ⟨hp, first, rest⟩; exact ⟨⟨hp, first⟩, rest⟩

theorem entry_checks_supported
    (hg : entryChecks params clauses path index = some output)
    (hs : SymbolsBelow bound params) (hp : path.Supported bound) : output.path.Supported bound := by
  induction clauses generalizing path index output with
  | nil => cases hg; exact hp
  | cons clause clauses ih =>
    simp only [entryChecks, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hrs, heq⟩ := hg
    cases heq
    have hfirst := clause.clause_supported hf hs (by intro value hv; cases hv) (by intro value hv; cases hv)
    change rest.path.Supported bound
    exact ih hrs ⟨hp, hfirst.2⟩

theorem post_checks_sound
    (hg : postChecks symbols symbol path clauses index = some output)
    (hp : EnvRep model symbols params) (hv : ProductDenotes model symbol value) :
    (group output).Holds model ↔ (path.Holds model → AssertionsHold params (some value) [] clauses) := by
  induction clauses generalizing index output with
  | nil => cases hg; simp [group, Formula.Holds, AssertionsHold]
  | cons clause clauses ih =>
    simp only [postChecks, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hrs, heq⟩ := hg
    cases heq
    have hfirst := (clause.clause_sound (result := some value) hf hp hv .nil).2
    have hrest := ih hrs
    simp only [group_cons, hfirst, hrest]
    constructor
    · rintro ⟨first, rest⟩ hg clause hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact first hg
      · exact rest hg clause hc
    · intro h
      exact ⟨fun hg => h hg _ (.head _), fun hg clause hc => h hg clause (.tail _ hc)⟩

theorem entry_path_input (hg : entryChecks params clauses path index = some output)
    (hp : output.path.Holds model) : path.Holds model := by
  induction clauses generalizing path index output with
  | nil => cases hg; exact hp
  | cons clause clauses ih =>
    simp only [entryChecks, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, _, rest, hrs, heq⟩ := hg
    cases heq
    exact (ih hrs hp).1

end APL.ProductFlow
