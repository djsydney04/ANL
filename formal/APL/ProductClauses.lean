import APL.ProductSpec

namespace APL.ProductAnnotations
open ProductLogic
open VCG (Model)

structure Clause where
  defined : Formula
  truth : Formula

def booleanClause (input : Instantiated) : Option Clause :=
  match input.value with
  | .scalar value =>
      if value.type = .bool then
        some ⟨.and input.defined (.boolean value.term), .and input.defined (.holds value.term)⟩
      else none
  | .tuple _ => none

def Spec.clause (params : List SymValue) (result : Option SymValue) (locals : List SymValue)
    (spec : Spec) : Option Clause := do
  let instantiated ← spec.instantiate params result locals
  booleanClause instantiated

theorem boolean_clause_sound (hg : booleanClause input = some clause)
    (h : input.Agrees model semantic) :
    (clause.defined.Holds model ↔ ∃ test, semantic = some (.scalar (.bool test))) ∧
    (clause.truth.Holds model ↔ semantic = some (.scalar (.bool true))) := by
  cases input with
  | mk symbol defined =>
    cases symbol with
    | tuple fields => simp [booleanClause] at hg
    | scalar symbol =>
      simp only [booleanClause] at hg
      split at hg
      next ht =>
        cases hg
        constructor
        · constructor
          · rintro ⟨hd, test, htest⟩
            obtain ⟨value, hv, hr⟩ := h.1 hd
            have he := hr.eval
            simp only [SymValue.eval, htest, Option.map_some, Option.some.injEq] at he
            subst value
            exact ⟨test, hv⟩
          · rintro ⟨test, htest⟩
            obtain ⟨hd, hr⟩ := h.2 _ htest
            cases hr with
            | scalar hr => exact ⟨hd, test, hr.2⟩
        · constructor
          · rintro ⟨hd, htest⟩
            change symbol.term.eval model = some (.bool true) at htest
            obtain ⟨value, hv, hr⟩ := h.1 hd
            have he := hr.eval
            simp only [SymValue.eval, htest, Option.map_some, Option.some.injEq] at he
            subst value
            exact hv
          · intro htest
            obtain ⟨hd, hr⟩ := h.2 _ htest
            cases hr with
            | scalar hr => exact ⟨hd, hr.2⟩
      · contradiction

theorem Spec.clause_sound {spec : Spec} {result : Option MValue} {clause : Clause}
    (hg : spec.clause symbolicParams symbolicResult symbolicLocals = some clause)
    (hp : EnvRep model symbolicParams params) (hr : ResultRep model symbolicResult result)
    (hl : EnvRep model symbolicLocals locals) :
    (clause.defined.Holds model ↔ ∃ test, spec.eval params result locals = some (.scalar (.bool test))) ∧
    (clause.truth.Holds model ↔ spec.eval params result locals = some (.scalar (.bool true))) := by
  simp only [Spec.clause, bind, Option.bind_eq_some_iff] at hg
  obtain ⟨instantiated, hi, hc⟩ := hg
  exact boolean_clause_sound hc (spec.instantiate_sound hi hp hr hl)

def RequiresDefined (params : List MValue) : List Spec → Prop
  | [] => True
  | clause :: clauses => (∃ test, clause.eval params none [] = some (.scalar (.bool test))) ∧
      (clause.eval params none [] = some (.scalar (.bool true)) → RequiresDefined params clauses)

def RequiresHold (params : List MValue) : List Spec → Prop
  | [] => True
  | clause :: clauses => clause.eval params none [] = some (.scalar (.bool true)) ∧ RequiresHold params clauses

def requiresVC (params : List SymValue) : List Spec → Option Clause
  | [] => some ⟨.truth true, .truth true⟩
  | clause :: clauses => do
      let first ← clause.clause params none []
      let rest ← requiresVC params clauses
      return ⟨.and first.defined (.imp first.truth rest.defined), .and first.truth rest.truth⟩

theorem requires_vc_sound (hg : requiresVC symbols clauses = some output)
    (hp : EnvRep model symbols params) :
    (output.defined.Holds model ↔ RequiresDefined params clauses) ∧
    (output.truth.Holds model ↔ RequiresHold params clauses) := by
  induction clauses generalizing output with
  | nil => cases hg; simp [Formula.Holds, RequiresDefined, RequiresHold]
  | cons clause clauses ih =>
    simp only [requiresVC, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hr, he⟩ := hg
    cases he
    have hfirst := clause.clause_sound (result := none) hf hp (by trivial) .nil
    have hrest := ih hr
    simp only [Formula.Holds, RequiresDefined, RequiresHold, hfirst.1, hfirst.2, hrest.1, hrest.2]
    trivial

def AssertionsHold (params : List MValue) (result : Option MValue) (locals : List MValue)
    (clauses : List Spec) : Prop :=
  ∀ clause ∈ clauses, clause.eval params result locals = some (.scalar (.bool true))

def assertionsVC (params : List SymValue) (result : Option SymValue) (locals : List SymValue) :
    List Spec → Option (List Clause)
  | [] => some []
  | clause :: clauses => do
      let first ← clause.clause params result locals
      let rest ← assertionsVC params result locals clauses
      return first :: rest

def clauseConjunction : List Clause → Formula
  | [] => .truth true
  | clause :: clauses => .and clause.truth (clauseConjunction clauses)

theorem assertions_vc_sound (hg : assertionsVC symbolicParams symbolicResult symbolicLocals clauses = some outputs)
    (hp : EnvRep model symbolicParams params) (hr : ResultRep model symbolicResult result)
    (hl : EnvRep model symbolicLocals locals) :
    (clauseConjunction outputs).Holds model ↔ AssertionsHold params result locals clauses := by
  induction clauses generalizing outputs with
  | nil => cases hg; simp [clauseConjunction, Formula.Holds, AssertionsHold]
  | cons clause clauses ih =>
    simp only [assertionsVC, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, hf, rest, hrest, he⟩ := hg
    cases he
    have hc := (clause.clause_sound hf hp hr hl).2
    simp only [clauseConjunction, Formula.Holds, hc, ih hrest, AssertionsHold, List.mem_cons]
    constructor
    · rintro ⟨hc, hrs⟩ member hm
      rcases hm with rfl | hm
      · exact hc
      · exact hrs member hm
    · intro h
      exact ⟨h clause (.inl rfl), fun member hm => h member (.inr hm)⟩

end APL.ProductAnnotations
