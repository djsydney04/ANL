import APL.ProductContracts

namespace APL.ProductFlow
open ProductLogic

def namedGroups (checks : List Check) : List CheckGroup :=
  let groups := groupChecks checks
  if CheckKey.body ∈ groups.map Prod.fst then groups else groups ++ [(.body, [])]

theorem named_groups_partition : (flattenGroups (namedGroups checks)).Perm checks := by
  simp only [namedGroups]
  split
  · exact exact_named_check_partition
  · simpa [flattenGroups, List.flatMap_append] using exact_named_check_partition (checks := checks)

theorem named_groups_keys_distinct : ((namedGroups checks).map Prod.fst).Nodup := by
  simp only [namedGroups]
  split
  · exact grouped_keys_distinct
  next hn =>
    simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨grouped_keys_distinct, by simp, ?_⟩
    intro a ha b hb heq
    exact hn (List.mem_singleton.mp hb ▸ heq ▸ ha)

theorem named_groups_named : NamedGroups (namedGroups checks) := by
  simp only [namedGroups]
  split
  · exact grouped_checks_named
  · intro key groupChecks hg check hc
    rcases List.mem_append.mp hg with hg | hg
    · exact grouped_checks_named key groupChecks hg check hc
    · have heq := List.mem_singleton.mp hg
      cases heq
      cases hc

theorem named_groups_exact : NamedQueriesHold model (namedGroups checks) ↔ (group checks).Holds model := by
  simp only [namedGroups]
  split
  · exact named_queries_exact
  · constructor
    · intro h
      apply named_queries_exact.mp
      intro pair hp
      exact h pair (List.mem_append_left _ hp)
    · intro h pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact named_queries_exact.mpr h pair hp
      · have heq := List.mem_singleton.mp hp
        cases heq
        trivial

inductive QueryKind where
  | safety (key : CheckKey)
  | reachable
  deriving DecidableEq, Repr

structure Query where
  kind : QueryKind
  assertion : Formula
  expectedSat : Bool
  deriving Repr

def Query.Accepted (query : Query) : Prop :=
  if query.expectedSat then ∃ model, query.assertion.Holds model
  else ∀ model, ¬ query.assertion.Holds model

def contractQueries (output : ContractOutput) : List Query :=
  ⟨.reachable, output.entry.path, true⟩ :: (namedGroups output.checks).map
    (fun pair => ⟨.safety pair.1, .not (group pair.2), false⟩)

def QueriesAccepted (queries : List Query) : Prop := ∀ query ∈ queries, query.Accepted

theorem contract_queries_exact : QueriesAccepted (contractQueries output) ↔ output.Accepted := by
  constructor
  · intro accepted
    refine ⟨?_, accepted _ (.head _)⟩
    intro model
    apply named_queries_exact.mpr
    apply named_groups_exact.mp
    intro pair hp
    have valid := accepted ⟨.safety pair.1, .not (group pair.2), false⟩
      (.tail _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    exact Classical.byContradiction (valid model)
  · rintro ⟨valid, reachable⟩ query hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact reachable
    · obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hq
      intro model hnot
      exact hnot (named_groups_exact.mpr (named_queries_exact.mp (valid model)) pair hp)

theorem entry_check_keys (hg : entryChecks params clauses path index = some output) :
    output.checks.map Check.key = (List.range' index clauses.length).map CheckKey.precondition := by
  induction clauses generalizing path index output with
  | nil => cases hg; rfl
  | cons clause clauses ih =>
    simp only [entryChecks, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, _, rest, hr, heq⟩ := hg
    cases heq
    simpa [List.range'_succ] using congrArg (CheckKey.precondition index :: ·) (ih hr)

theorem post_check_keys (hg : postChecks params value path clauses index = some output) :
    output.map Check.key = (List.range' index clauses.length).map CheckKey.postcondition := by
  induction clauses generalizing index output with
  | nil => cases hg; rfl
  | cons clause clauses ih =>
    simp only [postChecks, bind, Option.bind_eq_some_iff, Option.pure_def] at hg
    obtain ⟨first, _, rest, hr, heq⟩ := hg
    cases heq
    simpa [List.range'_succ] using congrArg (CheckKey.postcondition index :: ·) (ih hr)

theorem invariant_check_keys :
    (invariantChecks site isPreservation path clauses).map Check.key =
      (List.range' 0 clauses.length).map (CheckKey.invariant site isPreservation) := by
  simp only [invariantChecks, List.map_map, Function.comp_def]
  rw [← List.zipIdx_map_snd (l := clauses) 0, List.map_map]
  rfl

theorem contract_queries_sound
    (wf : ProductAnnotations.WellTyped fs)
    (hg : generateContract fs height fn = some output)
    (ht : params.map FlatProducts.Val.type = fn.params)
    (hp : ProductAnnotations.RequiresHold (params.map embedValue) fn.requires)
    (accepted : QueriesAccepted (contractQueries output)) :
    FlatProducts.LoopVerification.RunSafe
      (fun value final => Covered (reservedCount fn.params) (ProductEntry.parameterModel params) output.body value final ∧
        ProductAnnotations.AssertionsHold (params.map embedValue) (some (embedValue value)) [] fn.ensures)
      (FlatProducts.run (ProductAnnotations.eraseFunctions fs) budget (.eval fn.body.erase params.reverse [])) :=
  contract_accepted_run wf hg ht hp (contract_queries_exact.mp accepted)

end APL.ProductFlow
