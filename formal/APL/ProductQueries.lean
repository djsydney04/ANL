import APL.ProductContractClauses

namespace APL.ProductFlow
open ProductLogic

abbrev CheckGroup := CheckKey × List Check

def insertGroup (check : Check) : List CheckGroup → List CheckGroup
  | [] => [(check.key, [check])]
  | (key, checks) :: groups =>
      if check.key = key then (key, check :: checks) :: groups
      else (key, checks) :: insertGroup check groups

def groupChecks (checks : List Check) : List CheckGroup := checks.foldr insertGroup []

def flattenGroups (groups : List CheckGroup) : List Check := groups.flatMap Prod.snd

theorem insert_group_partition :
    (flattenGroups (insertGroup check groups)).Perm (check :: flattenGroups groups) := by
  induction groups with
  | nil => exact .refl _
  | cons pair groups ih =>
    obtain ⟨key, checks⟩ := pair
    simp only [insertGroup]
    split
    · exact .refl _
    · change (checks ++ flattenGroups (insertGroup check groups)).Perm (check :: (checks ++ flattenGroups groups))
      exact (ih.append_left checks).trans List.perm_middle

theorem exact_named_check_partition : (flattenGroups (groupChecks checks)).Perm checks := by
  induction checks with
  | nil => exact .refl _
  | cons check checks ih => exact insert_group_partition.trans (ih.cons check)

def NamedGroups (groups : List CheckGroup) : Prop :=
  ∀ key checks, (key, checks) ∈ groups → ∀ check ∈ checks, check.key = key

theorem insert_group_named (h : NamedGroups groups) : NamedGroups (insertGroup check groups) := by
  induction groups with
  | nil =>
    intro key checks hg actual ha
    simp only [insertGroup, List.mem_singleton, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    have ha := List.mem_singleton.mp ha
    exact congrArg Check.key ha
  | cons pair groups ih =>
    obtain ⟨key, checks⟩ := pair
    have tail : NamedGroups groups := fun key checks hg => h key checks (.tail _ hg)
    intro actualKey actualChecks hg actual ha
    simp only [insertGroup] at hg
    split at hg
    next heq =>
      rcases List.mem_cons.mp hg with he | hg
      · cases he
        rcases List.mem_cons.mp ha with rfl | ha
        · exact heq
        · exact h key checks (.head _) actual ha
      · exact tail actualKey actualChecks hg actual ha
    next _ =>
      rcases List.mem_cons.mp hg with he | hg
      · cases he; exact h key checks (.head _) actual ha
      · exact ih tail actualKey actualChecks hg actual ha

theorem grouped_checks_named : NamedGroups (groupChecks checks) := by
  induction checks with
  | nil => intro key checks h; cases h
  | cons _ _ ih => exact insert_group_named ih

theorem insert_group_keys : (insertGroup check groups).map Prod.fst =
    if check.key ∈ groups.map Prod.fst then groups.map Prod.fst else groups.map Prod.fst ++ [check.key] := by
  induction groups with
  | nil => simp [insertGroup]
  | cons pair groups ih =>
    obtain ⟨key, checks⟩ := pair
    by_cases heq : check.key = key
    · simp [insertGroup, heq]
    · simp only [insertGroup, ↓reduceIte, List.map_cons, List.mem_cons, heq, false_or]
      rw [ih]
      split <;> rfl

theorem insert_group_keys_distinct (h : (groups.map Prod.fst).Nodup) :
    ((insertGroup check groups).map Prod.fst).Nodup := by
  rw [insert_group_keys]
  split
  · exact h
  next hn =>
    apply List.nodup_append.mpr
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb heq
    have hb := List.mem_singleton.mp hb
    exact hn (hb ▸ heq ▸ ha)

theorem grouped_keys_distinct : ((groupChecks checks).map Prod.fst).Nodup := by
  induction checks with
  | nil => exact .nil
  | cons _ _ ih => exact insert_group_keys_distinct ih

def NamedQueriesHold (model : VCG.Model) (groups : List CheckGroup) : Prop :=
  ∀ pair ∈ groups, (group pair.2).Holds model

theorem named_queries_exact : NamedQueriesHold model (groupChecks checks) ↔ (group checks).Holds model := by
  have flat : NamedQueriesHold model (groupChecks checks) ↔
      (group (flattenGroups (groupChecks checks))).Holds model := by
    simp only [NamedQueriesHold, group_exact, flattenGroups, List.mem_flatMap]
    constructor
    · intro h check ⟨pair, hp, hc⟩; exact h pair hp check hc
    · intro h pair hp check hc; exact h check ⟨pair, hp, hc⟩
  rw [flat]
  have permutation := exact_named_check_partition (checks := checks)
  simp only [group_exact, permutation.mem_iff]

theorem named_query_checks_once :
    (flattenGroups (groupChecks checks)).length = checks.length :=
  exact_named_check_partition.length_eq

end APL.ProductFlow
