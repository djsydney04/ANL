import APL.LoopVCGSoundness

/-! Exact partition of collected checks into mathematical queries. A position
classifier tags each original check once. Correspondence to source occurrence,
clause, query names, production limits, and SMT encoding remains separate. -/

namespace APL.LoopVCG

open VCG

def tagFrom (classify : Nat → Key) : Nat → List Check → List (Key × Check)
  | _, [] => []
  | index, check :: rest => (classify index, check) :: tagFrom classify (index + 1) rest

def queryKeys [DecidableEq Key] : List (Key × Check) → List Key
  | [] => []
  | (key, _) :: rest =>
      let later := queryKeys rest
      if key ∈ later then later else key :: later

def queryChecks [DecidableEq Key] (key : Key) : List (Key × Check) → List Check
  | [] => []
  | (label, check) :: rest =>
      if label = key then check :: queryChecks key rest else queryChecks key rest

def queries [DecidableEq Key] (tagged : List (Key × Check)) : List (Key × Formula) :=
  (queryKeys tagged).map (fun key => (key, group (queryChecks key tagged)))

theorem tag_erases : (tagFrom classify first checks).map Prod.snd = checks := by
  induction checks generalizing first with
  | nil => rfl
  | cons check rest ih => simp only [tagFrom, List.map_cons, ih]

theorem tag_length : (tagFrom classify first checks).length = checks.length := by
  have h := congrArg List.length (tag_erases (classify := classify) (first := first) (checks := checks))
  simpa only [List.length_map] using h

theorem key_mem [DecidableEq Key] {key : Key} {tagged : List (Key × Check)} :
    key ∈ queryKeys tagged ↔ ∃ check, (key, check) ∈ tagged := by
  induction tagged with
  | nil => simp [queryKeys]
  | cons pair rest ih =>
    obtain ⟨label, check⟩ := pair
    simp only [queryKeys]
    split
    next hlabel =>
      rw [ih]
      constructor
      · rintro ⟨value, hv⟩; exact ⟨value, List.mem_cons_of_mem _ hv⟩
      · rintro ⟨value, hv⟩
        rcases List.mem_cons.mp hv with heq | hrest
        · cases heq
          exact ih.mp hlabel
        · exact ⟨value, hrest⟩
    next =>
      simp only [List.mem_cons, Prod.mk.injEq]
      rw [ih]
      constructor
      · rintro (rfl | ⟨value, hv⟩)
        · exact ⟨check, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨value, Or.inr hv⟩
      · rintro ⟨value, (⟨rfl, _⟩ | hv)⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨value, hv⟩

theorem keys_unique [DecidableEq Key] (tagged : List (Key × Check)) : (queryKeys tagged).Nodup := by
  induction tagged with
  | nil => exact .nil
  | cons pair rest ih =>
    obtain ⟨key, check⟩ := pair
    simp only [queryKeys]
    split
    · exact ih
    next h => exact List.nodup_cons.mpr ⟨h, ih⟩

theorem check_mem [DecidableEq Key] {key : Key} {check : Check} {tagged : List (Key × Check)} :
    check ∈ queryChecks key tagged ↔ (key, check) ∈ tagged := by
  induction tagged with
  | nil => simp [queryChecks]
  | cons pair rest ih =>
    obtain ⟨label, first⟩ := pair
    by_cases h : label = key
    · subst label
      simp only [queryChecks, ↓reduceIte, List.mem_cons, Prod.mk.injEq, true_and, ih]
    · simp only [queryChecks, h, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ih]
      constructor
      · exact Or.inr
      · rintro (⟨heq, _⟩ | hr)
        · exact False.elim (h heq.symm)
        · exact hr

theorem partition_exact [DecidableEq Key] {tagged : List (Key × Check)} :
    (∀ key ∈ queryKeys tagged, (group (queryChecks key tagged)).Holds model) ↔
      (group (tagged.map Prod.snd)).Holds model := by
  constructor
  · intro accepted
    apply group_exact.mpr
    intro check hm hp
    obtain ⟨⟨key, original⟩, hmember, heq⟩ := List.mem_map.mp hm
    cases heq
    have hk := key_mem.mpr ⟨original, hmember⟩
    exact group_exact.mp (accepted key hk) original (check_mem.mpr hmember) hp
  · intro accepted key _
    apply group_exact.mpr
    intro check hm hp
    have hmember := check_mem.mp hm
    exact group_exact.mp accepted check (List.mem_map.mpr ⟨(key, check), hmember, rfl⟩) hp

theorem query_list_exact [DecidableEq Key] {tagged : List (Key × Check)} :
    (∀ query ∈ queries tagged, query.2.Holds model) ↔
      (group (tagged.map Prod.snd)).Holds model := by
  rw [← partition_exact]
  simp only [queries, List.forall_mem_map]

theorem tagged_partition_exact [DecidableEq Key] (classify : Nat → Key) :
    (∀ query ∈ queries (tagFrom classify first checks), query.2.Holds model) ↔
      (group checks).Holds model := by
  rw [query_list_exact, tag_erases]

def QueriesValidFrom [DecidableEq Key] (classify : Nat → Key) (first bound : Nat)
    (model : Model) (checks : List Check) : Prop :=
  ∀ extended, AgreeBelow bound model extended →
    ∀ query ∈ queries (tagFrom classify first checks), query.2.Holds extended

theorem validity_partition_exact [DecidableEq Key] {classify : Nat → Key} :
    QueriesValidFrom classify first bound model checks ↔
      LoopVCG.ValidFrom bound model checks := by
  constructor
  · intro h extended ha
    exact (tagged_partition_exact classify).mp (h extended ha)
  · intro h extended ha
    exact (tagged_partition_exact classify).mpr (h extended ha)

theorem analyze_queries_run_sound [DecidableEq Key] {classify : Nat → Key}
    (wf : LocalState.WellTyped (LoopAnnotations.eraseFunctions fs))
    (hg : LoopVCG.analyze fs preconditions height Γ e syms path start = some generated)
    (he : SymbolsBelow start syms) (hp : FormulaBelow start path)
    (henv : EnvRep model syms env) (htyped : LocalState.EnvTyped env Γ)
    (hpath : path.Holds model)
    (hqueries : QueriesValidFrom classify first start model generated.checks) :
    StateVCG.RunSafe (LoopVCG.Covered start model generated)
      (LocalState.run (LoopAnnotations.eraseFunctions fs) budget (.eval e.erase env [])) :=
  LoopVCG.analyze_run_sound wf hg he hp henv htyped hpath
    (validity_partition_exact.mp hqueries)

-- Classification may describe kinds or clause/occurrence identifiers, but a
-- production naming/metadata mapping is a separate bridge. Every concrete check
-- is tagged once here, and grouping retains its original guard and requirement.

end APL.LoopVCG
