import ANL.WordsSimulationKontInvariant

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

def SiteList (offset : Nat) (ids sites : List Nat) : Prop :=
  sites.Nodup ∧ ∀ site ∈ sites, site + offset ∉ ids

theorem SiteList.append_left (h : SiteList offset ids (left ++ right)) : SiteList offset ids left :=
  ⟨(List.nodup_append.mp h.1).1, fun site hs => h.2 site (List.mem_append_left _ hs)⟩

theorem SiteList.append_right (h : SiteList offset ids (left ++ right)) : SiteList offset ids right :=
  ⟨(List.nodup_append.mp h.1).2.1, fun site hs => h.2 site (List.mem_append_right _ hs)⟩

theorem SiteList.tail (h : SiteList offset ids (head :: rest)) : SiteList offset ids rest :=
  ⟨(List.nodup_cons.mp h.1).2, fun site hs => h.2 site (.tail _ hs)⟩

theorem SiteList.flatMap_member {items : List α} {f : α → List Nat}
    (h : SiteList offset ids (items.flatMap f)) (hm : item ∈ items) :
    SiteList offset ids (f item) := by
  induction items with
  | nil => simp at hm
  | cons first rest ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h.append_left
      · exact ih h.append_right hm

theorem SiteList.flatMap_tail {f : α → List Nat}
    (h : SiteList offset ids ((head :: rest).flatMap f)) : SiteList offset ids (rest.flatMap f) :=
  h.append_right

theorem SiteList.extend (h : SiteList offset ids sites) (fresh : owner ∉ sites) :
    SiteList offset ((owner + offset) :: ids) sites := by
  refine ⟨h.1, ?_⟩
  intro site hs membership
  rcases List.mem_cons.mp membership with eq | membership
  · exact fresh ((Nat.add_right_cancel eq) ▸ hs)
  · exact h.2 site hs membership

theorem ScopedSites.heap_parts {length initializer success failure : Term}
    (h : ScopedSites offset ids (.heap ty site length initializer success failure)) :
    site + offset ∉ ids ∧ ScopedSites offset ids length ∧ ScopedSites offset ids initializer ∧
      ScopedSites offset ((site + offset) :: ids) success ∧ ScopedSites offset ids failure := by
  simp only [ScopedSites, Term.heapSites] at h
  change SiteList offset ids (site :: (length.heapSites ++ initializer.heapSites ++
    success.heapSites ++ failure.heapSites)) at h
  have rest := h.tail
  refine ⟨h.2 site (.head _), rest.append_left.append_left.append_left,
    rest.append_left.append_left.append_right, ?_, rest.append_right⟩
  apply rest.append_left.append_right.extend
  intro membership
  apply (List.nodup_cons.mp h.1).1
  simp only [List.mem_append]
  exact Or.inl (Or.inr membership)

theorem ScopedSites.of_canonical {e : Term} (sites : e.CanonicalSites) (view : Option ViewMode) :
    ScopedSites (viewOffset view) (match view with | none => [] | some _ => [0]) e := by
  refine ⟨?_, ?_⟩
  · rw [sites]
    exact List.nodup_range
  · cases view <;> simp [viewOffset]

theorem function_scoped_sites {fn : Function} (wellFormed : fn.WellFormed sigs) :
    ScopedSites (viewOffset fn.view) (match fn.view with | none => [] | some _ => [0]) fn.body :=
  ScopedSites.of_canonical wellFormed.sites fn.view

end ANL.Words.Simulation
