import ANL.MemoryInvariant

namespace ANL.Memory

theorem Layout.nil_inv (h : Layout owners resources []) : owners = [] ∧ resources = [] := by
  cases h; exact ⟨rfl, rfl⟩

theorem Layout.pop_plain (h : Layout owners resources (frame :: k)) (plain : frame.Plain) :
    Layout owners resources k := by
  cases h with
  | plain _ h => exact h
  | owner => cases plain
  | callReturn => cases plain

theorem Layout.owner_inv (h : Layout owners resources (.owner binding site :: k)) :
    ∃ tail rest, owners = ⟨binding.ref, site, binding.length⟩ :: tail ∧
      resources = binding :: rest ∧ binding.mode = .owner ∧ Layout tail rest k := by
  cases h with
  | plain bad _ => cases bad
  | owner hm hl => exact ⟨_, _, rfl, rfl, hm, hl⟩

theorem Layout.call_inv (h : Layout owners resources (.callReturn caller loan :: k)) :
    resources = loanResources loan ∧ LoanOption.Valid loan caller.resources ∧ Layout owners caller.resources k := by
  cases h with
  | plain bad _ => cases bad
  | callReturn hv hl => exact ⟨rfl, hv, hl⟩

theorem Layout.live (h : Layout owners resources k) (hb : binding ∈ resources) :
    ∃ shape ∈ owners, shape.ref = binding.ref ∧ shape.length = binding.length := by
  induction h generalizing binding with
  | nil => cases hb
  | plain _ _ ih => exact ih hb
  | owner _ _ ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨shape, hm, hr, hl⟩ := ih hb
        exact ⟨shape, List.mem_cons_of_mem _ hm, hr, hl⟩
  | @callReturn loan owners k caller hv _ ih =>
      cases loan with
      | none => cases hb
      | some loan =>
          have eq : binding = loan.binding := by simpa [loanResources] using hb
          subst binding
          simpa only [Loan.binding] using ih (binding := loan.source) hv.1

theorem Layout.current_distinct (h : Layout owners resources k) (unique : (owners.map Shape.ref).Nodup) :
    (resources.map Binding.ref).Nodup := by
  induction h with
  | nil => simp
  | plain _ _ ih => exact ih unique
  | @owner binding owners resources k site _ hl ih =>
      simp only [List.map_cons, List.nodup_cons] at unique ⊢
      refine ⟨?_, ih unique.2⟩
      intro hm
      obtain ⟨other, hb, hr⟩ := List.mem_map.mp hm
      obtain ⟨shape, hs, he, _⟩ := hl.live hb
      exact unique.1 (List.mem_map.mpr ⟨shape, hs, he.trans hr⟩)
  | callReturn => cases ‹Option Loan› <;> simp [loanResources]

theorem Store.lookup_of_mem {owners : Store} (unique : (owners.map Owner.ref).Nodup)
    (member : owner ∈ owners) : Store.lookup owners owner.ref = some owner := by
  induction owners with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [Store.lookup]
      · have hu := List.nodup_cons.mp unique
        have hn : first.ref ≠ owner.ref := by
          intro he
          exact hu.1 (List.mem_map.mpr ⟨owner, member, he.symm⟩)
        simp [Store.lookup, hn, ih hu.2 member]

theorem Layout.lookup {w : World} (h : Layout (w.owners.map Owner.shape) resources k)
    (hw : w.Valid p) (hb : binding ∈ resources) :
    ∃ owner, w.lookup binding.ref = some owner ∧ owner.length = binding.length := by
  obtain ⟨shape, hm, hr, hl⟩ := h.live hb
  obtain ⟨owner, ho, he⟩ := List.mem_map.mp hm
  subst shape
  change owner.ref = binding.ref at hr
  exact ⟨owner, by rw [← hr]; exact Store.lookup_of_mem hw.unique ho, hl⟩

theorem Layout.close_exists {w : World} (h : Layout (w.owners.map Owner.shape) resources (.owner binding site :: k)) :
    ∃ next, w.close binding.ref site = some next := by
  obtain ⟨tail, rest, ho, _, _, _⟩ := h.owner_inv
  cases hw : w.owners with
  | nil => simp [hw] at ho
  | cons owner owners =>
      simp only [hw, List.map_cons, List.cons.injEq] at ho
      have hr := congrArg Shape.ref ho.1
      have hs := congrArg Shape.site ho.1
      change owner.ref = binding.ref at hr
      change owner.site = site at hs
      exact ⟨_, by simpa only [hr, hs] using w.close_top hw⟩

theorem Layout.closed {w next : World}
    (h : Layout (w.owners.map Owner.shape) resources (.owner binding site :: k))
    (hc : w.close binding.ref site = some next) :
    Layout (next.owners.map Owner.shape) resources.tail k := by
  obtain ⟨tail, rest, ho, hr, _, hl⟩ := h.owner_inv
  obtain ⟨owner, owners, hs, _, _, rfl⟩ := World.close_spec hc
  simp only [hs, List.map_cons, List.cons.injEq] at ho
  simpa [hr, ← ho.2] using hl

theorem allocate_shapes {p : Profile} {w next : World}
    (h : allocate p responses w site n init = (.allocated ref, next)) :
    next.owners.map Owner.shape = ⟨ref, site, n⟩ :: w.owners.map Owner.shape := by
  by_cases hb : p.maxCells < n
  · rw [allocate_target hb] at h; cases h
  · by_cases hz : n = 0
    · subst n; rw [allocate_empty] at h; cases h; rfl
    · have hn : 0 < n := by omega
      have bound : n ≤ p.maxCells := by omega
      cases hr : responses w.nextRequest with
      | refused => rw [allocate_refused hn bound hr] at h; cases h
      | success =>
          rw [allocate_success hn bound hr] at h; cases h
          simp [Owner.shape, Owner.ref, Owner.site, Owner.length, Owner.cells]

theorem allocate_failure_owners {p : Profile} {w next : World}
    (h : allocate p responses w site n init = (result, next))
    (failed : result = .refused ∨ result = .targetRejected) : next.owners = w.owners := by
  by_cases hb : p.maxCells < n
  · rw [allocate_target hb] at h; cases h; rfl
  · by_cases hz : n = 0
    · subst n; rw [allocate_empty] at h; cases h; cases failed <;> contradiction
    · have hn : 0 < n := by omega
      have bound : n ≤ p.maxCells := by omega
      cases hr : responses w.nextRequest with
      | refused => rw [allocate_refused hn bound hr] at h; cases h; rfl
      | success => rw [allocate_success hn bound hr] at h; cases h; cases failed <;> contradiction

theorem allocate_eq_valid {p : Profile} {w next : World}
    (hw : w.Valid p) (ha : allocate p responses w site n init = (result, next)) : next.Valid p := by
  have valid := allocate_valid (responses := responses) (site := site) (n := n) (initial := init) hw
  simpa only [ha] using valid

theorem allocate_eq_live_frame {p : Profile} {w next : World}
    (hw : w.Valid p) (hl : w.lookup ref = some owner)
    (ha : allocate p responses w site n init = (result, next)) : next.lookup ref = some owner := by
  have frame := allocate_live_frame (responses := responses) (site := site) (n := n) (initial := init) hw hl
  simpa only [ha] using frame

theorem resource_lookup {i : Nat} (h : (resourceModes resources)[i]? = some mode) :
    ∃ binding : Binding, resources[i]? = some binding ∧ binding.mode = mode := by
  simpa only [resourceModes, List.getElem?_map, Option.map_eq_some_iff] using h

theorem loan_resource_modes (loan : Option Loan) : resourceModes (loanResources loan) = viewContext (loanMode loan) := by
  cases loan <;> rfl

theorem State.Typed.world (h : State.Typed p s t) : s.world.Valid p.profile := by cases h; assumption
theorem State.Typed.layout (h : State.Typed p s t) : Layout (s.world.owners.map Owner.shape) s.current.resources s.kont := by
  cases h; assumption

theorem State.Typed.distinct (h : State.Typed p s t) : (s.accessible.map Binding.ref).Nodup := by
  unfold State.accessible
  split
  · simp
  · apply h.layout.current_distinct
    simpa [List.map_map, Function.comp_def, Owner.shape] using h.world.unique

theorem State.Typed.lookup (h : State.Typed p s t) (hb : binding ∈ s.current.resources) :
    ∃ owner, s.world.lookup binding.ref = some owner ∧ owner.length = binding.length :=
  h.layout.lookup h.world hb

end ANL.Memory
