import ANL.MemoryCore

namespace ANL.Memory

structure Site where
  function : Nat
  heap : Nat
  deriving DecidableEq, Repr

inductive Ref where
  | positive (request : Nat)
  | empty (activation : Nat)
  deriving DecidableEq, Repr

inductive Response where
  | success | refused
  deriving DecidableEq, Repr

abbrev Responses := Nat → Response

inductive Event where
  | request (ordinal : Nat) (site : Site) (length : Nat) (response : Response)
  | release (ordinal : Nat) (site : Site)
  | emptyOpen (ordinal : Nat) (site : Site)
  | emptyClose (ordinal : Nat) (site : Site)
  deriving DecidableEq, Repr

def Ref.closeEvent (r : Ref) (site : Site) : Event :=
  match r with
  | .positive ordinal => .release ordinal site
  | .empty ordinal => .emptyClose ordinal site

inductive Owner where
  | positive (request : Nat) (site : Site) (cells : List APL.I64)
  | empty (activation : Nat) (site : Site)
  deriving DecidableEq, Repr

def Owner.ref : Owner → Ref
  | .positive ordinal _ _ => .positive ordinal
  | .empty ordinal _ => .empty ordinal

def Owner.site : Owner → Site
  | .positive _ site _ | .empty _ site => site

def Owner.cells : Owner → List APL.I64
  | .positive _ _ cells => cells
  | .empty _ _ => []

def Owner.length (o : Owner) : Nat := o.cells.length

structure Shape where
  ref : Ref
  site : Site
  length : Nat
  deriving DecidableEq, Repr

def Owner.shape (o : Owner) : Shape := ⟨o.ref, o.site, o.length⟩

def Owner.closeEvent : Owner → Event
  | .positive ordinal site _ => .release ordinal site
  | .empty ordinal site => .emptyClose ordinal site

def Ref.Below (nextRequest nextEmpty : Nat) : Ref → Prop
  | .positive n => n < nextRequest
  | .empty n => n < nextEmpty

def Shape.Valid (p : Profile) (s : Shape) : Prop :=
  match s.ref with
  | .positive _ => 0 < s.length ∧ s.length ≤ p.maxCells
  | .empty _ => s.length = 0

/-- History records identities, sites and lengths, never mutable cell contents. -/
inductive History (p : Profile) : Nat → Nat → List Shape → List Event → Prop where
  | initial : History p 0 0 [] []
  | success : History p nr ne owners trace → 0 < n → n ≤ p.maxCells →
      History p (nr + 1) ne (⟨.positive nr, site, n⟩ :: owners)
        (trace ++ [.request nr site n .success])
  | refused : History p nr ne owners trace → 0 < n → n ≤ p.maxCells →
      History p (nr + 1) ne owners (trace ++ [.request nr site n .refused])
  | emptyOpen : History p nr ne owners trace →
      History p nr (ne + 1) (⟨.empty ne, site, 0⟩ :: owners) (trace ++ [.emptyOpen ne site])
  | release : History p nr ne (⟨.positive ordinal, site, n⟩ :: owners) trace →
      History p nr ne owners (trace ++ [.release ordinal site])
  | emptyClose : History p nr ne (⟨.empty ordinal, site, 0⟩ :: owners) trace →
      History p nr ne owners (trace ++ [.emptyClose ordinal site])

abbrev Store := List Owner

def Store.lookup (owners : Store) (r : Ref) : Option Owner :=
  match owners with
  | [] => none
  | owner :: rest => if owner.ref = r then some owner else Store.lookup rest r

def Owner.write (owner : Owner) (index : Nat) (value : APL.I64) : Option Owner :=
  match owner with
  | .empty _ _ => none
  | .positive ordinal site cells =>
      if index < cells.length then some (.positive ordinal site (cells.set index value)) else none

def Store.write (owners : Store) (r : Ref) (index : Nat) (value : APL.I64) : Option Store :=
  match owners with
  | [] => none
  | owner :: rest =>
      if owner.ref = r then (owner.write index value).map (· :: rest)
      else (Store.write rest r index value).map (owner :: ·)

structure World where
  /-- Live lexical owners, newest first; views are separate machine descriptors. -/
  owners : Store
  nextRequest : Nat
  nextEmpty : Nat
  revTrace : List Event
  deriving DecidableEq, Repr

def World.initial : World := ⟨[], 0, 0, []⟩

/-- Ordered export/proof projection; runners should not recompute it at every transition. -/
def World.trace (w : World) : List Event := w.revTrace.reverse

structure World.Valid (p : Profile) (w : World) : Prop where
  profile : p.Admissible
  history : History p w.nextRequest w.nextEmpty (w.owners.map Owner.shape) w.trace

def World.lookup (w : World) (r : Ref) : Option Owner := Store.lookup w.owners r
def World.length (w : World) (r : Ref) : Option Nat := (w.lookup r).map Owner.length
def World.read (w : World) (r : Ref) (index : Nat) : Option APL.I64 :=
  (w.lookup r).bind fun owner => owner.cells[index]?

def World.write (w : World) (r : Ref) (index : Nat) (value : APL.I64) : Option World :=
  (Store.write w.owners r index value).map fun owners => { w with owners }

/-- Normal lexical closure retires only the matching top owner. Traps do not call this. -/
def World.close (w : World) (r : Ref) (site : Site) : Option World :=
  match w.owners with
  | [] => none
  | owner :: rest =>
      if owner.ref = r ∧ owner.site = site then
        some { w with owners := rest, revTrace := owner.closeEvent :: w.revTrace }
      else none

inductive Allocation where
  | allocated (ref : Ref)
  | refused
  | targetRejected
  deriving DecidableEq, Repr

/-- Uses a captured initializer; resource-limited runners must preflight before this call. -/
def allocate (p : Profile) (responses : Responses) (w : World) (site : Site)
    (length : Nat) (initial : APL.I64) : Allocation × World :=
  if p.maxCells < length then (.targetRejected, w)
  else if length = 0 then
    (.allocated (.empty w.nextEmpty),
      ⟨Owner.empty w.nextEmpty site :: w.owners, w.nextRequest, w.nextEmpty + 1,
        .emptyOpen w.nextEmpty site :: w.revTrace⟩)
  else
    let response := responses w.nextRequest
    let events := .request w.nextRequest site length response :: w.revTrace
    match response with
    | .refused => (.refused, ⟨w.owners, w.nextRequest + 1, w.nextEmpty, events⟩)
    | .success =>
      (.allocated (.positive w.nextRequest),
        ⟨Owner.positive w.nextRequest site (List.replicate length initial) :: w.owners,
          w.nextRequest + 1, w.nextEmpty, events⟩)

def checkedIndex (length : Nat) (index : Int) : Option Nat :=
  if 0 ≤ index ∧ index < (length : Int) then some index.toNat else none

theorem checkedIndex_iff : checkedIndex length index = some n ↔
    0 ≤ index ∧ index < (length : Int) ∧ index.toNat = n := by
  unfold checkedIndex
  split
  next h => simp [h.1, h.2]
  next h =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hn, hl, _⟩
    exact h ⟨hn, hl⟩

theorem checkedIndex_bounds (h : checkedIndex length index = some n) :
    n < length ∧ (n : Int) = index := by
  obtain ⟨hn, hl, rfl⟩ := checkedIndex_iff.mp h
  exact ⟨(Int.toNat_lt hn).mpr hl, Int.toNat_of_nonneg hn⟩

theorem checkedIndex_exists {length : Nat} {index : Int} (hn : 0 ≤ index) (hl : index < (length : Int)) :
    checkedIndex length index = some index.toNat := checkedIndex_iff.mpr ⟨hn, hl, rfl⟩

theorem Ref.Below.mono {r : Ref} (h : r.Below nr ne) (hr : nr ≤ nr') (he : ne ≤ ne') :
    r.Below nr' ne' := by
  cases r <;> simp only [Ref.Below] at * <;> omega

theorem History.refs_below (h : History p nr ne owners trace) :
    ∀ owner ∈ owners, owner.ref.Below nr ne := by
  induction h with
  | initial => simp
  | success _ _ _ ih =>
      intro owner hm
      rcases List.mem_cons.mp hm with rfl | hm
      · simp [Ref.Below]
      · exact (ih owner hm).mono (by omega) (by omega)
  | refused _ _ _ ih =>
      intro owner hm
      exact (ih owner hm).mono (by omega) (by omega)
  | emptyOpen _ ih =>
      intro owner hm
      rcases List.mem_cons.mp hm with rfl | hm
      · simp [Ref.Below]
      · exact (ih owner hm).mono (by omega) (by omega)
  | release _ ih =>
      intro owner hm
      exact ih owner (List.mem_cons_of_mem _ hm)
  | emptyClose _ ih =>
      intro owner hm
      exact ih owner (List.mem_cons_of_mem _ hm)

theorem History.shapes_valid (h : History p nr ne owners trace) :
    ∀ owner ∈ owners, owner.Valid p := by
  induction h with
  | initial => simp
  | success _ hp hb ih =>
      intro owner hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨hp, hb⟩
      · exact ih owner hm
  | refused _ _ _ ih => exact ih
  | emptyOpen _ ih =>
      intro owner hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact ih owner hm
  | release _ ih =>
      intro owner hm
      exact ih owner (List.mem_cons_of_mem _ hm)
  | emptyClose _ ih =>
      intro owner hm
      exact ih owner (List.mem_cons_of_mem _ hm)

theorem History.fresh_positive (h : History p nr ne owners trace) :
    Ref.positive nr ∉ owners.map Shape.ref := by
  intro hm
  obtain ⟨owner, ho, hr⟩ := List.mem_map.mp hm
  have hb := h.refs_below owner ho
  rw [hr] at hb
  exact Nat.lt_irrefl _ hb

theorem History.fresh_empty (h : History p nr ne owners trace) :
    Ref.empty ne ∉ owners.map Shape.ref := by
  intro hm
  obtain ⟨owner, ho, hr⟩ := List.mem_map.mp hm
  have hb := h.refs_below owner ho
  rw [hr] at hb
  exact Nat.lt_irrefl _ hb

theorem History.unique (h : History p nr ne owners trace) : (owners.map Shape.ref).Nodup := by
  induction h with
  | initial => simp
  | success h _ _ ih => exact List.nodup_cons.mpr ⟨h.fresh_positive, ih⟩
  | refused _ _ _ ih => exact ih
  | emptyOpen h ih => exact List.nodup_cons.mpr ⟨h.fresh_empty, ih⟩
  | release _ ih => exact (List.nodup_cons.mp ih).2
  | emptyClose _ ih => exact (List.nodup_cons.mp ih).2

theorem Store.lookup_none_iff {owners : Store} {r : Ref} :
    Store.lookup owners r = none ↔ r ∉ owners.map Owner.ref := by
  induction owners with
  | nil => simp [Store.lookup]
  | cons owner rest ih =>
      by_cases h : owner.ref = r
      · simp [Store.lookup, h]
      · have hr := Ne.symm h
        simp [Store.lookup, h, hr, ih]

theorem Store.lookup_mem {owners : Store} {r : Ref} {owner : Owner}
    (h : Store.lookup owners r = some owner) : owner ∈ owners ∧ owner.ref = r := by
  induction owners with
  | nil => simp [Store.lookup] at h
  | cons first rest ih =>
      simp only [Store.lookup] at h
      split at h
      next he => cases h; exact ⟨List.mem_cons_self, he⟩
      next _ =>
        obtain ⟨hm, hr⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hm, hr⟩

theorem Owner.write_spec {owner next : Owner} (h : owner.write index value = some next) :
    ∃ ordinal site cells, owner = .positive ordinal site cells ∧ index < cells.length ∧
      next = .positive ordinal site (cells.set index value) := by
  cases owner with
  | empty ordinal site => simp [Owner.write] at h
  | positive ordinal site cells =>
      simp only [Owner.write] at h
      split at h
      next hl => exact ⟨ordinal, site, cells, rfl, hl, (Option.some.inj h).symm⟩
      next _ => contradiction

theorem Owner.write_shape {owner next : Owner} (h : owner.write index value = some next) :
    next.shape = owner.shape := by
  obtain ⟨ordinal, site, cells, rfl, _, rfl⟩ := Owner.write_spec h
  simp [Owner.shape, Owner.ref, Owner.site, Owner.length, Owner.cells]

theorem Owner.write_ref {owner next : Owner} (h : owner.write index value = some next) :
    next.ref = owner.ref := congrArg Shape.ref (Owner.write_shape h)

theorem Owner.write_same {owner next : Owner} (h : owner.write index value = some next) :
    next.cells[index]? = some value := by
  obtain ⟨ordinal, site, cells, rfl, hl, rfl⟩ := Owner.write_spec h
  exact List.getElem?_set_self hl

theorem Owner.write_other {owner next : Owner} (h : owner.write index value = some next)
    (different : index ≠ other) : next.cells[other]? = owner.cells[other]? := by
  obtain ⟨ordinal, site, cells, rfl, _, rfl⟩ := Owner.write_spec h
  exact List.getElem?_set_ne different

theorem Owner.write_exists {owner : Owner} (h : index < owner.length) :
    ∃ next, owner.write index value = some next := by
  cases owner with
  | empty ordinal site => simp [Owner.length, Owner.cells] at h
  | positive ordinal site cells =>
      exact ⟨.positive ordinal site (cells.set index value), by simpa [Owner.write] using
        (show index < cells.length from h)⟩

theorem Store.write_shapes {owners next : Store} (h : Store.write owners r index value = some next) :
    next.map Owner.shape = owners.map Owner.shape := by
  induction owners generalizing next with
  | nil => simp [Store.write] at h
  | cons owner rest ih =>
      simp only [Store.write] at h
      split at h
      next _ =>
        obtain ⟨updated, hu, rfl⟩ := Option.map_eq_some_iff.mp h
        simp [Owner.write_shape hu]
      next _ =>
        obtain ⟨updated, hu, rfl⟩ := Option.map_eq_some_iff.mp h
        simp [ih hu]

theorem Store.write_target {owners next : Store} (h : Store.write owners r index value = some next) :
    ∃ before after, Store.lookup owners r = some before ∧ before.write index value = some after ∧
      Store.lookup next r = some after := by
  induction owners generalizing next with
  | nil => simp [Store.write] at h
  | cons owner rest ih =>
      simp only [Store.write] at h
      split at h
      next he =>
        obtain ⟨updated, hu, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨owner, updated, by simp [Store.lookup, he], hu,
          by simp [Store.lookup, Owner.write_ref hu, he]⟩
      next he =>
        obtain ⟨updated, hu, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨before, after, hb, hw, ha⟩ := ih hu
        exact ⟨before, after, by simp [Store.lookup, he, hb], hw, by simp [Store.lookup, he, ha]⟩

theorem Store.write_other {owners next : Store} (h : Store.write owners r index value = some next)
    (different : other ≠ r) : Store.lookup next other = Store.lookup owners other := by
  induction owners generalizing next with
  | nil => simp [Store.write] at h
  | cons owner rest ih =>
      simp only [Store.write] at h
      split at h
      next he =>
        obtain ⟨updated, hu, rfl⟩ := Option.map_eq_some_iff.mp h
        have hn : owner.ref ≠ other := by rw [he]; exact Ne.symm different
        simp [Store.lookup, Owner.write_ref hu, hn]
      next _ =>
        obtain ⟨updated, hu, rfl⟩ := Option.map_eq_some_iff.mp h
        simp [Store.lookup, ih hu]

theorem Store.write_exists {owners : Store} {owner : Owner}
    (h : Store.lookup owners r = some owner) (hi : index < owner.length) :
    ∃ next, Store.write owners r index value = some next := by
  induction owners with
  | nil => simp [Store.lookup] at h
  | cons first rest ih =>
      simp only [Store.lookup] at h
      split at h
      next he =>
        cases h
        obtain ⟨next, hn⟩ := Owner.write_exists hi (value := value)
        exact ⟨next :: rest, by simp [Store.write, he, hn]⟩
      next he =>
        obtain ⟨next, hn⟩ := ih h
        exact ⟨first :: next, by simp [Store.write, he, hn]⟩

variable {p : Profile} {w next : World} {r : Ref} {owner : Owner} {index : Nat} {value : APL.I64}

theorem World.initial_valid (hp : p.Admissible) : World.initial.Valid p := ⟨hp, .initial⟩

theorem World.Valid.unique (h : w.Valid p) : (w.owners.map Owner.ref).Nodup := by
  simpa [List.map_map, Function.comp_def, Owner.shape] using h.history.unique

theorem World.Valid.fresh_positive (h : w.Valid p) : w.lookup (.positive w.nextRequest) = none := by
  apply Store.lookup_none_iff.mpr
  simpa [List.map_map, Owner.shape] using h.history.fresh_positive

theorem World.Valid.fresh_empty (h : w.Valid p) : w.lookup (.empty w.nextEmpty) = none := by
  apply Store.lookup_none_iff.mpr
  simpa [List.map_map, Owner.shape] using h.history.fresh_empty

theorem World.Valid.lookup_shape (h : w.Valid p) (hl : w.lookup r = some owner) : owner.shape.Valid p := by
  have hm := (Store.lookup_mem hl).1
  exact h.history.shapes_valid owner.shape (List.mem_map.mpr ⟨owner, hm, rfl⟩)

theorem World.Valid.lookup_below (h : w.Valid p) (hl : w.lookup r = some owner) :
    r.Below w.nextRequest w.nextEmpty := by
  obtain ⟨hm, hr⟩ := Store.lookup_mem hl
  have hb := h.history.refs_below owner.shape (List.mem_map.mpr ⟨owner, hm, rfl⟩)
  simpa [Owner.shape, hr] using hb

theorem Profile.eligible_bytes_size {p : Profile} (h : n ≤ p.maxCells) : n * 8 ≤ p.sizeMax :=
  (Nat.le_div_iff_mul_le (by decide)).mp (Nat.le_trans h p.maxCells_le_size)

theorem Profile.eligible_bytes_ptrdiff {p : Profile} (h : n ≤ p.maxCells) : n * 8 ≤ p.ptrdiffMax :=
  (Nat.le_div_iff_mul_le (by decide)).mp (Nat.le_trans h p.maxCells_le_ptrdiff)

theorem Profile.eligible_in_range {p : Profile} (h : n ≤ p.maxCells) : APL.InRange (n : Int) := by
  have hb := Nat.le_trans h p.maxCells_le_i64
  change n ≤ 9223372036854775807 at hb
  simp only [APL.InRange, APL.minI64, APL.maxI64]
  omega

theorem World.Valid.lookup_length (h : w.Valid p) (hl : w.lookup r = some owner) :
    owner.length ≤ p.maxCells := by
  have hv := h.lookup_shape hl
  cases owner with
  | empty ordinal site => simp [Owner.length, Owner.cells]
  | positive ordinal site cells => exact hv.2

theorem World.Valid.lookup_length_in_range (h : w.Valid p) (hl : w.lookup r = some owner) :
    APL.InRange (owner.length : Int) := Profile.eligible_in_range (h.lookup_length hl)

theorem World.write_valid (hw : w.Valid p) (h : w.write r index value = some next) : next.Valid p := by
  simp only [World.write, Option.map_eq_some_iff] at h
  obtain ⟨owners, ho, rfl⟩ := h
  exact ⟨hw.profile, by simpa [World.trace, Store.write_shapes ho] using hw.history⟩

theorem World.write_same (h : w.write r index value = some next) : next.read r index = some value := by
  simp only [World.write, Option.map_eq_some_iff] at h
  obtain ⟨owners, ho, rfl⟩ := h
  obtain ⟨before, after, _, ha, hl⟩ := Store.write_target ho
  simp [World.read, World.lookup, hl, Owner.write_same ha]

theorem World.write_other_ref (h : w.write r index value = some next) (different : other ≠ r) :
    next.lookup other = w.lookup other := by
  simp only [World.write, Option.map_eq_some_iff] at h
  obtain ⟨owners, ho, rfl⟩ := h
  exact Store.write_other ho different

theorem World.write_other_cell (h : w.write r index value = some next) (different : index ≠ other) :
    next.read r other = w.read r other := by
  simp only [World.write, Option.map_eq_some_iff] at h
  obtain ⟨owners, ho, rfl⟩ := h
  obtain ⟨before, after, hb, ha, hl⟩ := Store.write_target ho
  simp [World.read, World.lookup, hb, hl, Owner.write_other ha different]

theorem World.write_exists (hl : w.lookup r = some owner) (hi : index < owner.length) :
    ∃ next, w.write r index value = some next := by
  obtain ⟨owners, ho⟩ := Store.write_exists hl hi (value := value)
  exact ⟨{ w with owners }, by simp [World.write, ho]⟩

def World.liveCells (w : World) : Nat := (w.owners.map Owner.length).sum

def World.positiveHeap (w : World) : List (Nat × Site × List APL.I64) :=
  w.owners.filterMap fun owner => match owner with
    | .positive ordinal site cells => some (ordinal, site, cells)
    | .empty _ _ => none

def World.activeEmpties (w : World) : List (Nat × Site) :=
  w.owners.filterMap fun owner => match owner with
    | .positive _ _ _ => none
    | .empty ordinal site => some (ordinal, site)

theorem World.write_length (h : w.write r index value = some next) : next.length r = w.length r := by
  simp only [World.write, Option.map_eq_some_iff] at h
  obtain ⟨owners, ho, rfl⟩ := h
  obtain ⟨before, after, hb, ha, hl⟩ := Store.write_target ho
  have hs := congrArg Shape.length (Owner.write_shape ha)
  simp [World.length, World.lookup, hb, hl, show after.length = before.length from hs]

theorem World.write_footprint (h : w.write r index value = some next) :
    next.owners.map Owner.shape = w.owners.map Owner.shape ∧
      next.nextRequest = w.nextRequest ∧ next.nextEmpty = w.nextEmpty ∧ next.trace = w.trace := by
  simp only [World.write, Option.map_eq_some_iff] at h
  obtain ⟨owners, ho, rfl⟩ := h
  exact ⟨Store.write_shapes ho, rfl, rfl, rfl⟩

theorem World.write_liveCells (h : w.write r index value = some next) : next.liveCells = w.liveCells := by
  have hs := congrArg (fun xs => (xs.map Shape.length).sum) (World.write_footprint h).1
  simpa [World.liveCells, List.map_map, Function.comp_def, Owner.shape] using hs

theorem World.write_ownerCount (h : w.write r index value = some next) : next.owners.length = w.owners.length := by
  simpa using congrArg List.length (World.write_footprint h).1

theorem allocate_target (h : p.maxCells < n) :
    allocate p responses w site n initial = (.targetRejected, w) := by simp [allocate, h]

theorem allocate_empty : allocate p responses w site 0 initial =
    (.allocated (.empty w.nextEmpty),
      ⟨.empty w.nextEmpty site :: w.owners, w.nextRequest, w.nextEmpty + 1,
        .emptyOpen w.nextEmpty site :: w.revTrace⟩) := by simp [allocate]

theorem allocate_success (hn : 0 < n) (hb : n ≤ p.maxCells) (hr : responses w.nextRequest = .success) :
    allocate p responses w site n initial =
      (.allocated (.positive w.nextRequest),
        ⟨.positive w.nextRequest site (List.replicate n initial) :: w.owners,
          w.nextRequest + 1, w.nextEmpty, .request w.nextRequest site n .success :: w.revTrace⟩) := by
  simp [allocate, Nat.not_lt.mpr hb, Nat.ne_of_gt hn, hr]

theorem allocate_refused (hn : 0 < n) (hb : n ≤ p.maxCells) (hr : responses w.nextRequest = .refused) :
    allocate p responses w site n initial =
      (.refused, ⟨w.owners, w.nextRequest + 1, w.nextEmpty,
        .request w.nextRequest site n .refused :: w.revTrace⟩) := by
  simp [allocate, Nat.not_lt.mpr hb, Nat.ne_of_gt hn, hr]

theorem allocate_valid (hw : w.Valid p) : (allocate p responses w site n initial).2.Valid p := by
  by_cases hb : p.maxCells < n
  · simpa [allocate, hb] using hw
  · by_cases hz : n = 0
    · subst n
      rw [allocate_empty]
      exact ⟨hw.profile, by simpa [World.trace, Owner.shape, Owner.ref, Owner.site, Owner.length, Owner.cells] using History.emptyOpen (site := site) hw.history⟩
    · have hn : 0 < n := by omega
      have bound : n ≤ p.maxCells := by omega
      cases hr : responses w.nextRequest with
      | refused =>
          rw [allocate_refused hn bound hr]
          exact ⟨hw.profile, by simpa [World.trace] using History.refused (site := site) hw.history hn bound⟩
      | success =>
          rw [allocate_success hn bound hr]
          refine ⟨hw.profile, ?_⟩
          simpa [World.trace, Owner.shape, Owner.ref, Owner.site, Owner.length, Owner.cells] using
            History.success (site := site) hw.history hn bound

theorem allocate_initialized (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .success) :
    (allocate p responses w site n initial).2.lookup (.positive w.nextRequest) =
      some (.positive w.nextRequest site (List.replicate n initial)) := by
  rw [allocate_success hn hb hr]
  simp [World.lookup, Store.lookup, Owner.ref]

theorem allocate_initial_cell (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .success) (hi : index < n) :
    (allocate p responses w site n initial).2.read (.positive w.nextRequest) index = some initial := by
  simp [World.read, allocate_initialized hn hb hr, Owner.cells, hi]

theorem allocate_positive_length (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .success) :
    (allocate p responses w site n initial).2.length (.positive w.nextRequest) = some n := by
  simp [World.length, allocate_initialized hn hb hr, Owner.length, Owner.cells]

theorem allocate_empty_length :
    (allocate p responses w site 0 initial).2.length (.empty w.nextEmpty) = some 0 := by
  rw [allocate_empty]
  simp [World.length, World.lookup, Store.lookup, Owner.ref, Owner.length, Owner.cells]

theorem allocate_refusal_frame (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .refused) :
    (allocate p responses w site n initial).2.owners = w.owners := by
  rw [allocate_refused hn hb hr]

theorem allocate_positive_frame (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .success) (different : r ≠ .positive w.nextRequest) :
    (allocate p responses w site n initial).2.lookup r = w.lookup r := by
  rw [allocate_success hn hb hr]
  simp [World.lookup, Store.lookup, Owner.ref, Ne.symm different]

theorem allocate_empty_frame (different : r ≠ .empty w.nextEmpty) :
    (allocate p responses w site 0 initial).2.lookup r = w.lookup r := by
  rw [allocate_empty]
  simp [World.lookup, Store.lookup, Owner.ref, Ne.symm different]

theorem allocate_positive_liveCells (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .success) :
    (allocate p responses w site n initial).2.liveCells = n + w.liveCells := by
  rw [allocate_success hn hb hr]
  simp [World.liveCells, Owner.length, Owner.cells]

theorem allocate_empty_positiveHeap :
    (allocate p responses w site 0 initial).2.positiveHeap = w.positiveHeap := by
  rw [allocate_empty]
  simp [World.positiveHeap]

theorem allocate_positive_emptySet (hn : 0 < n) (hb : n ≤ p.maxCells)
    (hr : responses w.nextRequest = .success) :
    (allocate p responses w site n initial).2.activeEmpties = w.activeEmpties := by
  rw [allocate_success hn hb hr]
  simp [World.activeEmpties]

theorem World.close_spec (h : w.close r site = some next) :
    ∃ owner rest, w.owners = owner :: rest ∧ owner.ref = r ∧ owner.site = site ∧
      next = { w with owners := rest, revTrace := owner.closeEvent :: w.revTrace } := by
  unfold World.close at h
  cases ho : w.owners with
  | nil => simp [ho] at h
  | cons first rest =>
      simp only [ho] at h
      split at h
      next he => exact ⟨first, rest, rfl, he.1, he.2, (Option.some.inj h).symm⟩
      next _ => contradiction

theorem World.close_top (h : w.owners = owner :: rest) :
    w.close owner.ref owner.site = some { w with owners := rest, revTrace := owner.closeEvent :: w.revTrace } := by
  simp [World.close, h]

theorem World.close_valid (hw : w.Valid p) (h : w.close r site = some next) : next.Valid p := by
  obtain ⟨owner, rest, ho, _, _, rfl⟩ := World.close_spec h
  refine ⟨hw.profile, ?_⟩
  have hist := hw.history
  rw [ho] at hist
  cases owner with
  | positive ordinal allocSite cells => simpa [World.trace, Owner.closeEvent, Owner.site] using History.release hist
  | empty ordinal allocSite => simpa [World.trace, Owner.closeEvent, Owner.site] using History.emptyClose hist

theorem World.close_retired (hw : w.Valid p) (h : w.close r site = some next) : next.lookup r = none := by
  obtain ⟨owner, rest, ho, hr, _, rfl⟩ := World.close_spec h
  have hu := hw.unique
  rw [ho, List.map_cons] at hu
  apply Store.lookup_none_iff.mpr
  simpa [hr] using (List.nodup_cons.mp hu).1

theorem World.close_other (h : w.close r site = some next) (different : other ≠ r) :
    next.lookup other = w.lookup other := by
  obtain ⟨owner, rest, ho, hr, _, rfl⟩ := World.close_spec h
  simp [World.lookup, ho, Store.lookup, hr, Ne.symm different]

theorem World.close_counters (h : w.close r site = some next) :
    next.nextRequest = w.nextRequest ∧ next.nextEmpty = w.nextEmpty := by
  obtain ⟨owner, rest, _, _, _, rfl⟩ := World.close_spec h
  exact ⟨rfl, rfl⟩

theorem World.close_liveCells (h : w.close r site = some next) :
    ∃ owner, w.lookup r = some owner ∧ next.liveCells + owner.length = w.liveCells := by
  obtain ⟨owner, rest, ho, hr, _, rfl⟩ := World.close_spec h
  exact ⟨owner, by simp [World.lookup, ho, Store.lookup, hr], by
    simp [World.liveCells, ho, Nat.add_comm]⟩

def Event.requestOrdinal : Event → Option Nat
  | .request ordinal _ _ _ => some ordinal
  | _ => none

def Event.emptyOrdinal : Event → Option Nat
  | .emptyOpen ordinal _ => some ordinal
  | _ => none

theorem History.request_ordinals (h : History p nr ne owners trace) :
    trace.filterMap Event.requestOrdinal = List.range nr := by
  induction h <;> simp_all [Event.requestOrdinal, List.range_succ]

theorem History.empty_ordinals (h : History p nr ne owners trace) :
    trace.filterMap Event.emptyOrdinal = List.range ne := by
  induction h <;> simp_all [Event.emptyOrdinal, List.range_succ]

theorem allocate_request_trace (hn : 0 < n) (hb : n ≤ p.maxCells) :
    (allocate p responses w site n initial).2.nextRequest = w.nextRequest + 1 ∧
    (allocate p responses w site n initial).2.nextEmpty = w.nextEmpty ∧
    (allocate p responses w site n initial).2.trace =
      w.trace ++ [.request w.nextRequest site n (responses w.nextRequest)] := by
  cases hr : responses w.nextRequest <;>
    simp [allocate, Nat.not_lt.mpr hb, Nat.ne_of_gt hn, hr, World.trace]

theorem allocate_empty_trace :
    (allocate p responses w site 0 initial).2.nextRequest = w.nextRequest ∧
    (allocate p responses w site 0 initial).2.nextEmpty = w.nextEmpty + 1 ∧
    (allocate p responses w site 0 initial).2.trace = w.trace ++ [.emptyOpen w.nextEmpty site] := by
  rw [allocate_empty]
  simp [World.trace]

theorem allocate_live_frame (hw : w.Valid p) (hl : w.lookup r = some owner) :
    (allocate p responses w site n initial).2.lookup r = some owner := by
  by_cases hb : p.maxCells < n
  · rw [allocate_target hb]; exact hl
  · by_cases hz : n = 0
    · subst n
      have different : r ≠ .empty w.nextEmpty := by
        intro he
        rw [he, hw.fresh_empty] at hl
        cases hl
      rw [allocate_empty_frame different]
      exact hl
    · have hn : 0 < n := by omega
      have bound : n ≤ p.maxCells := by omega
      cases hr : responses w.nextRequest with
      | refused => rw [allocate_refused hn bound hr]; exact hl
      | success =>
          have different : r ≠ .positive w.nextRequest := by
            intro he
            rw [he, hw.fresh_positive] at hl
            cases hl
          rw [allocate_positive_frame hn bound hr different]
          exact hl

theorem allocate_allocated_fresh_length (hw : w.Valid p)
    (ha : allocate p responses w site n initial = (.allocated r, next)) :
    w.lookup r = none ∧ next.length r = some n := by
  by_cases hb : p.maxCells < n
  · rw [allocate_target hb] at ha; cases ha
  · by_cases hz : n = 0
    · subst n
      rw [allocate_empty] at ha
      cases ha
      exact ⟨hw.fresh_empty, by
        simp [World.length, World.lookup, Store.lookup, Owner.ref, Owner.length, Owner.cells]⟩
    · have hn : 0 < n := by omega
      have bound : n ≤ p.maxCells := by omega
      cases hr : responses w.nextRequest with
      | refused => rw [allocate_refused hn bound hr] at ha; cases ha
      | success =>
          rw [allocate_success hn bound hr] at ha
          cases ha
          exact ⟨hw.fresh_positive, by
            simp [World.length, World.lookup, Store.lookup, Owner.ref, Owner.length, Owner.cells]⟩

theorem World.close_trace (h : w.close r site = some next) :
    next.trace = w.trace ++ [r.closeEvent site] := by
  obtain ⟨owner, rest, _, hr, hs, rfl⟩ := World.close_spec h
  rw [← hr, ← hs]
  cases owner <;> simp [World.trace, Owner.ref, Owner.site, Owner.closeEvent, Ref.closeEvent]

theorem World.close_rejects_non_top (h : w.owners = owner :: rest)
    (different : owner.ref ≠ r ∨ owner.site ≠ site) : w.close r site = none := by
  simp only [World.close, h]
  split
  next he => exact False.elim (different.elim (· he.1) (· he.2))
  next _ => rfl

theorem World.read_exists (hl : w.lookup r = some owner) (hi : index < owner.length) :
    ∃ value, w.read r index = some value := by
  exact ⟨owner.cells[index], by simp [World.read, hl, List.getElem?_eq_getElem hi]⟩

theorem World.read_bounds (h : w.read r index = some value) :
    ∃ owner, w.lookup r = some owner ∧ index < owner.length ∧ owner.cells[index]? = some value := by
  simp only [World.read, Option.bind_eq_some_iff] at h
  obtain ⟨owner, hl, hv⟩ := h
  exact ⟨owner, hl, (List.getElem?_eq_some_iff.mp hv).choose, hv⟩

end ANL.Memory
