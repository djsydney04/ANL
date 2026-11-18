import ANL.WordsSimulationData

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

variable {rid key : Nat} {value prior : α} {entries updated : List (Nat × α)}

@[simp] theorem lookupId_cons_same : Mir.lookupId rid ((rid, value) :: entries) = some value := by
  simp [Mir.lookupId, ANL.Memory.Mir.lookupId]

@[simp] theorem lookupId_cons_other (h : rid ≠ key) :
    Mir.lookupId rid ((key, prior) :: entries) = Mir.lookupId rid entries := by
  simp [Mir.lookupId, ANL.Memory.Mir.lookupId, h]

theorem lookupId_mem (h : Mir.lookupId rid entries = some value) : (rid, value) ∈ entries := by
  induction entries with
  | nil => simp [Mir.lookupId, ANL.Memory.Mir.lookupId] at h
  | cons pair rest ih =>
      rcases pair with ⟨key, prior⟩
      by_cases hk : rid = key
      · subst key; simp [Mir.lookupId, ANL.Memory.Mir.lookupId] at h; subst prior; exact .head _
      · simp [Mir.lookupId, ANL.Memory.Mir.lookupId, hk] at h
        exact .tail _ (ih h)

theorem updateId_lookup_same (h : Mir.updateId rid value entries = some updated) :
    Mir.lookupId rid updated = some value := by
  induction entries generalizing updated with
  | nil => simp [Mir.updateId, ANL.Memory.Mir.updateId] at h
  | cons pair rest ih =>
      rcases pair with ⟨key, prior⟩
      by_cases hk : rid = key
      · subst key; simp [Mir.updateId, ANL.Memory.Mir.updateId] at h; subst updated; simp
      · simp only [Mir.updateId, ANL.Memory.Mir.updateId, ite_eq_right hk, Option.map_eq_some_iff] at h
        obtain ⟨tail, ht, rfl⟩ := h
        simpa [Mir.lookupId, ANL.Memory.Mir.lookupId, hk] using ih ht

theorem updateId_lookup_other (h : Mir.updateId rid value entries = some updated) (hk : key ≠ rid) :
    Mir.lookupId key updated = Mir.lookupId key entries := by
  induction entries generalizing updated with
  | nil => simp [Mir.updateId, ANL.Memory.Mir.updateId] at h
  | cons pair rest ih =>
      rcases pair with ⟨found, prior⟩
      by_cases hr : rid = found
      · subst found; simp [Mir.updateId, ANL.Memory.Mir.updateId] at h; subst updated; simp [Mir.lookupId, ANL.Memory.Mir.lookupId, hk]
      · simp only [Mir.updateId, ANL.Memory.Mir.updateId, ite_eq_right hr, Option.map_eq_some_iff] at h
        obtain ⟨tail, ht, rfl⟩ := h
        by_cases kf : key = found
        · subst found; simp
        · simp [Mir.lookupId, ANL.Memory.Mir.lookupId, kf, ih ht]

theorem updateId_exists (h : Mir.lookupId rid entries = some prior) :
    ∃ updated, Mir.updateId rid value entries = some updated := by
  induction entries with
  | nil => simp [Mir.lookupId, ANL.Memory.Mir.lookupId] at h
  | cons pair rest ih =>
      rcases pair with ⟨key, old⟩
      by_cases hk : rid = key
      · subst key; exact ⟨(rid, value) :: rest, by simp [Mir.updateId, ANL.Memory.Mir.updateId]⟩
      · simp only [Mir.lookupId, ANL.Memory.Mir.lookupId, ite_eq_right hk] at h
        obtain ⟨tail, ht⟩ := ih h
        exact ⟨(key, old) :: tail, by simp [Mir.updateId, ANL.Memory.Mir.updateId, hk, ht]⟩

theorem updateId_keys (h : Mir.updateId rid value entries = some updated) :
    updated.map Prod.fst = entries.map Prod.fst := by
  induction entries generalizing updated with
  | nil => simp [Mir.updateId, ANL.Memory.Mir.updateId] at h
  | cons pair rest ih =>
      rcases pair with ⟨key, prior⟩
      by_cases hk : rid = key
      · subst key; simp [Mir.updateId, ANL.Memory.Mir.updateId] at h; subst updated; rfl
      · simp only [Mir.updateId, ANL.Memory.Mir.updateId, ite_eq_right hk, Option.map_eq_some_iff] at h
        obtain ⟨tail, ht, rfl⟩ := h
        simp [ih ht]

theorem LocalsRel.retarget (h : LocalsRel a locals values)
    (same : ∀ l ∈ locals, localValue b l = localValue a l) : LocalsRel b locals values := by
  induction h with
  | nil => exact .nil
  | @cons l v ls vs hv h ih =>
      exact .cons ((same l (.head _)).trans hv) (ih (fun l hl => same l (.tail _ hl)))

theorem mutableIds_mem (h : Local.mutable slot ∈ locals) : slot.id ∈ mutableIds locals := by
  induction locals with
  | nil => simp at h
  | cons l rest ih =>
      cases l with
      | value t => exact ih (by simpa using h)
      | mutable s =>
          rcases List.mem_cons.mp h with eq | h
          · cases eq; exact .head _
          · exact .tail _ (ih h)

theorem LocalsRel.temp_extension (h : LocalsRel a locals values)
    (fresh : ∀ t, Local.value t ∈ locals → t.id ≠ rid) :
    LocalsRel {a with temps := (rid, v) :: a.temps} locals values := by
  apply h.retarget
  intro l hl
  cases l with
  | value t => simp [localValue, Mir.Activation.temp, fresh t hl]
  | mutable s => rfl

theorem LocalsRel.slot_update_other (h : LocalsRel a locals values)
    (updated : Mir.updateId rid v a.slots = some slots)
    (fresh : rid ∉ mutableIds locals) :
    LocalsRel {a with slots} locals values := by
  apply h.retarget
  intro l hl
  cases l with
  | value t => rfl
  | mutable s =>
      have hs : s.id ≠ rid := by intro eq; exact fresh (eq ▸ mutableIds_mem hl)
      exact updateId_lookup_other updated hs

theorem ResourcesRel.lookup {index : Nat} (h : ResourcesRel ids source target)
    (unique : ids.Nodup) (hi : ids[index]? = some rid) :
    ∃ b, source[index]? = some b ∧ Mir.lookupId rid target = some (binding b) := by
  induction h generalizing index with
  | nil => simp at hi
  | @cons ids bs rs b key h ih =>
      have hn := List.nodup_cons.mp unique
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
                subst rid
                exact ⟨b, rfl, by simp⟩
      | succ index =>
          have hr : ids[index]? = some rid := by simpa using hi
          obtain ⟨found, hf, lookup⟩ := ih hn.2 hr
          have ne : rid ≠ key := by intro eq; exact hn.1 (eq ▸ List.mem_of_getElem? hr)
          exact ⟨found, hf, by simpa [Mir.lookupId, ANL.Memory.Mir.lookupId, ne] using lookup⟩

end ANL.Words.Simulation
