import ANL.WordsMir

namespace ANL.Words.Mir

variable {sigs : Signatures} {c : Context} {b : Block} {op : Operation} {t u : Ty}
variable {ids : List Nat} {n i r : Nat} {args : List Temp} {types : List Ty} {a : Temp}
variable {p : Program} {f : Function}

mutual
  theorem checkBlock_iff (sigs : Signatures) (c : Context) (b : Block) (t : Ty) :
      checkBlock sigs c b t = true ↔ b.Typed sigs c t := by
    cases b with
    | yield value => simp [checkBlock, Block.Typed]
    | next d op rest =>
        simp only [checkBlock, Block.Typed, Bool.and_eq_true,
          checkOperation_iff sigs c op d.ty, checkBlock_iff sigs (c.withTemp d) rest t]
  theorem checkOperation_iff (sigs : Signatures) (c : Context) (op : Operation) (t : Ty) :
      checkOperation sigs c op t = true ↔ op.Typed sigs c t := by
    cases op <;>
      simp [checkOperation, Operation.Typed, checkBlock_iff, wordLiteralType_iff,
        unaryType_iff, binaryType_iff, convertType_iff, and_assoc]
end

theorem checkBlock_sound (h : checkBlock sigs c b t = true) : b.Typed sigs c t :=
  (checkBlock_iff ..).mp h
theorem checkBlock_complete (h : b.Typed sigs c t) : checkBlock sigs c b t = true :=
  (checkBlock_iff ..).mpr h
theorem checkOperation_sound (h : checkOperation sigs c op t = true) : op.Typed sigs c t :=
  (checkOperation_iff ..).mp h
theorem checkOperation_complete (h : op.Typed sigs c t) : checkOperation sigs c op t = true :=
  (checkOperation_iff ..).mpr h

theorem Dense.length (h : Dense ids n) : ids.length = n := by
  simpa [Dense] using List.Perm.length_eq h

theorem Dense.mem_iff (h : Dense ids n) : i ∈ ids ↔ i < n := by
  exact (List.Perm.mem_iff h).trans List.mem_range

theorem Dense.nodup (h : Dense ids n) : ids.Nodup :=
  h.nodup_iff.mpr List.nodup_range

theorem Dense.sorted_eq (h : Dense ids n) : ids.mergeSort (· ≤ ·) = List.range n := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ hab hba
    exact Nat.le_antisymm hab hba
  · simpa using List.pairwise_mergeSort (le := fun a b : Nat => a ≤ b)
      (by intro a b c h₁ h₂; exact of_decide_eq_true (by simpa using decide_eq_true (Nat.le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂))))
      (by intro a b; rcases Nat.le_total a b with h | h <;> simp [h]) ids
  · exact List.pairwise_le_range
  · exact (List.mergeSort_perm ids _).trans h

theorem checkDense_iff (ids : List Nat) (n : Nat) : checkDense ids n = true ↔ Dense ids n := by
  simp only [checkDense, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hlen, sorted⟩
    unfold Dense
    rw [hlen] at sorted
    have hs : (ids.mergeSort (· ≤ ·)).Perm (List.range n) := by rw [sorted]
    exact (List.mergeSort_perm ids _).symm.trans hs
  · intro h
    exact ⟨h.length, by simpa [h.length] using h.sorted_eq⟩

theorem checkFunction_iff (sigs : Signatures) (f : Function) :
    checkFunction sigs f = true ↔ f.WellFormed sigs := by
  simp [checkFunction, Function.WellFormed, checkDense_iff, checkBlock_iff, and_assoc]

theorem checkProgram_iff (p : Program) : checkProgram p = true ↔ p.WellFormed := by
  simp only [checkProgram, Program.WellFormed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, checkFunction_iff, and_assoc]

theorem checkProgram_sound (h : checkProgram p = true) : p.WellFormed := (checkProgram_iff p).mp h
theorem checkProgram_complete (h : p.WellFormed) : checkProgram p = true := (checkProgram_iff p).mpr h

theorem ArgsTyped.length (h : ArgsTyped c args types) : args.length = types.length := by
  simpa using congrArg List.length h.2

theorem ArgsTyped.get (h : ArgsTyped c args types) (ha : args[i]? = some a) :
    types[i]? = some a.ty ∧ a ∈ c.temps := by
  constructor
  · rw [← h.2, List.getElem?_map, ha]
    rfl
  · exact h.1 _ (List.mem_of_getElem? ha)

theorem CallTyped.lookup {fnId : Nat} (h : CallTyped sigs c fnId view args t) :
    ∃ fn, sigs[fnId]? = some fn ∧ fn.view = view ∧ ArgsTyped c args fn.params ∧ fn.result = t := by
  unfold CallTyped at h
  split at h
  · contradiction
  · exact ⟨_, ‹_›, h⟩

theorem Writable.readable (h : Writable c r) : Readable c r := by
  obtain ⟨binding, hm, hi, _⟩ := h
  exact ⟨binding, hm, hi⟩

theorem Lendable.edit_writable (h : Lendable c r .edit) : Writable c r := by
  obtain ⟨binding, hm, hi, hp⟩ := h
  exact ⟨binding, hm, hi, by simpa [ANL.Memory.Mode.CanLend] using hp⟩

theorem Block.Typed.yield_type (h : b.Typed sigs c t) : b.yieldValue.ty = t := by
  induction b using Block.rec (motive_2 := fun _ => True) generalizing c with
  | yield value => exact h.2
  | next d op rest _ ih => exact ih h.2
  | _ => trivial

theorem Block.Typed.unique (a : b.Typed sigs c t) (b' : b.Typed sigs c u) : t = u :=
  a.yield_type.symm.trans b'.yield_type

theorem Program.signatures_lookup (h : p.functions[i]? = some f) :
    p.signatures[i]? = some f.signature := by
  simp [Program.signatures, Array.getElem?_map, h]

theorem Program.WellFormed.function (h : p.WellFormed) (hf : p.functions[i]? = some f) :
    f.id = i ∧ f.WellFormed p.signatures := by
  have hi : i < p.functions.size := (Array.getElem?_eq_some_iff.mp hf).1
  have ids := h.2.2.2.1 i (List.mem_range.mpr hi)
  simp only [hf, Option.map_some, Option.some.injEq] at ids
  exact ⟨ids, h.2.2.2.2.2 f (by simpa using Array.mem_of_getElem? hf)⟩

theorem Program.WellFormed.entry (h : p.WellFormed) :
    ∃ f, p.functions[p.entry]? = some f ∧ f.view = none ∧ f.params = [] ∧
      f.result = .scalar (.legacy .i64) ∧ f.WellFormed p.signatures := by
  have he := h.2.2.2.2.1
  unfold Program.EntryValid at he
  split at he
  · contradiction
  · exact ⟨_, ‹_›, he.1, he.2.1, he.2.2, (h.function ‹_›).2⟩

theorem Program.signatures_lookup_inv (h : p.signatures[i]? = some sig) :
    ∃ f, p.functions[i]? = some f ∧ f.signature = sig := by
  simpa only [Program.signatures, Array.getElem?_map, Option.map_eq_some_iff] using h

theorem Function.WellFormed.tables (h : f.WellFormed sigs) :
    Dense f.inventory.temps f.tempCount ∧ Dense f.inventory.slots f.slotCount ∧
      Dense f.inventory.resources f.resourceCount := ⟨h.1, h.2.1, h.2.2.1⟩

theorem Function.WellFormed.body (h : f.WellFormed sigs) :
    f.body.Typed sigs f.context f.result := h.2.2.2

theorem Temp.Typed.visible (h : a.Typed c t) : a ∈ c.temps := h.1
theorem Temp.Typed.annotation (h : a.Typed c t) : a.ty = t := h.2

private theorem binding_unique {α : Type} (key : α → Nat) {entries : List α} {a b : α}
    (hn : (entries.map key).Nodup) (ha : a ∈ entries) (hb : b ∈ entries)
    (he : key a = key b) : a = b := by
  induction entries with
  | nil => simp at ha
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact False.elim (hn.1 (he ▸ List.mem_map_of_mem hb))
    · exact False.elim (hn.1 (he ▸ List.mem_map_of_mem ha))
    · exact ih hn.2 ha hb

theorem Temp.Typed.same_id {a b : Temp} (hc : (c.temps.map Temp.id).Nodup)
    (ha : a.Typed c t) (hb : b.Typed c u) (hi : a.id = b.id) : a = b ∧ t = u := by
  have eq := binding_unique Temp.id hc ha.1 hb.1 hi
  exact ⟨eq, ha.2.symm.trans (eq ▸ hb.2)⟩

theorem Slot.Typed.same_id {a b : Slot} (hc : (c.slots.map Slot.id).Nodup)
    (ha : a.Typed c t) (hb : b.Typed c u) (hi : a.id = b.id) : a = b ∧ t = u := by
  have eq := binding_unique Slot.id hc ha.1 hb.1 hi
  exact ⟨eq, ha.2.symm.trans (eq ▸ hb.2)⟩

theorem Operation.Typed.heap_parts {site owner : Nat} {length : Temp} {initial success failure : Block}
    (h : (Operation.heapScope site owner length initial success failure).Typed sigs c t) :
    length.Typed c (.scalar (.legacy .i64)) ∧ initial.Typed sigs c (.scalar (.legacy .i64)) ∧
      success.Typed sigs (c.withOwner owner) t ∧ failure.Typed sigs c t := h

theorem Operation.Typed.write_parts {r : Nat} {index : Temp} {value : Block}
    (h : (Operation.bufferWrite r index value).Typed sigs c t) :
    Writable c r ∧ index.Typed c (.scalar (.legacy .i64)) ∧ value.Typed sigs c (.scalar (.legacy .i64)) ∧
      t = .scalar (.legacy .unit) := h

theorem Operation.Typed.view_parts {f r : Nat} {mode : ViewMode}
    (h : (Operation.callView f r mode args).Typed sigs c t) :
    Lendable c r mode ∧ ∃ fn, sigs[f]? = some fn ∧ fn.view = some mode ∧
      ArgsTyped c args fn.params ∧ fn.result = t := ⟨h.1, h.2.lookup⟩

theorem Operation.Typed.ordinary_call {f : Nat}
    (h : (Operation.call f args).Typed sigs c t) :
    ∃ fn, sigs[f]? = some fn ∧ fn.view = none ∧ ArgsTyped c args fn.params ∧
      fn.result = t := h.lookup

end ANL.Words.Mir
