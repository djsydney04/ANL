import ANL.WordsCore
import ANL.WordsValueTyping

namespace ANL.Words

theorem HasType.annotation (h : HasType sigs Γ R e t) : e.ty = t := by
  cases h <;> rfl

theorem checkTerm_complete (h : HasType sigs Γ R e t) : checkTerm sigs Γ R e = some t := by
  induction h using HasType.rec
    (motive_2 := fun Γ R es ts _ => es.mapM (checkTerm sigs Γ R) = some ts) with
  | lit => simp [checkTerm, annotated]
  | word h => simp [checkTerm, annotated, wordLiteralType_iff.mpr h]
  | convert _ hs ih => simp [checkTerm, annotated, ih, convertType_iff.mpr hs]
  | «local» h => simp [checkTerm, annotated, h]
  | letE _ _ ha hb => simp [checkTerm, annotated, ha, hb]
  | letMut _ _ ha hb => simp [checkTerm, annotated, ha, hb]
  | assign hi _ ha => simp [checkTerm, annotated, hi, ha]
  | whileE _ _ hc hb => simp [checkTerm, annotated, hc, hb]
  | ifE _ _ _ hc ha hb => simp [checkTerm, annotated, hc, ha, hb]
  | unary _ hs ha => simp [checkTerm, annotated, ha, unaryType_iff.mpr hs]
  | binary _ _ hop ha hb => simp [checkTerm, annotated, ha, hb, binaryType_iff.mpr hop]
  | call hf hv _ ha => simp [checkTerm, annotated, hf, hv, ha]
  | tuple _ ih =>
    simp only [checkTerm, ih, bind, Option.bind_some, scalarList_complete,
      APL.FlatProducts.Flat.make_fields]
    simp [annotated]
  | project _ hi ih => simp [checkTerm, annotated, ih, hi]
  | heap _ _ _ _ hl hi hs hf => simp [checkTerm, annotated, hl, hi, hs, hf]
  | bufferLength hr => simp [checkTerm, annotated, hr]
  | bufferRead hr _ hi => simp [checkTerm, annotated, hr, hi]
  | bufferWrite hr hm _ _ hi hv => simp [checkTerm, annotated, hr, hm, hi, hv]
  | callView hf hm hr hp _ ha => simp [checkTerm, annotated, hf, hm, hr, hp, ha]
  | nil => rfl
  | cons _ _ ha hb => simp [List.mapM_cons, ha, hb]

theorem checkTerm_sound (h : checkTerm sigs Γ R e = some t) : HasType sigs Γ R e t := by
  induction e using Term.rec
    (motive_2 := fun es => ∀ Γ R ts, es.mapM (checkTerm sigs Γ R) = some ts →
      ArgsTyped sigs Γ R es ts) generalizing Γ R t with
  | lit ann v =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    cases h
    exact .lit
  | word ann width value =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨hv, ht⟩ := h
    subst ann
    exact .word (wordLiteralType_iff.mp hv)
  | convert ann mode target operand ih =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨hv, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at hv
    obtain ⟨source, hs, hc⟩ := hv
    exact .convert (ih hs) (convertType_iff.mp hc)
  | «local» ann i =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    obtain ⟨⟨ty, permission⟩, hi, ht⟩ := Option.map_eq_some_iff.mp h
    change ty = t at ht
    subst ty
    exact .local hi
  | letE ann a b ia ib =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hb⟩ := h
    exact .letE (ia ha) (ib hb)
  | letMut ann a b ia ib =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hb⟩ := h
    exact .letMut (ia ha) (ib hb)
  | assign ann i a ia =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨u, permission⟩, hi, v, ha, h⟩ := h
    split at h
    next ht =>
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      exact .assign hi (ia ha)
    · contradiction
  | whileE ann c b ic ib =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨ct, hc, bt, hb, h⟩ := h
    split at h
    next ht =>
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      exact .whileE (ic hc) (ib hb)
    · contradiction
  | ifE ann c a b ic ia ib =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨ct, hc, ta, ha, tb, hb, h⟩ := h
    split at h
    next ht =>
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      exact .ifE (ic hc) (ia ha) (ib hb)
    · contradiction
  | unary ann op a ia =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hop⟩ := h
    exact .unary (ia ha) (unaryType_iff.mp hop)
  | binary ann op a b ia ib =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, v, hb, hop⟩ := h
    exact .binary (ia ha) (ib hb) (binaryType_iff.mp hop)
  | call ann f args ih =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨fn, hf, actual, ha, h⟩ := h
    split at h
    next he =>
      obtain ⟨hv, rfl⟩ := he
      cases h
      exact .call hf hv (ih _ _ _ ha)
    · contradiction
  | tuple ann fields ih =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨types, ht, scalars, hs, shape, hm, h⟩ := h
    cases h
    have typed := ih Γ R types ht
    rw [scalarList_sound hs, ← make_fields hm] at typed
    exact .tuple typed
  | project ann base index ih =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨ty, hb, h⟩ := h
    cases ty with
    | scalar ty => simp at h
    | tuple shape =>
      obtain ⟨ty, hi, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .project (ih hb) hi
  | heap ann site len initial success failed il ii iss iff =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨lt, hl, it, hi, st, hs, ft, hf, h⟩ := h
    split at h
    next he =>
      obtain ⟨rfl, rfl, rfl⟩ := he
      cases h
      exact .heap (il hl) (ii hi) (iss hs) (iff hf)
    · contradiction
  | bufferLength ann r =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨mode, hr, h⟩ := h
    cases h
    exact .bufferLength hr
  | bufferRead ann r index ih =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨mode, hr, it, hi, h⟩ := h
    split at h
    next he => cases h; subst it; exact .bufferRead hr (ih hi)
    · contradiction
  | bufferWrite ann r index value ii iv =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨mode, hr, it, hi, vt, hv, h⟩ := h
    split at h
    next he =>
      obtain ⟨hp, rfl, rfl⟩ := he
      cases h
      exact .bufferWrite hr hp (ii hi) (iv hv)
    · contradiction
  | callView ann f r mode args ih =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨fn, hf, source, hr, actual, ha, h⟩ := h
    split at h
    next he =>
      obtain ⟨hv, hp, rfl⟩ := he
      cases h
      exact .callView hf hv hr hp (ih _ _ _ ha)
    · contradiction
  | nil Γ R ts h =>
    simp at h
    subst ts
    exact .nil
  | cons a args ia ih Γ R ts h =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨t, ht, rest, hr, h⟩ := h
    cases h
    exact .cons (ia ht) (ih _ _ _ hr)

theorem checkTerm_iff : checkTerm sigs Γ R e = some t ↔ HasType sigs Γ R e t :=
  ⟨checkTerm_sound, checkTerm_complete⟩

theorem type_unique (ha : HasType sigs Γ R e a) (hb : HasType sigs Γ R e b) : a = b :=
  ha.annotation.symm.trans hb.annotation

theorem ArgsTyped.length (h : ArgsTyped sigs Γ R es ts) : es.length = ts.length := by
  induction es generalizing ts with
  | nil => cases h; rfl
  | cons a es ih =>
      cases h with
      | cons _ rest => exact congrArg Nat.succ (ih rest)

theorem ArgsTyped.annotations (h : ArgsTyped sigs Γ R es ts) : es.map Term.ty = ts := by
  induction es generalizing ts with
  | nil => cases h; rfl
  | cons a es ih =>
      cases h with
      | cons ht rest => simp [ht.annotation, ih rest]

theorem lookup_append {xs extra : List α} {i : Nat} {v : α} (h : xs[i]? = some v) : (xs ++ extra)[i]? = some v := by
  obtain ⟨lt, _⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left lt]
  exact h

/-- Appending inaccessible outer bindings preserves every checked index. -/
theorem HasType.weaken (h : HasType sigs Γ R e t) (values : VCtx) (resources : RCtx) :
    HasType sigs (Γ ++ values) (R ++ resources) e t := by
  induction h using HasType.rec
    (motive_2 := fun Γ R es ts _ => ArgsTyped sigs (Γ ++ values) (R ++ resources) es ts) with
  | lit => exact .lit
  | word h => exact .word h
  | convert _ hs ih => exact .convert ih hs
  | «local» hi => exact .local (lookup_append hi)
  | letE _ _ ha hb => exact .letE ha hb
  | letMut _ _ ha hb => exact .letMut ha hb
  | assign hi _ ha => exact .assign (lookup_append hi) ha
  | whileE _ _ hc hb => exact .whileE hc hb
  | ifE _ _ _ hc ha hb => exact .ifE hc ha hb
  | unary _ hs ha => exact .unary ha hs
  | binary _ _ hop ha hb => exact .binary ha hb hop
  | call hf hv _ ha => exact .call hf hv ha
  | tuple _ ha => exact .tuple ha
  | project _ hi ha => exact .project ha hi
  | heap _ _ _ _ hl hi hs hf => exact .heap hl hi hs hf
  | bufferLength hr => exact .bufferLength (lookup_append hr)
  | bufferRead hr _ hi => exact .bufferRead (lookup_append hr) hi
  | bufferWrite hr hp _ _ hi hv => exact .bufferWrite (lookup_append hr) hp hi hv
  | callView hf hm hr hp _ ha => exact .callView hf hm (lookup_append hr) hp ha
  | nil => exact .nil
  | cons _ _ ha hb => exact .cons ha hb

theorem read_cannot_write : ¬ANL.Memory.Mode.read.CanWrite := by simp [ANL.Memory.Mode.CanWrite]
theorem read_cannot_lend_edit : ¬ANL.Memory.Mode.read.CanLend .edit := by simp [ANL.Memory.Mode.CanLend, ANL.Memory.Mode.CanWrite]
theorem every_mode_lends_read (mode : Mode) : mode.CanLend .read := Or.inl rfl

theorem checkFunction_iff : checkFunction sigs fn = true ↔ fn.WellFormed sigs := by
  simp only [checkFunction, Bool.and_eq_true, decide_eq_true_eq, checkTerm_iff]
  constructor
  · rintro ⟨⟨hn, hs⟩, hb⟩; exact ⟨hn, hs, hb⟩
  · intro h; exact ⟨⟨h.name, h.sites⟩, h.body⟩

theorem checkEntry_iff : checkEntry p = true ↔ EntryValid p := by
  cases h : p.functions[p.entry]? <;> simp [checkEntry, EntryValid, h]

theorem checkProgram_iff : checkProgram p = true ↔ WellFormedProgram p := by
  simp only [checkProgram, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    checkFunction_iff, checkEntry_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hs, hr⟩, hp⟩, hi⟩, hn⟩, hf⟩, he⟩
    exact ⟨hs, hr, hp, hi, hn, hf, he⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h.schema, h.revision⟩, h.profile⟩, h.ids⟩, h.names⟩, h.functions⟩, h.entry⟩

theorem signatures_lookup {p : Program} {f : Nat} {fn : Function} (h : p.functions[f]? = some fn) :
    p.signatures[f]? = some fn.signature := by
  simp [Program.signatures, Array.getElem?_map, h]

theorem signatures_lookup_inv {p : Program} {f : Nat} {signature : Signature} (h : p.signatures[f]? = some signature) :
    ∃ fn, p.functions[f]? = some fn ∧ fn.signature = signature := by
  simpa only [Program.signatures, Array.getElem?_map, Option.map_eq_some_iff] using h

theorem WellFormedProgram.function_at {p : Program} {f : Nat} {fn : Function} (hp : WellFormedProgram p) (h : p.functions[f]? = some fn) :
    fn.WellFormed p.signatures := by
  apply hp.functions
  exact List.mem_iff_getElem?.mpr ⟨f, by simpa using h⟩

theorem WellFormedProgram.function_id {p : Program} {f : Nat} {fn : Function} (hp : WellFormedProgram p) (h : p.functions[f]? = some fn) :
    fn.id = f := by
  have hi := congrArg (fun xs => xs[f]?) hp.ids
  have lt := (Array.getElem?_eq_some_iff.mp h).choose
  simpa [List.getElem?_map, h, List.getElem?_range lt] using hi

theorem WellFormedProgram.entry_typed (hp : WellFormedProgram p) :
    ∃ fn, p.functions[p.entry]? = some fn ∧ fn.view = none ∧ fn.params = [] ∧
      fn.result = .scalar (.legacy .i64) ∧ HasType p.signatures [] [] fn.body (.scalar (.legacy .i64)) := by
  obtain ⟨fn, hf, hv, ha, ht⟩ := hp.entry
  have hb := (hp.function_at hf).body
  exact ⟨fn, hf, hv, ha, ht, by
    simpa [Function.valueContext, Function.resourceContext, immutable,
      viewContext, ANL.Memory.viewContext, hv, ha, ht] using hb⟩

end ANL.Words
