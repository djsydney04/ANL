import ANL.MemoryCore

namespace ANL.Memory

mutual
  inductive HasType (sigs : Signatures) : VCtx → RCtx → Term → Ty → Prop where
    | lit : HasType sigs Γ R (.lit (.scalar v.type) v) (.scalar v.type)
    | local : Γ[i]? = some (t, permission) → HasType sigs Γ R (.local t i) t
    | letE : HasType sigs Γ R a u → HasType sigs ((u, false) :: Γ) R b t →
        HasType sigs Γ R (.letE t a b) t
    | letMut : HasType sigs Γ R a u → HasType sigs ((u, true) :: Γ) R b t →
        HasType sigs Γ R (.letMut t a b) t
    | assign : Γ[i]? = some (t, true) → HasType sigs Γ R a t →
        HasType sigs Γ R (.assign (.scalar .unit) i a) (.scalar .unit)
    | whileE : HasType sigs Γ R c (.scalar .bool) → HasType sigs Γ R b (.scalar .unit) →
        HasType sigs Γ R (.whileE (.scalar .unit) c b) (.scalar .unit)
    | ifE : HasType sigs Γ R c (.scalar .bool) → HasType sigs Γ R a t → HasType sigs Γ R b t →
        HasType sigs Γ R (.ifE t c a b) t
    | unary : HasType sigs Γ R a (.scalar op.input) →
        HasType sigs Γ R (.unary (.scalar op.output) op a) (.scalar op.output)
    | binary : HasType sigs Γ R a u → HasType sigs Γ R b v →
        APL.FlatProducts.binaryType op u v = some t → HasType sigs Γ R (.binary t op a b) t
    | call : sigs[f]? = some fn → fn.view = none → ArgsTyped sigs Γ R args fn.params →
        HasType sigs Γ R (.call fn.result f args) fn.result
    | tuple : ArgsTyped sigs Γ R fields (shape.fields.map APL.FlatProducts.Ty.scalar) →
        HasType sigs Γ R (.tuple (.tuple shape) fields) (.tuple shape)
    | project : HasType sigs Γ R base (.tuple shape) → shape.fields[index]? = some t →
        HasType sigs Γ R (.project (.scalar t) base index) (.scalar t)
    | heap : HasType sigs Γ R len (.scalar .i64) → HasType sigs Γ R initial (.scalar .i64) →
        HasType sigs Γ (.owner :: R) success t → HasType sigs Γ R failed t →
        HasType sigs Γ R (.heap t site len initial success failed) t
    | bufferLength : R[r]? = some mode →
        HasType sigs Γ R (.bufferLength (.scalar .i64) r) (.scalar .i64)
    | bufferRead : R[r]? = some mode → HasType sigs Γ R index (.scalar .i64) →
        HasType sigs Γ R (.bufferRead (.scalar .i64) r index) (.scalar .i64)
    | bufferWrite : R[r]? = some mode → mode.CanWrite →
        HasType sigs Γ R index (.scalar .i64) → HasType sigs Γ R value (.scalar .i64) →
        HasType sigs Γ R (.bufferWrite (.scalar .unit) r index value) (.scalar .unit)
    | callView : sigs[f]? = some fn → fn.view = some mode → R[r]? = some source →
        source.CanLend mode → ArgsTyped sigs Γ R args fn.params →
        HasType sigs Γ R (.callView fn.result f r mode args) fn.result
  inductive ArgsTyped (sigs : Signatures) : VCtx → RCtx → List Term → List Ty → Prop where
    | nil : ArgsTyped sigs Γ R [] []
    | cons : HasType sigs Γ R e t → ArgsTyped sigs Γ R es ts →
        ArgsTyped sigs Γ R (e :: es) (t :: ts)
end

theorem HasType.annotation (h : HasType sigs Γ R e t) : e.ty = t := by
  cases h <;> rfl

theorem checkTerm_complete (h : HasType sigs Γ R e t) : checkTerm sigs Γ R e = some t := by
  induction h using HasType.rec
    (motive_2 := fun Γ R es ts _ => es.mapM (checkTerm sigs Γ R) = some ts) with
  | lit => simp [checkTerm, annotated]
  | «local» h => simp [checkTerm, annotated, h]
  | letE _ _ ha hb => simp [checkTerm, annotated, ha, hb]
  | letMut _ _ ha hb => simp [checkTerm, annotated, ha, hb]
  | assign hi _ ha => simp [checkTerm, annotated, hi, ha]
  | whileE _ _ hc hb => simp [checkTerm, annotated, hc, hb]
  | ifE _ _ _ hc ha hb => simp [checkTerm, annotated, hc, ha, hb]
  | unary _ ha => simp [checkTerm, annotated, ha]
  | binary _ _ hop ha hb => simp [checkTerm, annotated, ha, hb, hop]
  | call hf hv _ ha => simp [checkTerm, annotated, hf, hv, ha]
  | tuple _ ih =>
    simp only [checkTerm, ih, bind, Option.bind_some, APL.FlatProducts.scalarList_complete,
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
    obtain ⟨u, ha, h⟩ := h
    split at h
    next ht => cases h; subst u; exact .unary (ia ha)
    · contradiction
  | binary ann op a b ia ib =>
    rw [checkTerm, annotated_eq_some] at h
    obtain ⟨h, ht⟩ := h
    subst ann
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, v, hb, hop⟩ := h
    exact .binary (ia ha) (ib hb) hop
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
    rw [APL.FlatProducts.scalarList_sound hs, ← APL.FlatProducts.make_fields hm] at typed
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
  | «local» hi => exact .local (lookup_append hi)
  | letE _ _ ha hb => exact .letE ha hb
  | letMut _ _ ha hb => exact .letMut ha hb
  | assign hi _ ha => exact .assign (lookup_append hi) ha
  | whileE _ _ hc hb => exact .whileE hc hb
  | ifE _ _ _ hc ha hb => exact .ifE hc ha hb
  | unary _ ha => exact .unary ha
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

theorem read_cannot_write : ¬Mode.read.CanWrite := by simp [Mode.CanWrite]
theorem read_cannot_lend_edit : ¬Mode.read.CanLend .edit := by simp [Mode.CanLend, Mode.CanWrite]
theorem every_mode_lends_read (mode : Mode) : mode.CanLend .read := Or.inl rfl

structure Function.WellFormed (sigs : Signatures) (fn : Function) : Prop where
  name : ValidName fn.name
  sites : fn.body.CanonicalSites
  body : HasType sigs fn.valueContext fn.resourceContext fn.body fn.result

def checkFunction (sigs : Signatures) (fn : Function) : Bool :=
  decide (ValidName fn.name) && decide fn.body.CanonicalSites &&
    decide (checkTerm sigs fn.valueContext fn.resourceContext fn.body = some fn.result)

theorem checkFunction_iff : checkFunction sigs fn = true ↔ fn.WellFormed sigs := by
  simp only [checkFunction, Bool.and_eq_true, decide_eq_true_eq, checkTerm_iff]
  constructor
  · rintro ⟨⟨hn, hs⟩, hb⟩; exact ⟨hn, hs, hb⟩
  · intro h; exact ⟨⟨h.name, h.sites⟩, h.body⟩

def EntryValid (p : Program) : Prop :=
  ∃ fn, p.functions[p.entry]? = some fn ∧ fn.view = none ∧ fn.params = [] ∧ fn.result = .scalar .i64

def checkEntry (p : Program) : Bool :=
  match p.functions[p.entry]? with
  | none => false
  | some fn => decide (fn.view = none ∧ fn.params = [] ∧ fn.result = .scalar .i64)

theorem checkEntry_iff : checkEntry p = true ↔ EntryValid p := by
  cases h : p.functions[p.entry]? <;> simp [checkEntry, EntryValid, h]

structure WellFormedProgram (p : Program) : Prop where
  schema : p.schema = "anl-core-v3"
  revision : p.semanticRevision = "anl-owned-buffers-v1"
  profile : p.profile.Admissible
  ids : p.functions.toList.map Function.id = List.range p.functions.size
  names : (p.functions.toList.map Function.name).Nodup
  functions : ∀ fn ∈ p.functions.toList, fn.WellFormed p.signatures
  entry : EntryValid p

def checkProgram (p : Program) : Bool :=
  decide (p.schema = "anl-core-v3") &&
  decide (p.semanticRevision = "anl-owned-buffers-v1") &&
  decide p.profile.Admissible &&
  decide (p.functions.toList.map Function.id = List.range p.functions.size) &&
  decide (p.functions.toList.map Function.name).Nodup &&
  p.functions.toList.all (checkFunction p.signatures) && checkEntry p

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
      fn.result = .scalar .i64 ∧ HasType p.signatures [] [] fn.body (.scalar .i64) := by
  obtain ⟨fn, hf, hv, ha, ht⟩ := hp.entry
  have hb := (hp.function_at hf).body
  exact ⟨fn, hf, hv, ha, ht, by
    simpa [Function.valueContext, Function.resourceContext, APL.FlatProducts.immutable,
      viewContext, hv, ha, ht] using hb⟩

end ANL.Memory
