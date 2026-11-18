import ANL.BootRuntimeInput

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem languageTag_iff : languageTag trap = some tag ↔ LanguageTag trap tag := by
  constructor
  · cases trap <;> simp only [languageTag, Option.some.injEq, reduceCtorEq]
    all_goals intro h; cases h <;> constructor
  · intro h; cases h <;> rfl

 theorem checkScoped_iff : checkScoped p key = true ↔ Scoped p key := by
  constructor
  · intro h
    cases key with
    | beforePrimitive k ident =>
      simp only [checkScoped, Bool.and_eq_true, decide_eq_true_eq] at h
      cases found : p.functions[ident]? with
      | none => simp [found] at h
      | some row =>
        cases row with
        | defined d => simp [found] at h
        | primitive row => exact .before h.1 found
    | afterPrimitive k ident =>
      simp only [checkScoped, Bool.and_eq_true, decide_eq_true_eq] at h
      cases found : p.functions[ident]? with
      | none => simp [found] at h
      | some row =>
        cases row with
        | defined d => simp [found] at h
        | primitive row => exact .after h.1 found
    | bootPark origin =>
      simp only [checkScoped] at h
      cases found : p.functions[p.entries.boot.function]? with
      | none => simp [found] at h
      | some row =>
        cases row with
        | primitive op => simp [found] at h
        | defined d =>
          cases selected : designatedTail d.function.body with
          | none => simp [found, selected] at h
          | some path =>
            have eq : origin = ⟨p.entries.boot.function, Origin.tailPath path⟩ := by simpa [found, selected] using h
            subst origin
            exact .park found selected
  · intro h
    cases h <;> simp_all [checkScoped]

 theorem checkDelivery_iff : checkDelivery p d = true ↔ DeliveryValid p d := by
  simp only [checkDelivery, Bool.and_eq_true, checkScoped_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨scope, cause, pc, aux⟩; exact ⟨scope, cause, pc, aux⟩
  · intro h; exact ⟨h.scope, h.cause, h.pc, h.auxiliary⟩

 theorem checkInput_iff : checkInput p env = true ↔ InputValid p env := by
  simp only [checkInput, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  cases selected : env.delivery with
  | none =>
    simp only [selected, and_true]
    constructor
    · rintro ⟨⟨status, interrupts, hart, dtb⟩, reads⟩
      exact ⟨status, interrupts, hart, dtb, reads, fun d eq => by simp [selected] at eq⟩
    · intro h; exact ⟨⟨h.status, h.interrupts, h.hart, h.opaqueDtb⟩, h.reads⟩
  | some d =>
    simp only [selected, checkDelivery_iff]
    constructor
    · rintro ⟨⟨⟨status, interrupts, hart, dtb⟩, reads⟩, delivery⟩
      exact ⟨status, interrupts, hart, dtb, reads, fun actual eq => by
        have same : d = actual := Option.some.inj (selected.symm.trans eq)
        subst actual; exact delivery⟩
    · intro h
      exact ⟨⟨⟨h.status, h.interrupts, h.hart, h.opaqueDtb⟩, h.reads⟩, h.delivery d selected⟩

/-- This gateway is called once, before the stepping API receives its immutable input handle. -/
def validateInput (p : ANL.Boot.Program) (env : Environment) : Option (ValidatedInput p) :=
  if h : checkInput p env = true then some ⟨env, checkInput_iff.mp h⟩ else none

 theorem validateInput_some_iff : (validateInput p env).isSome = true ↔ InputValid p env := by
  simp [validateInput, checkInput_iff]

 theorem validateInput_raw (h : validateInput p env = some checked) : checked.raw = env := by
  unfold validateInput at h
  split at h <;> simp_all
  cases h; rfl

 theorem InputValid.initialHardware (h : InputValid p env) :
    Hardware.Valid ⟨env.sstatus, env.sie, none⟩ := ⟨h.status, h.interrupts⟩

 theorem InputValid.read_bound {i : Nat} (h : InputValid p env) (found : env.reads[i]? = some value) :
    value < byteModulus := h.reads value (List.mem_of_getElem? found)

 theorem InputValid.delivery_valid (h : InputValid p env) (found : env.delivery = some d) : DeliveryValid p d :=
  h.delivery d found

 theorem Scoped.primitive_id (h : Scoped p (.beforePrimitive k ident) ∨ Scoped p (.afterPrimitive k ident)) :
    0 < k ∧ ∃ row, p.functions[ident]? = some (.primitive row) := by
  rcases h with h | h <;> cases h <;> exact ⟨by assumption, _, by assumption⟩

end ANL.Boot.Runtime
