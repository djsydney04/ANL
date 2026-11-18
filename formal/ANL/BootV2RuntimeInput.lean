import ANL.BootV2RuntimeCore
import ANL.BootV2FaultProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Landmark Delivery wordModulus byteModulus Hardware)
set_option linter.unusedSimpArgs false

/-- Before cuts name any actual primitive; after cuts name only legacy operations. -/
inductive Scoped (p : Program) : Landmark → Prop where
  | before : 0 < k → p.functions[ident]? = some (.primitive row) →
      Scoped p (.beforePrimitive k ident)
  | after : 0 < k → p.functions[ident]? = some (.primitive row) →
      row.operation = .legacy op → Scoped p (.afterPrimitive k ident)
  | park : p.functions[p.entries.boot.function]? = some (.defined d) →
      designatedTail d.function.body = some path →
      Scoped p (.bootPark ⟨p.entries.boot.function, ANL.Boot.Origin.tailPath path⟩)

def checkScoped (p : Program) : Landmark → Bool
  | .beforePrimitive k ident =>
      decide (0 < k) && match p.functions[ident]? with
        | some (.primitive _) => true
        | _ => false
  | .afterPrimitive k ident =>
      decide (0 < k) && match p.functions[ident]? with
        | some (.primitive row) => match row.operation with
            | .legacy _ => true
            | .illegalInstruction _ => false
        | _ => false
  | .bootPark origin => match p.functions[p.entries.boot.function]? with
      | some (.defined d) => match designatedTail d.function.body with
          | some path => decide (origin = ⟨p.entries.boot.function, ANL.Boot.Origin.tailPath path⟩)
          | none => false
      | _ => false

structure DeliveryValid (p : Program) (d : Delivery) : Prop where
  scope : Scoped p d.landmark
  cause : d.scause < wordModulus
  pc : d.sepc < wordModulus
  auxiliary : d.stval < wordModulus

structure InputValid (p : Program) (env : Environment) : Prop where
  status : env.legacy.sstatus < wordModulus
  interrupts : env.legacy.sie < wordModulus
  hart : env.legacy.hart < wordModulus
  opaqueDtb : env.legacy.opaqueDtb < wordModulus
  reads : ∀ value ∈ env.legacy.reads, value < byteModulus
  delivery : ∀ d, env.legacy.delivery = some d → DeliveryValid p d
  fault : Fault.InputValid p env.fault

def checkDelivery (p : Program) (d : Delivery) : Bool :=
  checkScoped p d.landmark && decide (d.scause < wordModulus ∧ d.sepc < wordModulus ∧ d.stval < wordModulus)

def checkInput (p : Program) (env : Environment) : Bool :=
  decide (env.legacy.sstatus < wordModulus ∧ env.legacy.sie < wordModulus ∧
    env.legacy.hart < wordModulus ∧ env.legacy.opaqueDtb < wordModulus) &&
  env.legacy.reads.all (fun value => decide (value < byteModulus)) &&
  (match env.legacy.delivery with | none => true | some d => checkDelivery p d) &&
  Fault.checkInput p env.fault

/-- Constructed once by input admission; raw Environment and State stay proof-free. -/
structure ValidatedInput (p : Program) where
  raw : Environment
  valid : InputValid p raw

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
        | primitive row =>
          cases operation : row.operation with
          | legacy op => exact .after h.1 found operation
          | illegalInstruction authority => simp [found, operation] at h
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
            have eq : origin = ⟨p.entries.boot.function, ANL.Boot.Origin.tailPath path⟩ := by
              simpa [found, selected] using h
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
  simp only [checkInput, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Fault.checkInput_iff]
  cases selected : env.legacy.delivery with
  | none =>
    simp only [selected, and_true]
    constructor
    · rintro ⟨⟨⟨status, interrupts, hart, dtb⟩, reads⟩, fault⟩
      exact ⟨status, interrupts, hart, dtb, reads, fun d eq => by simp [selected] at eq, fault⟩
    · intro h; exact ⟨⟨⟨h.status, h.interrupts, h.hart, h.opaqueDtb⟩, h.reads⟩, h.fault⟩
  | some d =>
    simp only [selected, checkDelivery_iff]
    constructor
    · rintro ⟨⟨⟨⟨status, interrupts, hart, dtb⟩, reads⟩, delivery⟩, fault⟩
      exact ⟨status, interrupts, hart, dtb, reads, fun actual eq => by
        have same : d = actual := Option.some.inj (selected.symm.trans eq)
        subst actual; exact delivery, fault⟩
    · intro h
      exact ⟨⟨⟨⟨h.status, h.interrupts, h.hart, h.opaqueDtb⟩, h.reads⟩, h.delivery d selected⟩, h.fault⟩

def validateInput (p : Program) (env : Environment) : Option (ValidatedInput p) :=
  if h : checkInput p env = true then some ⟨env, checkInput_iff.mp h⟩ else none

theorem validateInput_some_iff : (validateInput p env).isSome = true ↔ InputValid p env := by
  simp [validateInput, checkInput_iff]

theorem validateInput_raw (h : validateInput p env = some checked) : checked.raw = env := by
  unfold validateInput at h
  split at h <;> simp_all
  cases h; rfl

theorem InputValid.initialHardware (h : InputValid p env) :
    Hardware.Valid ⟨env.legacy.sstatus, env.legacy.sie, none⟩ := ⟨h.status, h.interrupts⟩

theorem InputValid.read_bound {i : Nat} (h : InputValid p env) (found : env.legacy.reads[i]? = some value) :
    value < byteModulus := h.reads value (List.mem_of_getElem? found)

theorem Scoped.after_operation (h : Scoped p (.afterPrimitive k ident)) :
    ∃ op, p.operationAt ident = some (.legacy op) := by
  cases h with
  | after positive found operation =>
    rename_i row op
    exact ⟨op, by simp [Program.operationAt, found, operation]⟩

theorem illegal_after_not_scoped (illegal : p.operationAt ident = some (.illegalInstruction authority)) :
    ¬ Scoped p (.afterPrimitive k ident) := by
  intro hScoped
  obtain ⟨op, actual⟩ := hScoped.after_operation
  rw [illegal] at actual
  cases actual

theorem InputValid.illegal_slot (h : InputValid p env)
    (site : env.fault.illegalSitePc = some pc) : Fault.SiteValid p pc := h.fault.site pc site

end ANL.Boot.V2.Runtime
