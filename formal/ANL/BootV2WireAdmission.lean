import ANL.BootV2WireSafety
import ANL.BootReferenceAdmission

namespace ANL.Boot.V2.Wire.Admission

abbrev declarationLimit := ANL.Boot.Reference.declarationLimit
abbrev nodeLimit := ANL.Boot.Reference.nodeLimit
abbrev arityLimit := ANL.Boot.Reference.arityLimit
abbrev termNodes := ANL.Boot.Reference.termNodes
abbrev callArities := ANL.Boot.Reference.callArities

def programNodes (p : Program) : Nat :=
  (p.defined.map (fun d => termNodes d.function.body)).sum

/-- A private probe subset, separate from the v2 semantic judgment. -/
structure Admissible (p : Program) : Prop where
  declarations : p.functions.length ≤ declarationLimit
  nodes : programNodes p ≤ nodeLimit
  parameters : ∀ d ∈ p.defined, d.function.params.length ≤ arityLimit
  arguments : ∀ d ∈ p.defined, ∀ n ∈ callArities d.function.body, n ≤ arityLimit

def checkAdmission (p : Program) : Bool :=
  decide (p.functions.length ≤ declarationLimit) && decide (programNodes p ≤ nodeLimit) &&
  p.defined.all (fun d => decide (d.function.params.length ≤ arityLimit) &&
    (callArities d.function.body).all (fun n => decide (n ≤ arityLimit)))

def admitCore (p : Program) : Decode Program :=
  if checkAdmission p then
    if checkProgram p then .ok p else .error (invalid "v2 boot Core static policy rejected")
  else .error (ANL.Memory.Wire.limit "v2 probe Core structural limit")

def checkProbeDocument (text : String) : Decode Program := do
  admitCore (← readCore text)

theorem checkAdmission_iff : checkAdmission p = true ↔ Admissible p := by
  simp only [checkAdmission, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨decls, nodes⟩, bodies⟩
    exact ⟨decls, nodes, fun d hd => (bodies d hd).1, fun d hd => (bodies d hd).2⟩
  · intro h
    exact ⟨⟨h.declarations, h.nodes⟩, fun d hd => ⟨h.parameters d hd, h.arguments d hd⟩⟩

theorem admitCore_iff : admitCore p = .ok q ↔ p = q ∧ Admissible p ∧ WellFormedProgram p := by
  unfold admitCore
  by_cases admission : checkAdmission p = true
  · simp only [admission, ↓reduceIte]
    by_cases checked : checkProgram p = true
    · simp [checked, checkAdmission_iff.mp admission, checkProgram_iff.mp checked]
    · simp [checked, show ¬ WellFormedProgram p from fun h => checked (checkProgram_iff.mpr h)]
  · simp [admission, show ¬ Admissible p from fun h => admission (checkAdmission_iff.mpr h)]

theorem checkProbeDocument_iff : checkProbeDocument text = .ok p ↔
    checkCoreDocument text = .ok p ∧ Admissible p := by
  unfold checkProbeDocument
  cases raw : readCore text with
  | error e => simp [bind, Except.bind, checkCoreDocument, raw]
  | ok q =>
    simp only [bind, Except.bind, admitCore_iff, checkCoreDocument_iff, raw, Except.ok.injEq]
    constructor
    · rintro ⟨rfl, admitted, checked⟩; exact ⟨⟨rfl, checked⟩, admitted⟩
    · rintro ⟨⟨rfl, checked⟩, admitted⟩; exact ⟨rfl, admitted, checked⟩

theorem admission_precedes_static (rejected : ¬ Admissible p) :
    admitCore p = .error (ANL.Memory.Wire.limit "v2 probe Core structural limit") := by
  have h : checkAdmission p = false := Bool.eq_false_iff.mpr (fun h => rejected (checkAdmission_iff.mp h))
  simp [admitCore, h]

end ANL.Boot.V2.Wire.Admission
