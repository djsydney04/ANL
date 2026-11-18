import ANL.BootWireSafety

namespace ANL.Boot.Reference
open ANL.Words

abbrev Decode := ANL.Memory.Wire.Decode
abbrev invalid := ANL.Memory.Wire.invalid
abbrev limit := ANL.Memory.Wire.limit

def declarationLimit : Nat := 128
def nodeLimit : Nat := 8192
def arityLimit : Nat := 64

/-- Counts every raw node, including all children of statically forbidden memory forms. -/
def termNodes : Term → Nat
  | .lit _ _ | .word _ _ _ | .local _ _ | .bufferLength _ _ => 1
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _ | .bufferRead _ _ a =>
      1 + termNodes a
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b | .bufferWrite _ _ a b =>
      1 + termNodes a + termNodes b
  | .ifE _ c a b => 1 + termNodes c + termNodes a + termNodes b
  | .heap _ _ len initial yes no => 1 + termNodes len + termNodes initial + termNodes yes + termNodes no
  | .call _ _ args | .callView _ _ _ _ args | .tuple _ args => 1 + (args.map termNodes).sum

/-- Ordinary argument-vector sizes throughout the full raw tree. Tuple fields are not call arguments. -/
def callArities : Term → List Nat
  | .lit _ _ | .word _ _ _ | .local _ _ | .bufferLength _ _ => []
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _ | .bufferRead _ _ a => callArities a
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b | .bufferWrite _ _ a b =>
      callArities a ++ callArities b
  | .ifE _ c a b => callArities c ++ callArities a ++ callArities b
  | .heap _ _ len initial yes no => callArities len ++ callArities initial ++ callArities yes ++ callArities no
  | .call _ _ args | .callView _ _ _ _ args => args.length :: args.flatMap callArities
  | .tuple _ args => args.flatMap callArities

def programNodes (p : Program) : Nat := (p.defined.map (fun d => termNodes d.function.body)).sum

structure ReferenceAdmissible (p : Program) : Prop where
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
    if checkProgram p then .ok p else .error (invalid "boot Core static policy rejected")
  else .error (limit "reference Core structural limit")

def checkCoreDocument (text : String) : Decode Program := do
  admitCore (← Wire.readCore text)

theorem checkAdmission_iff : checkAdmission p = true ↔ ReferenceAdmissible p := by
  simp only [checkAdmission, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨decls, nodes⟩, bodies⟩
    exact ⟨decls, nodes, fun d hd => (bodies d hd).1, fun d hd => (bodies d hd).2⟩
  · intro h
    exact ⟨⟨h.declarations, h.nodes⟩, fun d hd => ⟨h.parameters d hd, h.arguments d hd⟩⟩

theorem admitCore_iff : admitCore p = .ok q ↔ p = q ∧ ReferenceAdmissible p ∧ WellFormedProgram p := by
  unfold admitCore
  by_cases admission : checkAdmission p = true
  · simp only [admission, ↓reduceIte]
    by_cases checked : checkProgram p = true
    · simp [checked, checkAdmission_iff.mp admission, checkProgram_iff.mp checked]
    · simp [checked, show ¬ WellFormedProgram p from fun h => checked (checkProgram_iff.mpr h)]
  · simp [admission, show ¬ ReferenceAdmissible p from fun h => admission (checkAdmission_iff.mpr h)]

theorem checkCoreDocument_iff : checkCoreDocument text = .ok p ↔
    Wire.checkCoreDocument text = .ok p ∧ ReferenceAdmissible p := by
  unfold checkCoreDocument
  cases raw : Wire.readCore text with
  | error e => simp [bind, Except.bind, Wire.checkCoreDocument, raw]
  | ok q =>
    simp only [bind, Except.bind, admitCore_iff, Wire.checkCoreDocument_iff, raw, Except.ok.injEq]
    constructor
    · rintro ⟨rfl, admitted, checked⟩; exact ⟨⟨rfl, checked⟩, admitted⟩
    · rintro ⟨⟨rfl, checked⟩, admitted⟩; exact ⟨rfl, admitted, checked⟩

theorem admission_precedes_static (rejected : ¬ ReferenceAdmissible p) :
    admitCore p = .error (limit "reference Core structural limit") := by
  have h : checkAdmission p = false := Bool.eq_false_iff.mpr (fun h => rejected (checkAdmission_iff.mp h))
  simp [admitCore, h]

end ANL.Boot.Reference
