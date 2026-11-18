import ANL.BootReferenceAdmission
import ANL.BootSessionExecutedBounds

namespace ANL.Boot.Reference
open ANL.Boot.Runtime ANL.Boot.Runtime.Session

def readLimit : Nat := 65536
def originLimit : Nat := 128
def actionLimit : Nat := 32
def transitionLimit : Nat := 65536
abbrev wireNatMax := ANL.Memory.Wire.wireNatMax

structure Request where
  environment : Environment
  actions : List Action
  deriving Repr

def TailEdge (edge : Origin.Edge) : Prop := edge = .letValue ∨ edge = .letBody
instance (edge : Origin.Edge) : Decidable (TailEdge edge) := inferInstanceAs (Decidable (_ ∨ _))

def LandmarkForm : Landmark → Prop
  | .beforePrimitive k id | .afterPrimitive k id => 0 < k ∧ k ≤ wireNatMax ∧ id ≤ wireNatMax
  | .bootPark origin => origin.function ≤ wireNatMax ∧ ∀ edge ∈ origin.path, TailEdge edge

instance (key : Landmark) : Decidable (LandmarkForm key) := by
  cases key <;> unfold LandmarkForm <;> infer_instance

def deliveryEdges : Option Delivery → Nat
  | some ⟨.bootPark origin, _, _, _⟩ => origin.path.length
  | _ => 0

structure RequestScalars (request : Request) : Prop where
  budgets : ∀ a ∈ request.actions, a.budget ≤ wireNatMax
  delivery : ∀ d, request.environment.delivery = some d → LandmarkForm d.landmark

structure RequestLimits (request : Request) : Prop where
  reads : request.environment.reads.length ≤ readLimit
  origin : deliveryEdges request.environment.delivery ≤ originLimit
  actions : request.actions.length ≤ actionLimit
  eachBudget : ∀ a ∈ request.actions, a.budget ≤ transitionLimit
  totalBudget : budgets request.actions ≤ transitionLimit

structure RequestValid (p : Program) (request : Request) : Prop where
  scalars : RequestScalars request
  limits : RequestLimits request
  shape : ActionShape request.actions
  input : InputValid p request.environment

def checkScalars (request : Request) : Bool :=
  request.actions.all (fun a => decide (a.budget ≤ wireNatMax)) &&
    match request.environment.delivery with
    | none => true
    | some d => decide (LandmarkForm d.landmark)

def checkLimits (request : Request) : Bool :=
  decide (request.environment.reads.length ≤ readLimit ∧
    deliveryEdges request.environment.delivery ≤ originLimit ∧
    request.actions.length ≤ actionLimit) &&
  request.actions.all (fun a => decide (a.budget ≤ transitionLimit)) &&
  decide (budgets request.actions ≤ transitionLimit)

/-- Raw decoded validation. Scalar form precedes budgets; full static input checking is last and occurs once. -/
def checkRequest (p : Program) (request : Request) : Decode Request :=
  if !checkScalars request then .error (invalid "invalid reference request scalar")
  else if !checkLimits request then .error (limit "reference request structural or budget limit")
  else if !checkShape request.actions then .error (invalid "invalid reference action sequence")
  else if checkInput p request.environment then .ok request
  else .error (invalid "invalid reference environment or delivery scope")

theorem checkScalars_iff : checkScalars request = true ↔ RequestScalars request := by
  unfold checkScalars
  cases hd : request.environment.delivery with
  | none =>
    simp only [Bool.and_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h => ⟨h, by simp [hd]⟩, fun h => h.budgets⟩
  | some d =>
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h => ⟨h.1, by intro v hv; cases hd.symm.trans hv; exact h.2⟩,
      fun h => ⟨h.budgets, h.delivery d hd⟩⟩

theorem checkLimits_iff : checkLimits request = true ↔ RequestLimits request := by
  simp only [checkLimits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨fun ⟨⟨⟨reads, origin, actions⟩, each⟩, total⟩ => ⟨reads, origin, actions, each, total⟩,
    fun h => ⟨⟨⟨h.reads, h.origin, h.actions⟩, h.eachBudget⟩, h.totalBudget⟩⟩

theorem checkRequest_iff : checkRequest p request = .ok value ↔ request = value ∧ RequestValid p request := by
  unfold checkRequest
  by_cases scalars : checkScalars request = true
  · simp only [scalars, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases limits : checkLimits request = true
    · simp only [limits, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases shape : checkShape request.actions = true
      · simp only [shape, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases input : checkInput p request.environment = true
        · simp only [input, ↓reduceIte, Except.ok.injEq]
          exact ⟨fun h => ⟨h, ⟨checkScalars_iff.mp scalars, checkLimits_iff.mp limits,
            checkShape_iff.mp shape, checkInput_iff.mp input⟩⟩, fun h => h.1⟩
        · simp only [input, ↓reduceIte, reduceCtorEq, false_iff, not_and]
          exact fun _ h => input (checkInput_iff.mpr h.input)
      · simp only [shape, Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        exact fun _ h => shape (checkShape_iff.mpr h.shape)
    · simp only [limits, Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      exact fun _ h => limits (checkLimits_iff.mpr h.limits)
  · simp only [scalars, Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    exact fun _ h => scalars (checkScalars_iff.mpr h.scalars)

/-- Evidence is introduced only at the gateway; raw requests and runtime states remain proof-free. -/
def RequestValid.validatedInput (valid : RequestValid p request) : ValidatedInput p :=
  ⟨request.environment, valid.input⟩

theorem RequestValid.budgets (valid : RequestValid p request) :
    budgets request.actions ≤ 65536 ∧ request.actions.length ≤ 32 :=
  ⟨valid.limits.totalBudget, valid.limits.actions⟩

end ANL.Boot.Reference
