import ANL.BootOriginCore
import ANL.WordsRunProofs

namespace ANL.Boot.Origin
open ANL.Words

structure Metadata where
  control : Location
  frames : List Location
  deriving DecidableEq, Repr

/-- Captures precede the currently evaluated element; remaining terms follow it. -/
def Pending (all remaining : List Term) (captured : Nat) : Prop :=
  ∃ before current, all = before ++ current :: remaining ∧ before.length = captured

def DefinedTarget (p : Program) (f : Nat) : Prop :=
  f ∉ p.roleIDs ∧ match p.functions[f]? with
    | some (.defined _) => True
    | _ => False

instance : Decidable (DefinedTarget p f) := by
  unfold DefinedTarget
  split <;> infer_instance

inductive ControlAt (p : Program) (origin : Location) : Control → Prop where
  | eval : Located p origin e → ControlAt p origin (.eval e)
  | ret : Located p origin e → ControlAt p origin (.ret v)
  | invoke : Located p origin (.call t f args) → values.length = args.length →
      ControlAt p origin (.invoke f none values)
  | grant : Located p origin (.call t f args) → values.length = args.length →
      DefinedTarget p f → ControlAt p origin (.grant f none values)
  | revoke : Located p origin e → ControlAt p origin (.revoke v)
  | restore : Located p origin e → ControlAt p origin (.restore v)
  | trap : Located p origin e → ControlAt p origin (.trap kind)
  | invalid : Located p origin e → ControlAt p origin .invalid

/-- Parent occurrences are checked against actual pending frame contents. -/
inductive FrameAt (p : Program) : Nat → Location → Frame → Nat → Prop where
  | bind : Located p o (.letE t a b) →
      FrameAt p o.function o (.bind false b) o.function
  | bindMut : Located p o (.letMut t a b) →
      FrameAt p o.function o (.bind true b) o.function
  | scope : Located p o (.letE t a b) → FrameAt p o.function o .scope o.function
  | scopeMut : Located p o (.letMut t a b) → FrameAt p o.function o .scope o.function
  | assign : Located p o (.assign t i a) → FrameAt p o.function o (.assign i) o.function
  | branch : Located p o (.ifE t c y n) → FrameAt p o.function o (.ifF y n) o.function
  | convert : Located p o (.convert t mode target a) →
      FrameAt p o.function o (.convert mode target) o.function
  | unary : Located p o (.unary t op a) → FrameAt p o.function o (.unary op) o.function
  | left : Located p o (.binary t op a b) → FrameAt p o.function o (.left op b) o.function
  | right : Located p o (.binary t op a b) → FrameAt p o.function o (.right op value) o.function
  | arguments : Located p o (.call t f args) → Pending args remaining values.length →
      FrameAt p o.function o (.arguments f none remaining values) o.function
  | caller : Located p o (.call t f args) → caller.function = o.function → DefinedTarget p f →
      FrameAt p f o (.callReturn caller none) caller.function
  | condition : Located p o (.whileE t c b) → FrameAt p o.function o (.condition c b) o.function
  | body : Located p o (.whileE t c b) → FrameAt p o.function o (.body c b) o.function
  | fields : Located p o (.tuple t args) → Pending args remaining values.length →
      FrameAt p o.function o (.fields remaining values) o.function
  | project : Located p o (.project t a i) → FrameAt p o.function o (.project i) o.function

inductive StackAt (p : Program) : Nat → List Location → List Frame → Prop where
  | nil : StackAt p function [] []
  | cons : FrameAt p function origin frame outer → StackAt p outer origins frames →
      StackAt p function (origin :: origins) (frame :: frames)

structure Aligned (p : Program) (s : State) (metadata : Metadata) : Prop where
  function : metadata.control.function = s.current.function
  control : ControlAt p metadata.control s.control
  frames : StackAt p s.current.function metadata.frames s.kont

theorem ControlAt.located (h : ControlAt p origin ctl) : ∃ e, Located p origin e := by
  cases h <;> exact ⟨_, by assumption⟩

theorem FrameAt.located (h : FrameAt p function origin frame outer) : ∃ e, Located p origin e := by
  cases h <;> exact ⟨_, by assumption⟩

theorem FrameAt.outer_function (h : FrameAt p function origin frame outerFn) : origin.function = outerFn := by
  cases h <;> simp_all

theorem StackAt.length (h : StackAt p function origins frames) : origins.length = frames.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Aligned.current_defined (h : Aligned p s metadata) :
    ∃ d, p.functions[s.current.function]? = some (.defined d) := by
  obtain ⟨e, occurrence⟩ := h.control.located
  rw [← h.function]
  exact occurrence.function_defined

/-- Actual source controls that may be delegated to ordinary Words stepping. -/
def Admitted (p : Program) (s : State) : Prop :=
  match s.control with
  | .invoke f none _ | .grant f none _ => DefinedTarget p f
  | .invoke _ (some _) _ | .grant _ (some _) _ => False
  | .eval (.heap ..) | .eval (.bufferLength ..) | .eval (.bufferRead ..)
  | .eval (.bufferWrite ..) | .eval (.callView ..) => False
  | .lengthReady .. | .allocate .. | .readCheck .. | .readCell ..
  | .writeCheck .. | .store .. | .close .. => False
  | .ret _ => match s.kont with
      | .heapLength .. :: _ | .heapInitial .. :: _ | .owner .. :: _
      | .readIndex .. :: _ | .writeIndex .. :: _ | .writeValue .. :: _ => False
      | .callReturn _ (some _) :: _ => False
      | _ => True
  | .revoke _ | .restore _ => match s.kont with
      | .callReturn _ none :: _ => True
      | _ => False
  | _ => True

instance : Decidable (Admitted p s) := by
  unfold Admitted
  split <;> first | infer_instance | (split <;> infer_instance)

def checkAdmitted (p : Program) (s : State) : Bool := decide (Admitted p s)

theorem checkAdmitted_iff : checkAdmitted p s = true ↔ Admitted p s := by simp [checkAdmitted]

/-- The primitive invocation has an authored caller occurrence, but no authored body entry. -/
def PrimitiveFrontier (p : Program) (s : State) : Prop :=
  ∃ f values op, s.control = .invoke f none values ∧ p.functions[f]? = some (.primitive op)

theorem primitive_not_admitted (frontier : PrimitiveFrontier p s) : ¬ Admitted p s := by
  obtain ⟨f, values, op, control, found⟩ := frontier
  simp [Admitted, control, DefinedTarget, found]

theorem role_invoke_not_admitted (role : f ∈ p.roleIDs) :
    ¬ Admitted p ⟨.invoke f none values, a, k, w⟩ := by
  simp [Admitted, DefinedTarget, role]

theorem role_grant_not_admitted (role : f ∈ p.roleIDs) :
    ¬ Admitted p ⟨.grant f none values, a, k, w⟩ := by
  simp [Admitted, DefinedTarget, role]

theorem missing_grant_not_admitted (missing : p.functions[f]? = none) :
    ¬ Admitted p ⟨.grant f none values, a, k, w⟩ := by
  simp [Admitted, DefinedTarget, missing]

theorem primitive_grant_not_admitted (found : p.functions[f]? = some (.primitive op)) :
    ¬ Admitted p ⟨.grant f none values, a, k, w⟩ := by
  simp [Admitted, DefinedTarget, found]

end ANL.Boot.Origin
