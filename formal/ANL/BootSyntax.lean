import ANL.BootCore

namespace ANL.Boot

open ANL.Words

/-- Preorder includes dead branches and records a call before its argument calls. -/
def calls : Term → List Nat
  | .lit _ _ | .word _ _ _ | .local _ _ | .bufferLength _ _ => []
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _
  | .bufferRead _ _ a => calls a
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b
  | .bufferWrite _ _ a b => calls a ++ calls b
  | .ifE _ c a b => calls c ++ calls a ++ calls b
  | .call _ f args | .callView _ f _ _ args => f :: args.flatMap calls
  | .tuple _ fields => fields.flatMap calls
  | .heap _ _ len initial success failure =>
    calls len ++ calls initial ++ calls success ++ calls failure

/-- The mathematical profile excludes every memory constructor, not only executed ones. -/
def MemoryFree : Term → Prop
  | .lit _ _ | .word _ _ _ | .local _ _ => True
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _ => MemoryFree a
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b => MemoryFree a ∧ MemoryFree b
  | .ifE _ c a b => MemoryFree c ∧ MemoryFree a ∧ MemoryFree b
  | .call _ _ args | .tuple _ args => ∀ a ∈ args, MemoryFree a
  | .heap .. | .bufferLength .. | .bufferRead .. | .bufferWrite .. | .callView .. => False

def checkMemoryFree : Term → Bool
  | .lit _ _ | .word _ _ _ | .local _ _ => true
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _ => checkMemoryFree a
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b => checkMemoryFree a && checkMemoryFree b
  | .ifE _ c a b => checkMemoryFree c && checkMemoryFree a && checkMemoryFree b
  | .call _ _ args | .tuple _ args => args.all checkMemoryFree
  | .heap .. | .bufferLength .. | .bufferRead .. | .bufferWrite .. | .callView .. => false

theorem checkMemoryFree_iff : checkMemoryFree e = true ↔ MemoryFree e := by
  induction e using Term.rec
    (motive_2 := fun es => es.all checkMemoryFree = true ↔ ∀ e ∈ es, MemoryFree e) <;>
    simp_all [checkMemoryFree, MemoryFree, List.all_cons, Bool.and_eq_true, and_assoc]

theorem MemoryFree.no_sites (h : MemoryFree e) : e.heapSites = [] := by
  induction e using Term.rec
    (motive_2 := fun es => (∀ e ∈ es, MemoryFree e) → es.flatMap Term.heapSites = []) <;>
    simp_all [MemoryFree, Term.heapSites]

def park : Term := .whileE unitTy (.lit boolTy (.bool true)) (.lit unitTy .unit)

def handler : Term := .letE unitTy park (.lit unitTy .unit)

def isPark : Term → Bool
  | .whileE t (.lit c (.bool true)) (.lit b .unit) => decide (t = unitTy ∧ c = boolTy ∧ b = unitTy)
  | _ => false

def isHandler : Term → Bool
  | .letE t a (.lit b .unit) => decide (t = unitTy ∧ b = unitTy) && isPark a
  | _ => false

inductive TailEdge where
  | value | body
  deriving DecidableEq, Repr

abbrev TailPath := List TailEdge

/-- Initializer priority is part of the executable origin selection. -/
def designatedTail (e : Term) : Option TailPath :=
  if isPark e then some []
  else match e with
  | .letE _ a b | .letMut _ a b =>
    match designatedTail a with
    | some path => some (.value :: path)
    | none => (designatedTail b).map (.body :: ·)
  | _ => none

inductive HasTail : Term → Prop where
  | park : HasTail park
  | letValue : HasTail a → HasTail (.letE t a b)
  | letBody : HasTail b → HasTail (.letE t a b)
  | mutValue : HasTail a → HasTail (.letMut t a b)
  | mutBody : HasTail b → HasTail (.letMut t a b)

inductive SelectedTail : Term → TailPath → Prop where
  | park : SelectedTail park []
  | letValue : SelectedTail a path → SelectedTail (.letE t a b) (.value :: path)
  | letBody : ¬ HasTail a → SelectedTail b path → SelectedTail (.letE t a b) (.body :: path)
  | mutValue : SelectedTail a path → SelectedTail (.letMut t a b) (.value :: path)
  | mutBody : ¬ HasTail a → SelectedTail b path → SelectedTail (.letMut t a b) (.body :: path)

/-- Typing includes unreachable children; the tail evidence carries no runtime oracle. -/
structure NoNormalReturn (sigs : Signatures) (Γ : VCtx) (R : RCtx) (e : Term) (t : Ty) : Prop where
  typed : HasType sigs Γ R e t
  tail : HasTail e

end ANL.Boot
