import APL.FlatProductsTyping

namespace ANL.Memory

abbrev Ty := APL.FlatProducts.Ty
abbrev Val := APL.FlatProducts.Val
abbrev VCtx := APL.FlatProducts.Ctx

inductive Mode where
  | owner | read | edit
  deriving DecidableEq, Repr

inductive ViewMode where
  | read | edit
  deriving DecidableEq, Repr

def ViewMode.mode : ViewMode → Mode
  | .read => .read
  | .edit => .edit

def Mode.CanWrite (m : Mode) : Prop := m = .owner ∨ m = .edit
instance (m : Mode) : Decidable m.CanWrite := inferInstanceAs (Decidable (_ ∨ _))

def Mode.CanLend (m : Mode) (v : ViewMode) : Prop := v = .read ∨ m.CanWrite
instance (m : Mode) (v : ViewMode) : Decidable (m.CanLend v) :=
  inferInstanceAs (Decidable (_ ∨ _))

abbrev RCtx := List Mode

def viewContext : Option ViewMode → RCtx
  | none => []
  | some v => [v.mode]

structure Profile where
  abi : String
  charBits : Nat
  i64Bytes : Nat
  i64Align : Nat
  sizeBits : Nat
  ptrdiffBits : Nat
  deriving DecidableEq, Repr

def Profile.Admissible (p : Profile) : Prop :=
  p.abi = "anl-buffer-c11-v1" ∧ p.charBits = 8 ∧ p.i64Bytes = 8 ∧
  p.i64Align ∈ [1, 2, 4, 8, 16] ∧ p.sizeBits ∈ [32, 64] ∧ p.ptrdiffBits ∈ [32, 64]

instance (p : Profile) : Decidable p.Admissible := inferInstanceAs (Decidable (_ ∧ _))

def Profile.sizeMax (p : Profile) : Nat := 2 ^ p.sizeBits - 1
def Profile.ptrdiffMax (p : Profile) : Nat := 2 ^ (p.ptrdiffBits - 1) - 1
def Profile.maxCells (p : Profile) : Nat :=
  min (2 ^ 63 - 1) (min (p.sizeMax / 8) (p.ptrdiffMax / 8))

theorem Profile.maxCells_le_i64 (p : Profile) : p.maxCells ≤ 2 ^ 63 - 1 :=
  Nat.min_le_left _ _

theorem Profile.maxCells_le_size (p : Profile) : p.maxCells ≤ p.sizeMax / 8 :=
  Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

theorem Profile.maxCells_le_ptrdiff (p : Profile) : p.maxCells ≤ p.ptrdiffMax / 8 :=
  Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

structure Signature where
  view : Option ViewMode
  params : List Ty
  result : Ty
  deriving DecidableEq, Repr

abbrev Signatures := Array Signature

/-- Every node stores an unchecked ordinary type annotation. -/
inductive Term where
  | lit (ty : Ty) (value : APL.Val)
  | local (ty : Ty) (index : Nat)
  | letE (ty : Ty) (value body : Term)
  | letMut (ty : Ty) (value body : Term)
  | assign (ty : Ty) (index : Nat) (value : Term)
  | whileE (ty : Ty) (condition body : Term)
  | ifE (ty : Ty) (condition yes no : Term)
  | unary (ty : Ty) (op : APL.UOp) (operand : Term)
  | binary (ty : Ty) (op : APL.BOp) (left right : Term)
  | call (ty : Ty) (function : Nat) (arguments : List Term)
  | tuple (ty : Ty) (fields : List Term)
  | project (ty : Ty) (base : Term) (index : Nat)
  | heap (ty : Ty) (site : Nat) (length initial success failure : Term)
  | bufferLength (ty : Ty) (resource : Nat)
  | bufferRead (ty : Ty) (resource : Nat) (index : Term)
  | bufferWrite (ty : Ty) (resource : Nat) (index value : Term)
  | callView (ty : Ty) (function resource : Nat) (mode : ViewMode) (arguments : List Term)
  deriving Repr

def Term.ty : Term → Ty
  | .lit t _ | .local t _ | .letE t _ _ | .letMut t _ _ | .assign t _ _
  | .whileE t _ _ | .ifE t _ _ _ | .unary t _ _ | .binary t _ _ _
  | .call t _ _ | .tuple t _ | .project t _ _ | .heap t _ _ _ _ _
  | .bufferLength t _ | .bufferRead t _ _ | .bufferWrite t _ _ _
  | .callView t _ _ _ _ => t

def Term.heapSites : Term → List Nat
  | .lit _ _ | .local _ _ | .bufferLength _ _ => []
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b
  | .bufferWrite _ _ a b => a.heapSites ++ b.heapSites
  | .assign _ _ a | .unary _ _ a | .project _ a _ | .bufferRead _ _ a => a.heapSites
  | .ifE _ c a b => c.heapSites ++ a.heapSites ++ b.heapSites
  | .call _ _ args | .tuple _ args | .callView _ _ _ _ args =>
      args.flatMap Term.heapSites
  | .heap _ site len initial success failure =>
      site :: (len.heapSites ++ initial.heapSites ++ success.heapSites ++ failure.heapSites)

def Term.CanonicalSites (e : Term) : Prop := e.heapSites = List.range e.heapSites.length
instance (e : Term) : Decidable e.CanonicalSites := inferInstanceAs (Decidable (_ = _))

structure Function where
  id : Nat
  name : String
  view : Option ViewMode
  params : List Ty
  result : Ty
  body : Term
  deriving Repr

def Function.signature (f : Function) : Signature := ⟨f.view, f.params, f.result⟩
def Function.valueContext (f : Function) : VCtx := APL.FlatProducts.immutable f.params.reverse
def Function.resourceContext (f : Function) : RCtx := viewContext f.view

structure Program where
  schema : String
  semanticRevision : String
  profile : Profile
  functions : Array Function
  entry : Nat
  deriving Repr

def Program.signatures (p : Program) : Signatures := p.functions.map Function.signature

def NameStart (c : Char) : Prop := c = '_' ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')
instance (c : Char) : Decidable (NameStart c) := inferInstanceAs (Decidable (_ ∨ _))

def NameRest (c : Char) : Prop := NameStart c ∨ ('0' ≤ c ∧ c ≤ '9')
instance (c : Char) : Decidable (NameRest c) := inferInstanceAs (Decidable (_ ∨ _))

def ValidName (s : String) : Prop :=
  (match s.toList with
   | [] => False
   | first :: rest => NameStart first ∧ ∀ c ∈ rest, NameRest c) ∧
  s ∉ ["fn", "let", "if", "else", "true", "false", "i64", "bool", "unit"]

instance (s : String) : Decidable (ValidName s) := by
  unfold ValidName
  cases s.toList <;> infer_instance

def annotated (expected : Ty) (actual : Option Ty) : Option Ty :=
  match actual with
  | none => none
  | some found => if found = expected then some found else none

@[simp] theorem annotated_eq_some {expected result : Ty} {actual : Option Ty} :
    annotated expected actual = some result ↔ actual = some result ∧ expected = result := by
  cases actual with
  | none => simp [annotated]
  | some found =>
      by_cases h : found = expected
      · subst found; simp [annotated]
      · simp only [annotated, ite_eq_right h, reduceCtorEq, false_iff]
        rintro ⟨eq, he⟩
        cases eq
        exact h he.symm

def checkTerm (sigs : Signatures) (Γ : VCtx) (R : RCtx) : Term → Option Ty
  | .lit t v => annotated t (some (.scalar v.type))
  | .local t i => annotated t ((Γ[i]?).map Prod.fst)
  | .letE t a b => annotated t (do
      let u ← checkTerm sigs Γ R a
      checkTerm sigs ((u, false) :: Γ) R b)
  | .letMut t a b => annotated t (do
      let u ← checkTerm sigs Γ R a
      checkTerm sigs ((u, true) :: Γ) R b)
  | .assign t i a => annotated t (do
      let (u, permission) ← Γ[i]?
      let v ← checkTerm sigs Γ R a
      if permission = true ∧ v = u then some (.scalar .unit) else none)
  | .whileE t c b => annotated t (do
      let ct ← checkTerm sigs Γ R c
      let bt ← checkTerm sigs Γ R b
      if ct = .scalar .bool ∧ bt = .scalar .unit then some (.scalar .unit) else none)
  | .ifE t c a b => annotated t (do
      let ct ← checkTerm sigs Γ R c
      let ta ← checkTerm sigs Γ R a
      let tb ← checkTerm sigs Γ R b
      if ct = .scalar .bool ∧ ta = tb then some ta else none)
  | .unary t op a => annotated t (do
      let u ← checkTerm sigs Γ R a
      if u = .scalar op.input then some (.scalar op.output) else none)
  | .binary t op a b => annotated t (do
      let u ← checkTerm sigs Γ R a
      let v ← checkTerm sigs Γ R b
      APL.FlatProducts.binaryType op u v)
  | .call t f args => annotated t (do
      let fn ← sigs[f]?
      let actual ← args.mapM (checkTerm sigs Γ R)
      if fn.view = none ∧ actual = fn.params then some fn.result else none)
  | .tuple t fields => annotated t (do
      let types ← fields.mapM (checkTerm sigs Γ R)
      let scalars ← types.mapM APL.FlatProducts.Ty.asScalar
      let shape ← APL.FlatProducts.Flat.make scalars
      pure (.tuple shape))
  | .project t base index => annotated t (do
      let bt ← checkTerm sigs Γ R base
      match bt with
      | .scalar _ => none
      | .tuple shape => (shape.fields[index]?).map APL.FlatProducts.Ty.scalar)
  | .heap t _ len initial success failure => annotated t (do
      let lt ← checkTerm sigs Γ R len
      let it ← checkTerm sigs Γ R initial
      let st ← checkTerm sigs Γ (.owner :: R) success
      let ft ← checkTerm sigs Γ R failure
      if lt = .scalar .i64 ∧ it = .scalar .i64 ∧ st = ft then some st else none)
  | .bufferLength t r => annotated t (do
      let _ ← R[r]?
      pure (.scalar .i64))
  | .bufferRead t r index => annotated t (do
      let _ ← R[r]?
      let it ← checkTerm sigs Γ R index
      if it = .scalar .i64 then some (.scalar .i64) else none)
  | .bufferWrite t r index value => annotated t (do
      let mode ← R[r]?
      let it ← checkTerm sigs Γ R index
      let vt ← checkTerm sigs Γ R value
      if mode.CanWrite ∧ it = .scalar .i64 ∧ vt = .scalar .i64 then some (.scalar .unit) else none)
  | .callView t f r mode args => annotated t (do
      let fn ← sigs[f]?
      let source ← R[r]?
      let actual ← args.mapM (checkTerm sigs Γ R)
      if fn.view = some mode ∧ source.CanLend mode ∧ actual = fn.params then some fn.result else none)

end ANL.Memory
