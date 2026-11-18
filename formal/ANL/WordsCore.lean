import ANL.WordsValues
import ANL.MemoryCore

namespace ANL.Words

abbrev Mode := ANL.Memory.Mode
abbrev ViewMode := ANL.Memory.ViewMode
abbrev Profile := ANL.Memory.Profile
abbrev RCtx := ANL.Memory.RCtx
abbrev viewContext := ANL.Memory.viewContext

structure Signature where
  view : Option ViewMode
  params : List Ty
  result : Ty
  deriving DecidableEq, Repr

abbrev Signatures := Array Signature

/-- Every node stores an unchecked ordinary type annotation. -/
inductive Term where
  | lit (ty : Ty) (value : APL.Val)
  | word (ty : Ty) (width value : Nat)
  | convert (ty : Ty) (mode : ConvertMode) (target : ScalarTy) (operand : Term)
  | local (ty : Ty) (index : Nat)
  | letE (ty : Ty) (value body : Term)
  | letMut (ty : Ty) (value body : Term)
  | assign (ty : Ty) (index : Nat) (value : Term)
  | whileE (ty : Ty) (condition body : Term)
  | ifE (ty : Ty) (condition yes no : Term)
  | unary (ty : Ty) (op : UOp) (operand : Term)
  | binary (ty : Ty) (op : BOp) (left right : Term)
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
  | .word t _ _ | .convert t _ _ _ | .lit t _ | .local t _ | .letE t _ _ | .letMut t _ _ | .assign t _ _
  | .whileE t _ _ | .ifE t _ _ _ | .unary t _ _ | .binary t _ _ _
  | .call t _ _ | .tuple t _ | .project t _ _ | .heap t _ _ _ _ _
  | .bufferLength t _ | .bufferRead t _ _ | .bufferWrite t _ _ _
  | .callView t _ _ _ _ => t

def Term.heapSites : Term → List Nat
  | .word _ _ _ | .lit _ _ | .local _ _ | .bufferLength _ _ => []
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b
  | .bufferWrite _ _ a b => a.heapSites ++ b.heapSites
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _ | .bufferRead _ _ a => a.heapSites
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
def Function.valueContext (f : Function) : VCtx := immutable f.params.reverse
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
  | .lit t v => annotated t (some (.scalar (.legacy v.type)))
  | .word t width value => annotated t (wordLiteralType width value)
  | .convert t mode target operand => annotated t (do
      let source ← checkTerm sigs Γ R operand
      convertType mode target source)
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
      if permission = true ∧ v = u then some (.scalar (.legacy .unit)) else none)
  | .whileE t c b => annotated t (do
      let ct ← checkTerm sigs Γ R c
      let bt ← checkTerm sigs Γ R b
      if ct = .scalar (.legacy .bool) ∧ bt = .scalar (.legacy .unit) then some (.scalar (.legacy .unit)) else none)
  | .ifE t c a b => annotated t (do
      let ct ← checkTerm sigs Γ R c
      let ta ← checkTerm sigs Γ R a
      let tb ← checkTerm sigs Γ R b
      if ct = .scalar (.legacy .bool) ∧ ta = tb then some ta else none)
  | .unary t op a => annotated t (do
      let u ← checkTerm sigs Γ R a
      unaryType op u)
  | .binary t op a b => annotated t (do
      let u ← checkTerm sigs Γ R a
      let v ← checkTerm sigs Γ R b
      binaryType op u v)
  | .call t f args => annotated t (do
      let fn ← sigs[f]?
      let actual ← args.mapM (checkTerm sigs Γ R)
      if fn.view = none ∧ actual = fn.params then some fn.result else none)
  | .tuple t fields => annotated t (do
      let types ← fields.mapM (checkTerm sigs Γ R)
      let scalars ← types.mapM Ty.asScalar
      let shape ← APL.FlatProducts.Flat.make scalars
      pure (.tuple shape))
  | .project t base index => annotated t (do
      let bt ← checkTerm sigs Γ R base
      match bt with
      | .scalar _ => none
      | .tuple shape => (shape.fields[index]?).map Ty.scalar)
  | .heap t _ len initial success failure => annotated t (do
      let lt ← checkTerm sigs Γ R len
      let it ← checkTerm sigs Γ R initial
      let st ← checkTerm sigs Γ (.owner :: R) success
      let ft ← checkTerm sigs Γ R failure
      if lt = .scalar (.legacy .i64) ∧ it = .scalar (.legacy .i64) ∧ st = ft then some st else none)
  | .bufferLength t r => annotated t (do
      let _ ← R[r]?
      pure (.scalar (.legacy .i64)))
  | .bufferRead t r index => annotated t (do
      let _ ← R[r]?
      let it ← checkTerm sigs Γ R index
      if it = .scalar (.legacy .i64) then some (.scalar (.legacy .i64)) else none)
  | .bufferWrite t r index value => annotated t (do
      let mode ← R[r]?
      let it ← checkTerm sigs Γ R index
      let vt ← checkTerm sigs Γ R value
      if mode.CanWrite ∧ it = .scalar (.legacy .i64) ∧ vt = .scalar (.legacy .i64) then some (.scalar (.legacy .unit)) else none)
  | .callView t f r mode args => annotated t (do
      let fn ← sigs[f]?
      let source ← R[r]?
      let actual ← args.mapM (checkTerm sigs Γ R)
      if fn.view = some mode ∧ source.CanLend mode ∧ actual = fn.params then some fn.result else none)

mutual
  inductive HasType (sigs : Signatures) : VCtx → RCtx → Term → Ty → Prop where
    | lit : HasType sigs Γ R (.lit (.scalar (.legacy v.type)) v) (.scalar (.legacy v.type))
    | word : WordLiteralSig width value t → HasType sigs Γ R (.word t width value) t
    | convert : HasType sigs Γ R operand source → ConvertSig mode target source t →
        HasType sigs Γ R (.convert t mode target operand) t
    | local : Γ[i]? = some (t, permission) → HasType sigs Γ R (.local t i) t
    | letE : HasType sigs Γ R a u → HasType sigs ((u, false) :: Γ) R b t →
        HasType sigs Γ R (.letE t a b) t
    | letMut : HasType sigs Γ R a u → HasType sigs ((u, true) :: Γ) R b t →
        HasType sigs Γ R (.letMut t a b) t
    | assign : Γ[i]? = some (t, true) → HasType sigs Γ R a t →
        HasType sigs Γ R (.assign (.scalar (.legacy .unit)) i a) (.scalar (.legacy .unit))
    | whileE : HasType sigs Γ R c (.scalar (.legacy .bool)) → HasType sigs Γ R b (.scalar (.legacy .unit)) →
        HasType sigs Γ R (.whileE (.scalar (.legacy .unit)) c b) (.scalar (.legacy .unit))
    | ifE : HasType sigs Γ R c (.scalar (.legacy .bool)) → HasType sigs Γ R a t → HasType sigs Γ R b t →
        HasType sigs Γ R (.ifE t c a b) t
    | unary : HasType sigs Γ R a u → UnarySig op u t →
        HasType sigs Γ R (.unary t op a) t
    | binary : HasType sigs Γ R a u → HasType sigs Γ R b v →
        BinarySig op u v t → HasType sigs Γ R (.binary t op a b) t
    | call : sigs[f]? = some fn → fn.view = none → ArgsTyped sigs Γ R args fn.params →
        HasType sigs Γ R (.call fn.result f args) fn.result
    | tuple : ArgsTyped sigs Γ R fields (shape.fields.map Ty.scalar) →
        HasType sigs Γ R (.tuple (.tuple shape) fields) (.tuple shape)
    | project : HasType sigs Γ R base (.tuple shape) → shape.fields[index]? = some t →
        HasType sigs Γ R (.project (.scalar t) base index) (.scalar t)
    | heap : HasType sigs Γ R len (.scalar (.legacy .i64)) → HasType sigs Γ R initial (.scalar (.legacy .i64)) →
        HasType sigs Γ (.owner :: R) success t → HasType sigs Γ R failed t →
        HasType sigs Γ R (.heap t site len initial success failed) t
    | bufferLength : R[r]? = some mode →
        HasType sigs Γ R (.bufferLength (.scalar (.legacy .i64)) r) (.scalar (.legacy .i64))
    | bufferRead : R[r]? = some mode → HasType sigs Γ R index (.scalar (.legacy .i64)) →
        HasType sigs Γ R (.bufferRead (.scalar (.legacy .i64)) r index) (.scalar (.legacy .i64))
    | bufferWrite : R[r]? = some mode → mode.CanWrite →
        HasType sigs Γ R index (.scalar (.legacy .i64)) → HasType sigs Γ R value (.scalar (.legacy .i64)) →
        HasType sigs Γ R (.bufferWrite (.scalar (.legacy .unit)) r index value) (.scalar (.legacy .unit))
    | callView : sigs[f]? = some fn → fn.view = some mode → R[r]? = some source →
        source.CanLend mode → ArgsTyped sigs Γ R args fn.params →
        HasType sigs Γ R (.callView fn.result f r mode args) fn.result
  inductive ArgsTyped (sigs : Signatures) : VCtx → RCtx → List Term → List Ty → Prop where
    | nil : ArgsTyped sigs Γ R [] []
    | cons : HasType sigs Γ R e t → ArgsTyped sigs Γ R es ts →
        ArgsTyped sigs Γ R (e :: es) (t :: ts)
end

structure Function.WellFormed (sigs : Signatures) (fn : Function) : Prop where
  name : ValidName fn.name
  sites : fn.body.CanonicalSites
  body : HasType sigs fn.valueContext fn.resourceContext fn.body fn.result

def checkFunction (sigs : Signatures) (fn : Function) : Bool :=
  decide (ValidName fn.name) && decide fn.body.CanonicalSites &&
    decide (checkTerm sigs fn.valueContext fn.resourceContext fn.body = some fn.result)

def EntryValid (p : Program) : Prop :=
  ∃ fn, p.functions[p.entry]? = some fn ∧ fn.view = none ∧ fn.params = [] ∧ fn.result = .scalar (.legacy .i64)

def checkEntry (p : Program) : Bool :=
  match p.functions[p.entry]? with
  | none => false
  | some fn => decide (fn.view = none ∧ fn.params = [] ∧ fn.result = .scalar (.legacy .i64))

structure WellFormedProgram (p : Program) : Prop where
  schema : p.schema = "anl-core-v4"
  revision : p.semanticRevision = "anl-words-v1"
  profile : p.profile.Admissible
  ids : p.functions.toList.map Function.id = List.range p.functions.size
  names : (p.functions.toList.map Function.name).Nodup
  functions : ∀ fn ∈ p.functions.toList, fn.WellFormed p.signatures
  entry : EntryValid p

def checkProgram (p : Program) : Bool :=
  decide (p.schema = "anl-core-v4") &&
  decide (p.semanticRevision = "anl-words-v1") &&
  decide p.profile.Admissible &&
  decide (p.functions.toList.map Function.id = List.range p.functions.size) &&
  decide (p.functions.toList.map Function.name).Nodup &&
  p.functions.toList.all (checkFunction p.signatures) && checkEntry p


end ANL.Words
