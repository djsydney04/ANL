import APL.ProductLogicValues
import APL.FlatProductsTyping

namespace APL.ProductAnnotations
open VCG (MVal)

inductive Spec where
  | lit (value : MVal)
  | param (index : Nat)
  | result
  | local (index : Nat)
  | unary (op : UOp) (operand : Spec)
  | binary (op : BOp) (left right : Spec)
  | tuple (fields : List Spec)
  | project (base : Spec) (index : Nat)
  deriving Repr

mutual
  inductive Spec.HasType (params : List FlatProducts.Ty) (result : Option FlatProducts.Ty) (locals : FlatProducts.Ctx) : Spec → FlatProducts.Ty → Prop where
    | lit : HasType params result locals (.lit value) (.scalar value.type)
    | param : params[index]? = some type → HasType params result locals (.param index) type
    | result : result = some type → HasType params result locals .result type
    | local : locals[index]? = some (type, permission) → HasType params result locals (.local index) type
    | unary : HasType params result locals operand (.scalar op.input) →
        HasType params result locals (.unary op operand) (.scalar op.output)
    | binary : HasType params result locals left a → HasType params result locals right b →
        FlatProducts.binaryType op a b = some type →
        HasType params result locals (.binary op left right) type
    | tuple : FieldsTyped params result locals fields (shape.fields.map FlatProducts.Ty.scalar) →
        HasType params result locals (.tuple fields) (.tuple shape)
    | project : HasType params result locals base (.tuple shape) →
        shape.fields[index]? = some type →
        HasType params result locals (.project base index) (.scalar type)
  inductive Spec.FieldsTyped (params : List FlatProducts.Ty) (result : Option FlatProducts.Ty) (locals : FlatProducts.Ctx) :
      List Spec → List FlatProducts.Ty → Prop where
    | nil : FieldsTyped params result locals [] []
    | cons : Spec.HasType params result locals field type →
        FieldsTyped params result locals fields types →
        FieldsTyped params result locals (field :: fields) (type :: types)
end

inductive Term where
  | lit (value : FlatProducts.Val)
  | local (index : Nat)
  | letE (value body : Term)
  | letMut (value body : Term)
  | assign (index : Nat) (value : Term)
  | whileE (invariants : List Spec) (condition body : Term)
  | ifE (condition yes no : Term)
  | unary (op : UOp) (operand : Term)
  | binary (op : BOp) (left right : Term)
  | call (function : Nat) (arguments : List Term)
  | tuple (fields : List Term)
  | project (base : Term) (index : Nat)
  deriving Repr

def Term.erase : Term → FlatProducts.Term
  | .lit value => .lit value
  | .local index => .local index
  | .letE value body => .letE value.erase body.erase
  | .letMut value body => .letMut value.erase body.erase
  | .assign index value => .assign index value.erase
  | .whileE _ condition body => .whileE condition.erase body.erase
  | .ifE condition yes no => .ifE condition.erase yes.erase no.erase
  | .unary op operand => .unary op operand.erase
  | .binary op left right => .binary op left.erase right.erase
  | .call function arguments => .call function (arguments.map erase)
  | .tuple fields => .tuple (fields.map erase)
  | .project base index => .project base.erase index

mutual
  inductive HasType (sigs : FlatProducts.Signatures) : FlatProducts.Ctx → Term → FlatProducts.Ty → Prop where
    | lit : HasType sigs Γ (.lit value) value.type
    | local : Γ[index]? = some (type, permission) → HasType sigs Γ (.local index) type
    | letE : HasType sigs Γ value a → HasType sigs ((a, false) :: Γ) body b →
        HasType sigs Γ (.letE value body) b
    | letMut : HasType sigs Γ value a → HasType sigs ((a, true) :: Γ) body b →
        HasType sigs Γ (.letMut value body) b
    | assign : Γ[index]? = some (type, true) → HasType sigs Γ value type →
        HasType sigs Γ (.assign index value) (.scalar .unit)
    | whileE : invariants ≠ [] →
        (∀ clause ∈ invariants, Spec.HasType [] none Γ clause (.scalar .bool)) →
        HasType sigs Γ condition (.scalar .bool) → HasType sigs Γ body (.scalar .unit) →
        HasType sigs Γ (.whileE invariants condition body) (.scalar .unit)
    | ifE : HasType sigs Γ condition (.scalar .bool) → HasType sigs Γ yes type →
        HasType sigs Γ no type → HasType sigs Γ (.ifE condition yes no) type
    | unary : HasType sigs Γ operand (.scalar op.input) →
        HasType sigs Γ (.unary op operand) (.scalar op.output)
    | binary : HasType sigs Γ left a → HasType sigs Γ right b →
        FlatProducts.binaryType op a b = some type → HasType sigs Γ (.binary op left right) type
    | call : sigs[function]? = some (params, result) → ArgsTyped sigs Γ arguments params →
        HasType sigs Γ (.call function arguments) result
    | tuple : ArgsTyped sigs Γ fields (shape.fields.map FlatProducts.Ty.scalar) →
        HasType sigs Γ (.tuple fields) (.tuple shape)
    | project : HasType sigs Γ base (.tuple shape) → shape.fields[index]? = some type →
        HasType sigs Γ (.project base index) (.scalar type)
  inductive ArgsTyped (sigs : FlatProducts.Signatures) : FlatProducts.Ctx → List Term → List FlatProducts.Ty → Prop where
    | nil : ArgsTyped sigs Γ [] []
    | cons : HasType sigs Γ term type → ArgsTyped sigs Γ terms types →
        ArgsTyped sigs Γ (term :: terms) (type :: types)
end

theorem erase_typed (h : HasType sigs Γ term type) :
    FlatProducts.HasType sigs Γ term.erase type := by
  induction h using HasType.rec
    (motive_2 := fun Γ terms types _ => FlatProducts.ArgsTyped sigs Γ (terms.map Term.erase) types) with
  | lit => simp only [Term.erase]; exact .lit
  | «local» h => simp only [Term.erase]; exact .local h
  | letE _ _ ha hb => simp only [Term.erase]; exact .letE ha hb
  | letMut _ _ ha hb => simp only [Term.erase]; exact .letMut ha hb
  | assign hi _ ha => simp only [Term.erase]; exact .assign hi ha
  | whileE _ _ _ _ hc hb => simp only [Term.erase]; exact .whileE hc hb
  | ifE _ _ _ hc ha hb => simp only [Term.erase]; exact .ifE hc ha hb
  | unary _ ha => simp only [Term.erase]; exact .unary ha
  | binary _ _ hop ha hb => simp only [Term.erase]; exact .binary ha hb hop
  | call hf _ ha => simp only [Term.erase]; exact .call hf ha
  | tuple _ h => simp only [Term.erase]; exact .tuple h
  | project _ hi h => simp only [Term.erase]; exact .project h hi
  | nil => exact .nil
  | cons _ _ ha hb => exact .cons ha hb

structure Function where
  name : String
  params : List FlatProducts.Ty
  result : FlatProducts.Ty
  requires : List Spec
  ensures : List Spec
  body : Term
  deriving Repr
abbrev Functions := Array Function

def signatures (fs : Functions) : FlatProducts.Signatures := fs.map fun fn => (fn.params, fn.result)

def Function.erase (fn : Function) : FlatProducts.Function :=
  ⟨fn.name, fn.params, fn.result, fn.body.erase⟩

def eraseFunctions (fs : Functions) : FlatProducts.Functions := fs.map Function.erase

def Function.WellTyped (sigs : FlatProducts.Signatures) (fn : Function) : Prop :=
  HasType sigs (FlatProducts.immutable fn.params.reverse) fn.body fn.result ∧
  (∀ clause ∈ fn.requires, Spec.HasType fn.params none [] clause (.scalar .bool)) ∧
  (∀ clause ∈ fn.ensures, Spec.HasType fn.params (some fn.result) [] clause (.scalar .bool))

def WellTyped (fs : Functions) : Prop :=
  ∀ (index : Nat) (fn : Function), fs[index]? = some fn → fn.WellTyped (signatures fs)

theorem erase_signatures : FlatProducts.signatures (eraseFunctions fs) = signatures fs := by
  simp [FlatProducts.signatures, signatures, eraseFunctions, Function.erase, Array.map_map]

theorem erase_wellTyped (h : WellTyped fs) : FlatProducts.WellTyped (eraseFunctions fs) := by
  intro index fn hf
  simp only [eraseFunctions, Array.getElem?_map, Option.map_eq_some_iff] at hf
  obtain ⟨old, ho, rfl⟩ := hf
  simpa only [erase_signatures, Function.erase] using erase_typed (h index old ho).1

theorem erase_lookup {fs : Functions} {index : Nat} {fn : Function} (h : fs[index]? = some fn) :
    (eraseFunctions fs)[index]? = some fn.erase := by
  simp [eraseFunctions, Array.getElem?_map, h]

end APL.ProductAnnotations
