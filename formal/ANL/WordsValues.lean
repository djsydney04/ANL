import APL.FlatProductsTyping
import ANL.WordBits
import ANL.WordConversions

namespace ANL.Words

abbrev Flat := APL.FlatProducts.Flat
abbrev WordValue := { raw : ANL.Word.Word // ANL.Word.Valid raw }

inductive ScalarTy where
  | legacy (type : APL.Ty)
  | word (width : ANL.Word.Width)
  deriving DecidableEq, Repr

inductive ScalarVal where
  | legacy (value : APL.Val)
  | word (value : WordValue)
  deriving DecidableEq, Repr

def ScalarVal.type : ScalarVal → ScalarTy
  | .legacy v => .legacy v.type
  | .word v => .word v.val.width

inductive Ty where
  | scalar (type : ScalarTy)
  | tuple (shape : Flat ScalarTy)
  deriving DecidableEq, Repr

inductive Val where
  | scalar (value : ScalarVal)
  | tuple (fields : Flat ScalarVal)
  deriving DecidableEq, Repr

def Val.type : Val → Ty
  | .scalar v => .scalar v.type
  | .tuple fields => .tuple (fields.map ScalarVal.type)

def Ty.asScalar : Ty → Option ScalarTy
  | .scalar t => some t
  | .tuple _ => none

abbrev VCtx := List (Ty × Bool)
abbrev Env := List Val
def immutable (types : List Ty) : VCtx := types.map (fun t => (t, false))
def update : Env → Nat → Val → Option Env
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (update xs n v).map (x :: ·)
def EnvTyped (env : Env) (Γ : VCtx) : Prop := env.map Val.type = Γ.map Prod.fst

inductive Trap where
  | arithmeticOverflow | divisionByZero | invalidShift | invalidLength | indexOutOfBounds
  deriving DecidableEq, Repr

def legacyTrap : APL.Trap → Trap
  | .arithmeticOverflow => .arithmeticOverflow
  | .divisionByZero => .divisionByZero
def primitiveTrap : ANL.Word.Trap → Trap
  | .overflow => .arithmeticOverflow
  | .divisionByZero => .divisionByZero
  | .invalidShift => .invalidShift

inductive Result where
  | value (value : Val)
  | trap (kind : Trap)
  | invalid
  deriving DecidableEq, Repr

def Result.Typed (type : Ty) : Result → Prop
  | .value v => v.type = type
  | .trap _ => True
  | .invalid => False

def legacyResult : APL.Result → Result
  | .value v => .value (.scalar (.legacy v))
  | .trap t => .trap (legacyTrap t)
  | .invalid => .invalid

/-- The raw primitive outcome is checked before acquiring a bounded runtime value. -/
def wordResult : ANL.Word.Outcome ANL.Word.Word → Result
  | .value v => if h : ANL.Word.Valid v then .value (.scalar (.word ⟨v, h⟩)) else .invalid
  | .trap t => .trap (primitiveTrap t)
  | .invalidInput => .invalid

def signedResult : ANL.Word.Outcome Int → Result
  | .value v => if h : APL.InRange v then .value (.scalar (.legacy (.int ⟨v, h⟩))) else .invalid
  | .trap t => .trap (primitiveTrap t)
  | .invalidInput => .invalid

def wordLiteral (width value : Nat) : Result :=
  match ANL.Word.decodeLiteral width value with
  | none => .invalid
  | some v => wordResult (.value v)

def wordLiteralType (width value : Nat) : Option Ty := do
  let w ← ANL.Word.Width.decode width
  if value < w.modulus then some (.scalar (.word w)) else none

inductive WordLiteralSig (width value : Nat) : Ty → Prop where
  | word : width = w.bits → value < w.modulus → WordLiteralSig width value (.scalar (.word w))

inductive UOp where
  | legacy (op : APL.UOp)
  | bitNot
  deriving DecidableEq, Repr

inductive BOp where
  | legacy (op : APL.BOp)
  | wrapAdd | wrapSub | wrapMul | bitAnd | bitXor | bitOr | shl | shr
  deriving DecidableEq, Repr

inductive ConvertMode where
  | checked | truncate
  deriving DecidableEq, Repr

def WordArithmeticOp (op : BOp) : Prop :=
  op ∈ [.legacy .add, .legacy .sub, .legacy .mul, .legacy .div, .legacy .rem,
    .wrapAdd, .wrapSub, .wrapMul, .bitAnd, .bitXor, .bitOr]
instance (op : BOp) : Decidable (WordArithmeticOp op) := inferInstanceAs (Decidable (_ ∈ _))
def WordCompareOp (op : BOp) : Prop :=
  op ∈ [.legacy .lt, .legacy .le, .legacy .gt, .legacy .ge, .legacy .eq, .legacy .ne]
instance (op : BOp) : Decidable (WordCompareOp op) := inferInstanceAs (Decidable (_ ∈ _))

def wordArithmetic : BOp → Option ANL.Word.BinaryOp
  | .legacy .add => some .add | .legacy .sub => some .sub | .legacy .mul => some .mul
  | .legacy .div => some .div | .legacy .rem => some .rem
  | .wrapAdd => some .wrapAdd | .wrapSub => some .wrapSub | .wrapMul => some .wrapMul
  | .bitAnd => some .bitAnd | .bitOr => some .bitOr | .bitXor => some .bitXor
  | _ => none

def compareWord (op : BOp) (a b : Nat) : Option Bool :=
  match op with
  | .legacy .lt => some (decide (a < b)) | .legacy .le => some (decide (a ≤ b))
  | .legacy .gt => some (decide (a > b)) | .legacy .ge => some (decide (a ≥ b))
  | .legacy .eq => some (decide (a = b)) | .legacy .ne => some (decide (a ≠ b))
  | _ => none

def Numeric : ScalarTy → Prop
  | .legacy .i64 | .word _ => True
  | _ => False
instance (t : ScalarTy) : Decidable (Numeric t) := by cases t with
  | legacy t => cases t <;> simp only [Numeric] <;> infer_instance
  | word _ => simp only [Numeric]; infer_instance
def IsWord : ScalarTy → Prop
  | .word _ => True | _ => False
instance (t : ScalarTy) : Decidable (IsWord t) := by cases t <;> simp only [IsWord] <;> infer_instance

def unaryType : UOp → Ty → Option Ty
  | .legacy op, .scalar (.legacy t) =>
      if t = op.input then some (.scalar (.legacy op.output)) else none
  | .bitNot, .scalar (.word w) => some (.scalar (.word w))
  | _, _ => none

def binaryType (op : BOp) (a b : Ty) : Option Ty :=
  match a, b with
  | .scalar (.legacy a), .scalar (.legacy b) => match op with
    | .legacy op => (APL.binaryType op a b).map (fun t => .scalar (.legacy t))
    | _ => none
  | .scalar (.word a), .scalar (.word b) =>
      if a = b then
        if WordArithmeticOp op then some (.scalar (.word a))
        else if WordCompareOp op then some (.scalar (.legacy .bool)) else none
      else none
  | .scalar (.word a), .scalar (.legacy .i64) =>
      if op = .shl ∨ op = .shr then some (.scalar (.word a)) else none
  | .tuple a, .tuple b =>
      if (op = .legacy .eq ∨ op = .legacy .ne) ∧ a = b then some (.scalar (.legacy .bool)) else none
  | _, _ => none

def convertType (mode : ConvertMode) (target : ScalarTy) : Ty → Option Ty
  | .scalar source =>
      if Numeric source ∧ Numeric target ∧ (mode = .checked ∨ IsWord target)
      then some (.scalar target) else none
  | .tuple _ => none

inductive UnarySig : UOp → Ty → Ty → Prop where
  | legacy : UnarySig (.legacy op) (.scalar (.legacy op.input)) (.scalar (.legacy op.output))
  | bitNot : UnarySig .bitNot (.scalar (.word w)) (.scalar (.word w))

inductive BinarySig : BOp → Ty → Ty → Ty → Prop where
  | legacy : APL.binaryType op a b = some t →
      BinarySig (.legacy op) (.scalar (.legacy a)) (.scalar (.legacy b)) (.scalar (.legacy t))
  | arithmetic : WordArithmeticOp op → BinarySig op (.scalar (.word w)) (.scalar (.word w)) (.scalar (.word w))
  | compare : WordCompareOp op → BinarySig op (.scalar (.word w)) (.scalar (.word w)) (.scalar (.legacy .bool))
  | shift : (op = .shl ∨ op = .shr) → BinarySig op (.scalar (.word w)) (.scalar (.legacy .i64)) (.scalar (.word w))
  | tuple : (op = .legacy .eq ∨ op = .legacy .ne) →
      BinarySig op (.tuple shape) (.tuple shape) (.scalar (.legacy .bool))

inductive ConvertSig : ConvertMode → ScalarTy → Ty → Ty → Prop where
  | numeric : Numeric source → Numeric target → (mode = .checked ∨ IsWord target) →
      ConvertSig mode target (.scalar source) (.scalar target)

def unary (op : UOp) : Val → Result
  | .scalar (.legacy v) => match op with
    | .legacy op => legacyResult (APL.unary op v) | _ => .invalid
  | .scalar (.word v) => match op with
    | .bitNot => wordResult (ANL.Word.complement v.val) | _ => .invalid
  | .tuple _ => .invalid

def binary (op : BOp) (a b : Val) : Result :=
  match a, b with
  | .scalar (.legacy a), .scalar (.legacy b) => match op with
    | .legacy op => legacyResult (APL.binary op a b) | _ => .invalid
  | .scalar (.word a), .scalar (.word b) =>
      if a.val.width = b.val.width then
        match wordArithmetic op with
        | some operation => wordResult (ANL.Word.binary operation a.val b.val)
        | none => match compareWord op a.val.value b.val.value with
          | some value => .value (.scalar (.legacy (.bool value))) | none => .invalid
      else .invalid
  | .scalar (.word a), .scalar (.legacy (.int n)) => match op with
    | .shl => wordResult (ANL.Word.shift .left a.val n.val)
    | .shr => wordResult (ANL.Word.shift .right a.val n.val)
    | _ => .invalid
  | .tuple a, .tuple b =>
      if a.map ScalarVal.type = b.map ScalarVal.type then match op with
        | .legacy .eq => .value (.scalar (.legacy (.bool (decide (a.fields = b.fields)))))
        | .legacy .ne => .value (.scalar (.legacy (.bool (!decide (a.fields = b.fields)))) )
        | _ => .invalid
      else .invalid
  | _, _ => .invalid

def convert (mode : ConvertMode) (target : ScalarTy) : Val → Result
  | .scalar (.legacy (.int n)) => match target, mode with
    | .legacy .i64, .checked => .value (.scalar (.legacy (.int n)))
    | .word w, .checked => wordResult (ANL.Word.checkedFromI64 w n.val)
    | .word w, .truncate => wordResult (ANL.Word.truncateFromI64 w n.val)
    | _, _ => .invalid
  | .scalar (.word a) => match target, mode with
    | .legacy .i64, .checked => signedResult (ANL.Word.checkedToI64 a.val)
    | .word w, .checked => wordResult (ANL.Word.checkedWordCast w a.val)
    | .word w, .truncate => wordResult (ANL.Word.truncateWordCast w a.val)
    | _, _ => .invalid
  | _ => .invalid

def shortCircuit (op : BOp) : Val → Bool
  | .scalar (.legacy v) => match op with
    | .legacy op => APL.shortCircuit op v | _ => false
  | _ => false

def construct (fields : List ScalarVal) : Result :=
  match APL.FlatProducts.Flat.make fields with
  | some fields => .value (.tuple fields) | none => .invalid
def project (v : Val) (index : Nat) : Result :=
  match v with
  | .scalar _ => .invalid
  | .tuple fields => match fields.fields[index]? with
    | some v => .value (.scalar v) | none => .invalid

def embedScalarTy := ScalarTy.legacy
def embedScalar := ScalarVal.legacy
def embedTy : APL.FlatProducts.Ty → Ty
  | .scalar t => .scalar (.legacy t)
  | .tuple ts => .tuple (ts.map ScalarTy.legacy)
def embedVal : APL.FlatProducts.Val → Val
  | .scalar v => .scalar (.legacy v)
  | .tuple vs => .tuple (vs.map ScalarVal.legacy)

end ANL.Words
