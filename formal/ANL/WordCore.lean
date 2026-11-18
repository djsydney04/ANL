import Std

namespace ANL.Word

/-- Only these four unsigned widths belong to the primitive domain. -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, BEq

def Width.bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

def Width.modulus (w : Width) : Nat := 2 ^ w.bits

def Width.decode : Nat → Option Width
  | 8 => some .w8 | 16 => some .w16 | 32 => some .w32 | 64 => some .w64
  | _ => none

/-- Raw payloads are not normalized and carry no validity evidence. -/
structure Word where
  width : Width
  value : Nat
  deriving DecidableEq, Repr, BEq

def Valid (a : Word) : Prop := a.value < a.width.modulus
instance (a : Word) : Decidable (Valid a) := inferInstanceAs (Decidable (_ < _))

def Compatible (a b : Word) : Prop := Valid a ∧ Valid b ∧ a.width = b.width
instance (a b : Word) : Decidable (Compatible a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- These constants match the existing signed scalar domain; no legacy code is changed. -/
def minI64 : Int := -9223372036854775808
def maxI64 : Int := 9223372036854775807
def I64Range (i : Int) : Prop := minI64 ≤ i ∧ i ≤ maxI64
instance (i : Int) : Decidable (I64Range i) := inferInstanceAs (Decidable (_ ∧ _))

inductive Trap where
  | overflow | divisionByZero | invalidShift
  deriving DecidableEq, Repr, BEq

/-- `invalidInput` is a malformed raw input, not a typed program trap. -/
inductive Outcome (α : Type) where
  | value (result : α)
  | trap (reason : Trap)
  | invalidInput
  deriving DecidableEq, Repr

inductive BinaryOp where
  | add | sub | mul | div | rem
  | wrapAdd | wrapSub | wrapMul
  | bitAnd | bitOr | bitXor
  deriving DecidableEq, Repr, BEq

inductive ShiftOp where
  | left | right
  deriving DecidableEq, Repr, BEq

/-- Euclidean remainder makes signed truncation unambiguous, including negatives. -/
def lowBits (w : Width) (i : Int) : Nat := (i % (w.modulus : Int)).toNat

def checkedInteger (w : Width) (i : Int) : Outcome Word :=
  if 0 ≤ i ∧ i < (w.modulus : Int) then .value ⟨w, i.toNat⟩
  else .trap .overflow

/-- Internal arithmetic accepts natural payloads; the public binary boundary validates them. -/
def calculate (op : BinaryOp) (w : Width) (a b : Nat) : Outcome Word :=
  match op with
  | .add => checkedInteger w ((a : Int) + (b : Int))
  | .sub => checkedInteger w ((a : Int) - (b : Int))
  | .mul => checkedInteger w ((a : Int) * (b : Int))
  | .div => if b = 0 then .trap .divisionByZero else .value ⟨w, a / b⟩
  | .rem => if b = 0 then .trap .divisionByZero else .value ⟨w, a % b⟩
  | .wrapAdd => .value ⟨w, lowBits w ((a : Int) + (b : Int))⟩
  | .wrapSub => .value ⟨w, lowBits w ((a : Int) - (b : Int))⟩
  | .wrapMul => .value ⟨w, lowBits w ((a : Int) * (b : Int))⟩
  | .bitAnd => .value ⟨w, a &&& b⟩
  | .bitOr => .value ⟨w, a ||| b⟩
  | .bitXor => .value ⟨w, a ^^^ b⟩

def binary (op : BinaryOp) (a b : Word) : Outcome Word :=
  if Compatible a b then calculate op a.width a.value b.value else .invalidInput

def complement (a : Word) : Outcome Word :=
  if Valid a then .value ⟨a.width, a.width.modulus - 1 - a.value⟩ else .invalidInput

def ShiftCount (w : Width) (i : Int) : Prop := 0 ≤ i ∧ i < (w.bits : Int)
instance (w : Width) (i : Int) : Decidable (ShiftCount w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def shift (op : ShiftOp) (a : Word) (i : Int) : Outcome Word :=
  if Valid a ∧ I64Range i then
    if ShiftCount a.width i then
      match op with
      | .left => .value ⟨a.width, (a.value * 2 ^ i.toNat) % a.width.modulus⟩
      | .right => .value ⟨a.width, a.value / 2 ^ i.toNat⟩
    else .trap .invalidShift
  else .invalidInput

/-- Literal decoding rejects invalid raw widths and payloads; it never wraps. -/
def decodeLiteral (width value : Nat) : Option Word := do
  let w ← Width.decode width
  if value < w.modulus then some ⟨w, value⟩ else none

def checkedFromI64 (w : Width) (i : Int) : Outcome Word :=
  if I64Range i then checkedInteger w i else .invalidInput

def truncateFromI64 (w : Width) (i : Int) : Outcome Word :=
  if I64Range i then .value ⟨w, lowBits w i⟩ else .invalidInput

def checkedToI64 (a : Word) : Outcome Int :=
  if Valid a then
    if (a.value : Int) ≤ maxI64 then .value (a.value : Int) else .trap .overflow
  else .invalidInput

/-- Word-to-word conversion does not pass through a signed i64 intermediate. -/
def checkedWordCast (w : Width) (a : Word) : Outcome Word :=
  if Valid a then checkedInteger w (a.value : Int) else .invalidInput

def truncateWordCast (w : Width) (a : Word) : Outcome Word :=
  if Valid a then .value ⟨w, a.value % w.modulus⟩ else .invalidInput

end ANL.Word
