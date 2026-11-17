import Std

namespace APL

inductive Ty where
  | i64 | bool | unit
  deriving DecidableEq, Repr, BEq

def minI64 : Int := -9223372036854775808
def maxI64 : Int := 9223372036854775807
def InRange (n : Int) : Prop := minI64 ≤ n ∧ n ≤ maxI64
instance (n : Int) : Decidable (InRange n) := inferInstanceAs (Decidable (_ ∧ _))
abbrev I64 := { n : Int // InRange n }

inductive Val where
  | int (n : I64)
  | bool (b : Bool)
  | unit
  deriving DecidableEq, Repr

def Val.type : Val → Ty
  | .int _ => .i64
  | .bool _ => .bool
  | .unit => .unit

inductive UOp where
  | neg | not
  deriving DecidableEq, Repr
inductive BOp where
  | add | sub | mul | div | rem | lt | le | gt | ge | eq | ne | and | or
  deriving DecidableEq, Repr

def UOp.input : UOp → Ty | .neg => .i64 | .not => .bool
def UOp.output : UOp → Ty | .neg => .i64 | .not => .bool

def binaryType (op : BOp) (a b : Ty) : Option Ty :=
  match op, a, b with
  | .add, .i64, .i64 | .sub, .i64, .i64 | .mul, .i64, .i64
  | .div, .i64, .i64 | .rem, .i64, .i64 => some .i64
  | .lt, .i64, .i64 | .le, .i64, .i64 | .gt, .i64, .i64 | .ge, .i64, .i64 => some .bool
  | .eq, a, b | .ne, a, b => if a = b then some .bool else none
  | .and, .bool, .bool | .or, .bool, .bool => some .bool
  | _, _, _ => none

inductive Expr where
  | lit (v : Val)
  | local (index : Nat)
  | letE (value body : Expr)
  | ifE (condition yes no : Expr)
  | unary (op : UOp) (operand : Expr)
  | binary (op : BOp) (left right : Expr)
  deriving Repr

abbrev Ctx := List Ty
abbrev Env := List Val

inductive HasType : Ctx → Expr → Ty → Prop where
  | lit : HasType Γ (.lit v) v.type
  | local : Γ[index]? = some t → HasType Γ (.local index) t
  | letE : HasType Γ a u → HasType (u :: Γ) b t → HasType Γ (.letE a b) t
  | ifE : HasType Γ c .bool → HasType Γ a t → HasType Γ b t → HasType Γ (.ifE c a b) t
  | unary : HasType Γ a op.input → HasType Γ (.unary op a) op.output
  | binary : HasType Γ a u → HasType Γ b v → binaryType op u v = some t →
      HasType Γ (.binary op a b) t

def infer (Γ : Ctx) : Expr → Option Ty
  | .lit v => some v.type
  | .local i => Γ[i]?
  | .letE a b => (infer Γ a).bind fun u => infer (u :: Γ) b
  | .ifE c a b => (infer Γ c).bind fun ct =>
      if ct ≠ .bool then none else
      (infer Γ a).bind fun ta => (infer Γ b).bind fun tb =>
      if ta = tb then some ta else none
  | .unary op a => (infer Γ a).bind fun t =>
      if t = op.input then some op.output else none
  | .binary op a b => (infer Γ a).bind fun u =>
      (infer Γ b).bind fun v => binaryType op u v

theorem infer_complete (h : HasType Γ e t) : infer Γ e = some t := by
  induction h with
  | lit => rfl
  | «local» h => exact h
  | letE _ _ ha hb => simp [infer, ha, hb]
  | ifE _ _ _ hc ha hb => simp [infer, hc, ha, hb]
  | unary _ ha => simp [infer, ha]
  | binary _ _ hop ha hb => simp [infer, ha, hb, hop]

theorem infer_sound (h : infer Γ e = some t) : HasType Γ e t := by
  induction e generalizing Γ t with
  | lit v => simp [infer] at h; subst t; exact .lit
  | «local» i => exact .local h
  | letE a b ia ib =>
    simp only [infer, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, hb⟩ := h
    exact .letE (ia ha) (ib hb)
  | ifE c a b ic ia ib =>
    simp only [infer, Option.bind_eq_some_iff] at h
    obtain ⟨ct, hc, h⟩ := h
    split at h
    · contradiction
    next ht =>
      have ht : ct = .bool := by simpa using ht
      subst ct
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ta, ha, tb, hb, h⟩ := h
      split at h
      next eq => cases h; subst tb; exact .ifE (ic hc) (ia ha) (ib hb)
      · contradiction
  | unary op a ia =>
    simp only [infer, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, h⟩ := h
    split at h
    next ht => cases h; subst u; exact .unary (ia ha)
    · contradiction
  | binary op a b ia ib =>
    simp only [infer, Option.bind_eq_some_iff] at h
    obtain ⟨u, ha, v, hb, ht⟩ := h
    exact .binary (ia ha) (ib hb) ht

theorem type_unique (ha : HasType Γ e a) (hb : HasType Γ e b) : a = b := by
  have := (infer_complete ha).symm.trans (infer_complete hb)
  exact Option.some.inj this

inductive Trap where
  | arithmeticOverflow | divisionByZero
  deriving DecidableEq, Repr

inductive Result where
  | value (v : Val)
  | trap (t : Trap)
  | invalid
  deriving DecidableEq, Repr

def checked (n : Int) : Result :=
  if h : InRange n then .value (.int ⟨n, h⟩) else .trap .arithmeticOverflow

def unary (op : UOp) (v : Val) : Result :=
  match op, v with
  | .neg, .int n => checked (-n.val)
  | .not, .bool b => .value (.bool (!b))
  | _, _ => .invalid

def quotient (a b : Int) : Int :=
  let n : Int := Int.ofNat (a.natAbs / b.natAbs)
  if (a < 0) != (b < 0) then -n else n

def division (a b : I64) (remainder : Bool) : Result :=
  if b.val = 0 then .trap .divisionByZero
  else if a.val = minI64 ∧ b.val = -1 then .trap .arithmeticOverflow
  else checked (if remainder then a.val - quotient a.val b.val * b.val else quotient a.val b.val)

def binary (op : BOp) (a b : Val) : Result :=
  match op, a, b with
  | .add, .int a, .int b => checked (a.val + b.val)
  | .sub, .int a, .int b => checked (a.val - b.val)
  | .mul, .int a, .int b => checked (a.val * b.val)
  | .div, .int a, .int b => division a b false
  | .rem, .int a, .int b => division a b true
  | .lt, .int a, .int b => .value (.bool (a.val < b.val))
  | .le, .int a, .int b => .value (.bool (a.val ≤ b.val))
  | .gt, .int a, .int b => .value (.bool (a.val > b.val))
  | .ge, .int a, .int b => .value (.bool (a.val ≥ b.val))
  | .eq, a, b => if a.type = b.type then .value (.bool (a = b)) else .invalid
  | .ne, a, b => if a.type = b.type then .value (.bool (a != b)) else .invalid
  | .and, .bool a, .bool b => .value (.bool (a && b))
  | .or, .bool a, .bool b => .value (.bool (a || b))
  | _, _, _ => .invalid

def Result.Typed (t : Ty) : Result → Prop
  | .value v => v.type = t
  | .trap _ => True
  | .invalid => False

theorem checked_typed (n : Int) : (checked n).Typed .i64 := by
  unfold checked
  split <;> simp [Result.Typed, Val.type]

theorem division_typed (a b : I64) (r : Bool) : (division a b r).Typed .i64 := by
  unfold division
  split
  · trivial
  · split
    · trivial
    · exact checked_typed _

theorem unary_typed (h : a.type = op.input) : (unary op a).Typed op.output := by
  cases op <;> cases a <;> simp_all [Val.type, UOp.input, UOp.output, unary, Result.Typed]
  exact checked_typed _

theorem binary_typed (h : binaryType op a.type b.type = some t) : (binary op a b).Typed t := by
  cases op <;> cases a <;> cases b <;>
    simp_all only [Val.type, binaryType, Option.some.injEq, ite_true, ite_false, reduceCtorEq]
  all_goals subst t
  all_goals simp only [binary]
  all_goals first | exact checked_typed _ | exact division_typed _ _ _ | simp [Result.Typed, Val.type]

end APL
