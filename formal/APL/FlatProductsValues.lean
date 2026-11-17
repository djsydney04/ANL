import APL.LocalStateSafety

namespace APL.FlatProducts

structure Flat (α : Type) where
  fields : List α
  nonempty : 0 < fields.length
  bounded : fields.length ≤ 8
  deriving DecidableEq, Repr

@[ext] theorem Flat.ext {a b : Flat α} (h : a.fields = b.fields) : a = b := by
  cases a; cases b; cases h; rfl

def Flat.map (f : α → β) (xs : Flat α) : Flat β :=
  ⟨xs.fields.map f, by simpa using xs.nonempty, by simpa using xs.bounded⟩

def Flat.make (xs : List α) : Option (Flat α) :=
  if h : 0 < xs.length ∧ xs.length ≤ 8 then some ⟨xs, h.1, h.2⟩ else none

@[simp] theorem Flat.make_fields (xs : Flat α) : Flat.make xs.fields = some xs := by
  simp [Flat.make, xs.nonempty, xs.bounded]

inductive Ty where
  | scalar (type : APL.Ty)
  | tuple (shape : Flat APL.Ty)
  deriving DecidableEq, Repr

inductive Val where
  | scalar (value : APL.Val)
  | tuple (fields : Flat APL.Val)
  deriving DecidableEq, Repr

def Val.type : Val → Ty
  | .scalar v => .scalar v.type
  | .tuple fields => .tuple (fields.map APL.Val.type)

abbrev Env := List Val

def Ty.asScalar : Ty → Option APL.Ty
  | .scalar t => some t
  | .tuple _ => none

inductive Result where
  | value (value : Val)
  | trap (kind : Trap)
  | invalid
  deriving DecidableEq, Repr

def embedResult : APL.Result → Result
  | .value v => .value (.scalar v)
  | .trap kind => .trap kind
  | .invalid => .invalid

def Result.Typed (t : Ty) : Result → Prop
  | .value v => v.type = t
  | .trap _ => True
  | .invalid => False

def unary (op : UOp) : Val → Result
  | .scalar v => embedResult (APL.unary op v)
  | .tuple _ => .invalid

def binaryType (op : BOp) (a b : Ty) : Option Ty :=
  match a, b with
  | .scalar a, .scalar b => (APL.binaryType op a b).map Ty.scalar
  | .tuple a, .tuple b =>
      if (op = .eq ∨ op = .ne) ∧ a = b then some (.scalar .bool) else none
  | _, _ => none

def binary (op : BOp) (a b : Val) : Result :=
  match a, b with
  | .scalar a, .scalar b => embedResult (APL.binary op a b)
  | .tuple a, .tuple b =>
      if a.map APL.Val.type = b.map APL.Val.type then
        match op with
        | .eq => .value (.scalar (.bool (decide (a.fields = b.fields))))
        | .ne => .value (.scalar (.bool (!decide (a.fields = b.fields))))
        | _ => .invalid
      else .invalid
  | _, _ => .invalid

def shortCircuit (op : BOp) : Val → Bool
  | .scalar v => APL.shortCircuit op v
  | .tuple _ => false

def construct (fields : List APL.Val) : Result :=
  match Flat.make fields with
  | some fields => .value (.tuple fields)
  | none => .invalid

def project (v : Val) (index : Nat) : Result :=
  match v with
  | .scalar _ => .invalid
  | .tuple fields => match fields.fields[index]? with
      | some v => .value (.scalar v)
      | none => .invalid

theorem scalar_canonical {v : Val} {t : APL.Ty} (h : v.type = .scalar t) : ∃ a, v = .scalar a ∧ a.type = t := by
  cases v with
  | scalar a => exact ⟨a, rfl, Ty.scalar.inj h⟩
  | tuple fields => cases h

theorem tuple_canonical {v : Val} {shape : Flat APL.Ty} (h : v.type = .tuple shape) :
    ∃ fields, v = .tuple fields ∧ fields.map APL.Val.type = shape := by
  cases v with
  | scalar a => cases h
  | tuple fields => exact ⟨fields, rfl, Ty.tuple.inj h⟩

theorem embedResult_typed (h : r.Typed t) : (embedResult r).Typed (.scalar t) := by
  cases r with
  | value v => exact congrArg Ty.scalar h
  | trap _ => trivial
  | invalid => exact h

theorem unary_typed (h : a.type = .scalar op.input) :
    (unary op a).Typed (.scalar op.output) := by
  obtain ⟨v, rfl, ht⟩ := scalar_canonical h
  exact embedResult_typed (APL.unary_typed ht)

theorem binary_typed (h : binaryType op a.type b.type = some t) :
    (binary op a b).Typed t := by
  cases a with
  | scalar a =>
    cases b with
    | scalar b =>
      simp only [Val.type, binaryType, Option.map_eq_some_iff] at h
      obtain ⟨ty, h, rfl⟩ := h
      exact embedResult_typed (APL.binary_typed h)
    | tuple b => simp [Val.type, binaryType] at h
  | tuple a =>
    cases b with
    | scalar b => simp [Val.type, binaryType] at h
    | tuple b =>
      simp only [Val.type, binaryType] at h
      split at h
      next condition =>
        obtain ⟨hop, shape⟩ := condition
        cases h
        rcases hop with rfl | rfl <;> simp [binary, shape, Result.Typed, Val.type, APL.Val.type]
      · contradiction

theorem shortCircuit_typed (h : binaryType op v.type b = some t)
    (hs : shortCircuit op v = true) : v.type = t := by
  cases v with
  | tuple fields => simp [shortCircuit] at hs
  | scalar v =>
    cases b with
    | tuple fields => simp [Val.type, binaryType] at h
    | scalar b =>
      simp only [Val.type, binaryType, Option.map_eq_some_iff] at h
      obtain ⟨ty, h, rfl⟩ := h
      exact congrArg Ty.scalar (APL.shortCircuit_typed h hs)

theorem construct_typed (h : fields.map APL.Val.type = shape.fields) :
    (construct fields).Typed (.tuple shape) := by
  have n : 0 < fields.length := by simpa [← h] using shape.nonempty
  have b : fields.length ≤ 8 := by simpa [← h] using shape.bounded
  simp only [construct, Flat.make, n, b, and_self, ↓reduceDIte, Result.Typed, Val.type]
  congr 1
  exact Flat.ext h

theorem project_typed (h : v.type = .tuple shape) (hi : shape.fields[index]? = some t) :
    (project v index).Typed (.scalar t) := by
  obtain ⟨fields, rfl, shape⟩ := tuple_canonical h
  subst shape
  simp only [Flat.map, List.getElem?_map] at hi
  cases hv : fields.fields[index]? with
  | none => simp [hv] at hi
  | some v =>
    simp only [hv, Option.map_some, Option.some.injEq] at hi
    simpa [project, hv, Result.Typed, Val.type] using congrArg Ty.scalar hi

end APL.FlatProducts
