import ANL.MemoryExecute
import ANL.MemoryLoweringProofs
import ANL.MemoryMirRunProofs

namespace ANL.Memory.Simulation

open Lowering

def binding (b : ANL.Memory.Binding) : Mir.Binding := ⟨b.mode, b.ref, b.length⟩
def loan (l : ANL.Memory.Loan) : Mir.Loan := ⟨binding l.source, l.mode⟩
def trap : MemoryTrap → Mir.Trap
  | .scalar kind => .scalar kind
  | .invalidLength => .invalidLength
  | .indexOutOfBounds => .indexOutOfBounds

def localValue (a : Mir.Activation) : Local → Option Val
  | .value v => a.temp v
  | .mutable s => a.slot s

/-- Immutable source bindings may alias; mutable source bindings name distinct slots. -/
inductive LocalsRel (a : Mir.Activation) : Locals → Env → Prop where
  | nil : LocalsRel a [] []
  | cons : localValue a l = some v → LocalsRel a ls vs → LocalsRel a (l :: ls) (v :: vs)

/-- Exact recursive pairing, with no truncated zip and no global descriptor uniqueness. -/
inductive ResourcesRel : List Nat → Resources → Mir.Resources → Prop where
  | nil : ResourcesRel [] [] []
  | cons {rid : Nat} : ResourcesRel ids bs rs →
      ResourcesRel (rid :: ids) (b :: bs) ((rid, binding b) :: rs)

def mutableIds : Locals → List Nat
  | [] => []
  | .value _ :: rest => mutableIds rest
  | .mutable s :: rest => s.id :: mutableIds rest

structure ActivationRel (locals : Locals) (ids : List Nat)
    (source : ANL.Memory.Activation) (target : Mir.Activation) : Prop where
  function : source.function = target.function
  values : LocalsRel target locals source.env
  slots : (mutableIds locals).Nodup
  slotKeys : target.slots.map Prod.fst = mutableIds locals
  resources : ResourcesRel ids source.resources target.resources
  resourceIds : ids.Nodup

/-- Captures are values already read, including tuple fields and ordinary call arguments. -/
def Captured (a : Mir.Activation) (temps : List Mir.Temp) (reversed : List Val) : Prop :=
  a.capture temps = some reversed.reverse

structure Below (supply : Supply) (a : Mir.Activation) : Prop where
  temps : ∀ id v, (id, v) ∈ a.temps → id < supply.nextTemp
  slots : ∀ id v, (id, v) ∈ a.slots → id < supply.nextSlot

def LocalBelow (supply : Supply) : Local → Prop
  | .value v => v.id < supply.nextTemp
  | .mutable s => s.id < supply.nextSlot

def LocalsBelow (supply : Supply) (locals : Locals) : Prop := ∀ l ∈ locals, LocalBelow supply l

def TempAgreement (bound : Nat) (current saved : Mir.Values) : Prop :=
  ∀ rid, rid < bound → Mir.lookupId rid current = Mir.lookupId rid saved

/-- The runtime frame stores only Temps; this proof metadata remembers their allocation frontier. -/
structure SavedTemps (locals : Locals) where
  values : Mir.Values
  bound : Supply
  tempsBelow : ∀ rid v, (rid, v) ∈ values → rid < bound.nextTemp
  localsBelow : LocalsBelow bound locals

structure Suspended where
  offset : Nat
  locals : Locals
  ids : List Nat
  bound : Supply
  source : ANL.Memory.Activation
  target : Mir.Activation
  represented : ActivationRel locals ids source target
  below : Below bound target

def CoreFramePlain : ANL.Memory.Frame → Prop
  | .owner _ _ | .callReturn _ _ => False
  | _ => True

def MirFramePlain : Mir.Frame → Prop
  | .owner _ _ _ | .callReturn _ _ => False
  | _ => True

/-- Retains owners and suspended callers; scalar evaluation frames do not grant capabilities. -/
inductive CapabilityKontRel : List ANL.Memory.Frame → List Mir.Frame → Prop where
  | nil : CapabilityKontRel [] []
  | sourcePlain : CoreFramePlain f → CapabilityKontRel k m → CapabilityKontRel (f :: k) m
  | targetPlain : MirFramePlain f → CapabilityKontRel k m → CapabilityKontRel k (f :: m)
  | owner {rid : Nat} : CapabilityKontRel k m →
      CapabilityKontRel (.owner b site :: k) (.owner rid (binding b) site :: m)
  | caller : ActivationRel locals ids a b → CapabilityKontRel k m →
      CapabilityKontRel (.callReturn a l :: k) (.callReturn b (l.map loan) :: m)

/-- Exact world identity includes mutable cells, request ordinals, live owners and retained events. -/
structure RuntimeRel (locals : Locals) (ids : List Nat)
    (source : ANL.Memory.State) (target : Mir.State) : Prop where
  current : ActivationRel locals ids source.current target.current
  suspended : CapabilityKontRel source.kont target.kont
  world : source.world = target.world

theorem binding_injective : Function.Injective binding := by
  intro a b h
  cases a; cases b
  cases h
  rfl

theorem binding_loan (l : ANL.Memory.Loan) : binding l.binding = (loan l).binding := rfl

theorem LocalsRel.length (h : LocalsRel a ls vs) : ls.length = vs.length := by
  induction h <;> simp_all

theorem LocalsRel.lookup {index : Nat} (h : LocalsRel a ls vs) (hi : ls[index]? = some l) :
    ∃ v, vs[index]? = some v ∧ localValue a l = some v := by
  induction h generalizing index with
  | nil => simp at hi
  | cons value _ ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
                subst l
                exact ⟨_, rfl, value⟩
      | succ index => exact ih (by simpa using hi)

theorem ResourcesRel.length (h : ResourcesRel ids bs rs) : ids.length = bs.length ∧ rs.length = bs.length := by
  induction h <;> simp_all

theorem ResourcesRel.keys (h : ResourcesRel ids bs rs) : rs.map Prod.fst = ids := by
  induction h <;> simp_all

theorem ResourcesRel.values (h : ResourcesRel ids bs rs) : rs.map Prod.snd = bs.map binding := by
  induction h <;> simp_all

end ANL.Memory.Simulation
