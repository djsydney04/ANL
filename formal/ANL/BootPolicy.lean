import ANL.BootSyntax

namespace ANL.Boot

open ANL.Words

inductive Ordered : Bool → List Declaration → Prop where
  | nil : Ordered phase []
  | defined : Ordered false rest → Ordered false (.defined d :: rest)
  | primitive : Ordered true rest → Ordered phase (.primitive p :: rest)

def checkOrdered : Bool → List Declaration → Bool
  | _, [] => true
  | false, .defined _ :: rest => checkOrdered false rest
  | true, .defined _ :: _ => false
  | _, .primitive _ :: rest => checkOrdered true rest

structure PrimitiveValid (p : Program) (d : Primitive) : Prop where
  name : d.name = "__hw_" ++ toString d.id
  identifier : ValidName d.name
  operation : d.operation.Valid p.entries.hardware.function
  params : d.params = d.operation.params
  result : d.result = d.operation.result
  effects : d.effects = d.operation.effects

def checkPrimitive (p : Program) (d : Primitive) : Bool :=
  decide (d.name = "__hw_" ++ toString d.id ∧ ValidName d.name ∧
    d.params = d.operation.params ∧ d.result = d.operation.result ∧ d.effects = d.operation.effects) &&
    checkOperation p.entries.hardware.function d.operation

def EffectSetValid (p : Program) (d : Defined) : Prop :=
  if d.function.id = p.entries.boot.function then d.effects = [0, 1]
  else if d.function.id ∈ [p.entries.hardware.function, p.entries.language.function] then d.effects = []
  else d.effects = [] ∨ d.effects = [1]

instance (p : Program) (d : Defined) : Decidable (EffectSetValid p d) := by
  unfold EffectSetValid; infer_instance

def TargetAllowed (p : Program) (effects : List Nat) (f : Nat) : Prop :=
  f ∉ p.roleIDs ∧ match p.functions[f]? with
  | some (.defined d) => ∀ e ∈ d.effects, e ∈ effects
  | some (.primitive d) => d.operation.effects = [1] ∧ ∀ e ∈ d.effects, e ∈ effects
  | none => False

instance (p : Program) (effects : List Nat) (f : Nat) : Decidable (TargetAllowed p effects f) := by
  unfold TargetAllowed
  cases p.functions[f]? with
  | none => infer_instance
  | some d => cases d <;> infer_instance

def BodyPolicy (p : Program) (effects : List Nat) (body : Term) : Prop :=
  MemoryFree body ∧ ∀ f ∈ calls body, TargetAllowed p effects f

def checkBodyPolicy (p : Program) (effects : List Nat) (body : Term) : Bool :=
  checkMemoryFree body && (calls body).all (fun f => decide (TargetAllowed p effects f))

inductive BootPrefix (p : Program) : Term → Term → Prop where
  | intro : p.operationAt clear = some (.csrClear 0 "sstatus" 2) →
      p.operationAt disable = some (.csrWrite 0 "sie" 0) →
      p.operationAt install = some (.installTrap 0 p.entries.hardware.function) →
      BootPrefix p
        (.letE unitTy (.call unitTy clear [])
          (.letE unitTy (.call unitTy disable [])
            (.letE unitTy (.call unitTy install []) rest))) rest

def bootRest (p : Program) : Term → Option Term
  | .letE t₁ (.call a₁ clear [])
      (.letE t₂ (.call a₂ disable [])
        (.letE t₃ (.call a₃ install []) rest)) =>
    if t₁ = unitTy ∧ a₁ = unitTy ∧ t₂ = unitTy ∧ a₂ = unitTy ∧ t₃ = unitTy ∧ a₃ = unitTy ∧
        p.operationAt clear = some (.csrClear 0 "sstatus" 2) ∧
        p.operationAt disable = some (.csrWrite 0 "sie" 0) ∧
        p.operationAt install = some (.installTrap 0 p.entries.hardware.function)
    then some rest else none
  | _ => none

def FunctionPolicy (p : Program) (d : Defined) : Prop :=
  if d.function.id = p.entries.boot.function then
    ∃ rest, BootPrefix p d.function.body rest ∧ BodyPolicy p d.effects rest
  else BodyPolicy p d.effects d.function.body

def checkFunctionPolicy (p : Program) (d : Defined) : Bool :=
  if d.function.id = p.entries.boot.function then
    match bootRest p d.function.body with
    | some rest => checkBodyPolicy p d.effects rest
    | none => false
  else checkBodyPolicy p d.effects d.function.body

structure DefinedValid (p : Program) (d : Defined) : Prop where
  name : UserName d.function.name
  view : d.function.view = none
  effects : EffectSetValid p d
  typed : HasType p.signatures d.function.valueContext [] d.function.body d.function.result
  policy : FunctionPolicy p d

def checkDefined (p : Program) (d : Defined) : Bool :=
  decide (UserName d.function.name ∧ d.function.view = none ∧ EffectSetValid p d) &&
  decide (checkTerm p.signatures d.function.valueContext [] d.function.body = some d.function.result) &&
  checkFunctionPolicy p d

def DeclarationValid (p : Program) : Declaration → Prop
  | .defined d => DefinedValid p d
  | .primitive d => PrimitiveValid p d

def checkDeclaration (p : Program) : Declaration → Bool
  | .defined d => checkDefined p d
  | .primitive d => checkPrimitive p d

inductive RoleValid (p : Program) (id : Nat) (params : List Ty) : Prop where
  | intro : p.functions[id]? = some (.defined d) → d.function.view = none →
      d.function.params = params → d.function.result = unitTy → RoleValid p id params

def checkRole (p : Program) (id : Nat) (params : List Ty) : Bool :=
  match p.functions[id]? with
  | some (.defined d) => decide (d.function.view = none ∧ d.function.params = params ∧ d.function.result = unitTy)
  | _ => false

structure RolesValid (p : Program) : Prop where
  boot : RoleValid p p.entries.boot.function [wordTy, wordTy]
  hardware : RoleValid p p.entries.hardware.function [wordTy, wordTy, wordTy]
  language : RoleValid p p.entries.language.function [byteTy]
  bootTail : ∀ d, p.functions[p.entries.boot.function]? = some (.defined d) → HasTail d.function.body
  hardwareBody : ∀ d, p.functions[p.entries.hardware.function]? = some (.defined d) → d.function.body = handler
  languageBody : ∀ d, p.functions[p.entries.language.function]? = some (.defined d) → d.function.body = handler

def roleBodyCheck (p : Program) (id : Nat) (check : Term → Bool) : Bool :=
  match p.functions[id]? with
  | some (.defined d) => check d.function.body
  | _ => false

def checkRoles (p : Program) : Bool :=
  checkRole p p.entries.boot.function [wordTy, wordTy] &&
  checkRole p p.entries.hardware.function [wordTy, wordTy, wordTy] &&
  checkRole p p.entries.language.function [byteTy] &&
  roleBodyCheck p p.entries.boot.function (fun body => (designatedTail body).isSome) &&
  roleBodyCheck p p.entries.hardware.function isHandler &&
  roleBodyCheck p p.entries.language.function isHandler

def Program.operationUses (p : Program) : List Operation :=
  p.defined.flatMap (fun d => (calls d.function.body).filterMap p.operationAt)

/-- A first occurrence is retained and all later equal keys are removed. -/
inductive FirstUses : List Operation → List Operation → Prop where
  | nil : FirstUses [] []
  | cons : FirstUses (rest.filter (fun op => decide (op ≠ first))) suffix →
      FirstUses (first :: rest) (first :: suffix)

def firstUses (uses : List Operation) : List Operation :=
  uses.eraseDupsBy (fun a b => decide (a = b))

def DiscoveryValid (p : Program) : Prop :=
  FirstUses p.operationUses (p.primitives.map Primitive.operation)

def checkDiscovery (p : Program) : Bool :=
  decide (firstUses p.operationUses = p.primitives.map Primitive.operation)

end ANL.Boot
