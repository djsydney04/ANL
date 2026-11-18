import ANL.BootSyntax

namespace ANL.Boot.V2
open ANL.Words

/-- An explicit sum, never an old operation used as a stand-in for the new one. -/
inductive Operation where
  | legacy (operation : ANL.Boot.Operation)
  | illegalInstruction (authority : Nat)
  deriving DecidableEq, Repr

def Operation.params : Operation → List Ty
  | .legacy op => op.params
  | .illegalInstruction _ => []

def Operation.result : Operation → Ty
  | .legacy op => op.result
  | .illegalInstruction _ => unitTy

def Operation.effects : Operation → List Nat
  | .legacy op => op.effects
  | .illegalInstruction _ => [0]

def Operation.signature (op : Operation) : Signature := ⟨none, op.params, op.result⟩

inductive Operation.Valid (hardware : Nat) : Operation → Prop where
  | legacy : op.Valid hardware → Valid hardware (.legacy op)
  | illegalInstruction : Valid hardware (.illegalInstruction 0)

def checkOperation (hardware : Nat) : Operation → Bool
  | .legacy op => ANL.Boot.checkOperation hardware op
  | .illegalInstruction authority => decide (authority = 0)

/-- Outside the exact boot prefix, old machine operations remain forbidden. -/
def Operation.RestAllowed : Operation → Prop
  | .legacy op => op.effects = [1]
  | .illegalInstruction authority => authority = 0

instance (op : Operation) : Decidable op.RestAllowed := by
  cases op <;> unfold Operation.RestAllowed <;> infer_instance

abbrev Defined := ANL.Boot.Defined

structure Primitive where
  id : Nat
  name : String
  operation : Operation
  params : List Ty
  result : Ty
  effects : List Nat
  deriving DecidableEq, Repr

inductive Declaration where
  | defined (value : Defined)
  | primitive (value : Primitive)
  deriving Repr

def Declaration.id : Declaration → Nat
  | .defined d => d.function.id
  | .primitive p => p.id
def Declaration.name : Declaration → String
  | .defined d => d.function.name
  | .primitive p => p.name
def Declaration.signature : Declaration → Signature
  | .defined d => d.function.signature
  | .primitive p => ⟨none, p.params, p.result⟩
def Declaration.effects : Declaration → List Nat
  | .defined d => d.effects
  | .primitive p => p.effects

/-- Every field is raw. The ordinary syntax is the unchanged Words term language. -/
structure Program where
  schema : String
  semanticRevision : String
  ordinaryRevision : String
  profile : TargetProfile
  image : Image
  stacks : List Stack
  devices : List Device
  entries : Entries
  functions : List Declaration
  deriving Repr

def targetProfile : TargetProfile :=
  { ANL.Boot.targetProfile with id := "rv64-virt-sbi-v2" }

def Program.signatures (p : Program) : Signatures :=
  (p.functions.map Declaration.signature).toArray
def Program.defined (p : Program) : List Defined :=
  p.functions.filterMap (fun d => match d with | .defined f => some f | _ => none)
def Program.primitives (p : Program) : List Primitive :=
  p.functions.filterMap (fun d => match d with | .primitive f => some f | _ => none)
def Program.roleIDs (p : Program) : List Nat :=
  [p.entries.boot.function, p.entries.hardware.function, p.entries.language.function]
def Program.operationAt (p : Program) (id : Nat) : Option Operation :=
  match p.functions[id]? with
  | some (.primitive op) => some op.operation
  | _ => none

structure MetadataValid (p : Program) : Prop where
  schema : p.schema = "anl-boot-core-v2"
  revision : p.semanticRevision = "anl-boot-rv64-virt-v2"
  ordinary : p.ordinaryRevision = "anl-words-v1"
  profile : p.profile = targetProfile
  image : p.image = ANL.Boot.image
  stacks : p.stacks = ANL.Boot.stacks
  devices : p.devices = ANL.Boot.devices
  roleStacks : p.entries.boot.stack = 0 ∧ p.entries.hardware.stack = 1 ∧ p.entries.language.stack = 1
  roleDistinct : p.roleIDs.Nodup

def checkMetadata (p : Program) : Bool :=
  decide (p.schema = "anl-boot-core-v2" ∧ p.semanticRevision = "anl-boot-rv64-virt-v2" ∧
    p.ordinaryRevision = "anl-words-v1" ∧ p.profile = targetProfile ∧
    p.image = ANL.Boot.image ∧ p.stacks = ANL.Boot.stacks ∧ p.devices = ANL.Boot.devices ∧
    (p.entries.boot.stack = 0 ∧ p.entries.hardware.stack = 1 ∧ p.entries.language.stack = 1) ∧
    p.roleIDs.Nodup)

end ANL.Boot.V2
