import ANL.WordsTyping

namespace ANL.Boot

open ANL.Words

abbrev unitTy : Ty := .scalar (.legacy .unit)
abbrev boolTy : Ty := .scalar (.legacy .bool)
abbrev byteTy : Ty := .scalar (.word .w8)
abbrev wordTy : Ty := .scalar (.word .w64)

structure TargetProfile where
  id : String
  generatedISA : String
  abi : String
  endianness : String
  privilege : String
  translation : String
  harts : Nat
  ramBase : Nat
  ramBytes : Nat
  deriving DecidableEq, Repr

structure Image where
  base : Nat
  limit : Nat
  deriving DecidableEq, Repr

structure Stack where
  id : Nat
  name : String
  bytes : Nat
  alignment : Nat
  deriving DecidableEq, Repr

structure Device where
  id : Nat
  name : String
  authority : Nat
  base : Nat
  size : Nat
  read8 : List Nat
  write8 : List Nat
  deriving DecidableEq, Repr

structure Role where
  function : Nat
  stack : Nat
  deriving DecidableEq, Repr

structure Entries where
  boot : Role
  hardware : Role
  language : Role
  deriving DecidableEq, Repr

def targetProfile : TargetProfile :=
  ⟨"rv64-virt-sbi-v1", "rv64im_zicsr", "lp64", "little", "s", "bare", 1,
    2147483648, 134217728⟩

def image : Image := ⟨2149580800, 1048576⟩

def stacks : List Stack :=
  [⟨0, "boot_stack", 16384, 16⟩, ⟨1, "terminal_stack", 4096, 16⟩]

def devices : List Device :=
  [⟨0, "uart0", 1, 268435456, 256, [5], [0, 1, 2, 3, 4]⟩]

/-- The closed operation tags keep all selector and integer errors representable. -/
inductive Operation where
  | read8 (region offset : Nat)
  | write8 (region offset : Nat)
  | fence (region : Nat)
  | csrClear (authority : Nat) (register : String) (mask : Nat)
  | csrWrite (authority : Nat) (register : String) (value : Nat)
  | installTrap (authority handler : Nat)
  deriving DecidableEq, Repr

def Operation.params : Operation → List Ty
  | .write8 _ _ => [byteTy]
  | _ => []

def Operation.result : Operation → Ty
  | .read8 _ _ => byteTy
  | _ => unitTy

def Operation.effects : Operation → List Nat
  | .read8 _ _ | .write8 _ _ | .fence _ => [1]
  | _ => [0]

def Operation.signature (op : Operation) : Signature :=
  ⟨none, op.params, op.result⟩

inductive Operation.Valid (hardware : Nat) : Operation → Prop where
  | read8 : Valid hardware (.read8 0 5)
  | write8 : offset ∈ [0, 1, 2, 3, 4] → Valid hardware (.write8 0 offset)
  | fence : Valid hardware (.fence 0)
  | csrClear : Valid hardware (.csrClear 0 "sstatus" 2)
  | csrWrite : Valid hardware (.csrWrite 0 "sie" 0)
  | installTrap : Valid hardware (.installTrap 0 hardware)

def checkOperation (hardware : Nat) : Operation → Bool
  | .read8 region offset => decide (region = 0 ∧ offset = 5)
  | .write8 region offset => decide (region = 0 ∧ offset ∈ [0, 1, 2, 3, 4])
  | .fence region => decide (region = 0)
  | .csrClear authority register mask => decide (authority = 0 ∧ register = "sstatus" ∧ mask = 2)
  | .csrWrite authority register value => decide (authority = 0 ∧ register = "sie" ∧ value = 0)
  | .installTrap authority handler => decide (authority = 0 ∧ handler = hardware)

structure Defined where
  function : Function
  effects : List Nat
  deriving Repr

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

def UserName (name : String) : Prop :=
  ValidName name ∧ ¬ name.startsWith "__hw_" ∧ ¬ name.startsWith "__carrier_"

instance (name : String) : Decidable (UserName name) := by unfold UserName; infer_instance

structure MetadataValid (p : Program) : Prop where
  schema : p.schema = "anl-boot-core-v1"
  revision : p.semanticRevision = "anl-boot-rv64-virt-v1"
  ordinary : p.ordinaryRevision = "anl-words-v1"
  profile : p.profile = targetProfile
  image : p.image = ANL.Boot.image
  stacks : p.stacks = ANL.Boot.stacks
  devices : p.devices = ANL.Boot.devices
  roleStacks : p.entries.boot.stack = 0 ∧ p.entries.hardware.stack = 1 ∧ p.entries.language.stack = 1
  roleDistinct : p.roleIDs.Nodup

def checkMetadata (p : Program) : Bool :=
  decide (p.schema = "anl-boot-core-v1" ∧ p.semanticRevision = "anl-boot-rv64-virt-v1" ∧
    p.ordinaryRevision = "anl-words-v1" ∧ p.profile = targetProfile ∧
    p.image = ANL.Boot.image ∧ p.stacks = ANL.Boot.stacks ∧ p.devices = ANL.Boot.devices ∧
    (p.entries.boot.stack = 0 ∧ p.entries.hardware.stack = 1 ∧ p.entries.language.stack = 1) ∧
    p.roleIDs.Nodup)

end ANL.Boot
