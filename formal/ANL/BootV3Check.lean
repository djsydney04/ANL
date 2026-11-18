import ANL.BootV2Check

namespace ANL.Boot.V3

open ANL.Words

abbrev Program := V2.Program
abbrev Defined := V2.Defined
abbrev Declaration := V2.Declaration

def targetProfile : TargetProfile :=
  { ANL.Boot.targetProfile with id := "rv64-virt-sbi-v3" }

structure MetadataValid (p : Program) : Prop where
  schema : p.schema = "anl-boot-core-v3"
  revision : p.semanticRevision = "anl-boot-rv64-virt-v3"
  ordinary : p.ordinaryRevision = "anl-words-v1"
  profile : p.profile = targetProfile
  image : p.image = ANL.Boot.image
  stacks : p.stacks = ANL.Boot.stacks
  devices : p.devices = ANL.Boot.devices
  roleStacks : p.entries.boot.stack = 0 ∧ p.entries.hardware.stack = 1 ∧ p.entries.language.stack = 1
  roleDistinct : p.roleIDs.Nodup

def checkMetadata (p : Program) : Bool :=
  decide (p.schema = "anl-boot-core-v3" ∧ p.semanticRevision = "anl-boot-rv64-virt-v3" ∧
    p.ordinaryRevision = "anl-words-v1" ∧ p.profile = targetProfile ∧
    p.image = ANL.Boot.image ∧ p.stacks = ANL.Boot.stacks ∧ p.devices = ANL.Boot.devices ∧
    (p.entries.boot.stack = 0 ∧ p.entries.hardware.stack = 1 ∧ p.entries.language.stack = 1) ∧
    p.roleIDs.Nodup)

def EffectSetValid (p : Program) (d : Defined) : Prop :=
  if d.function.id = p.entries.boot.function then d.effects = [0, 1]
  else if d.function.id = p.entries.hardware.function then d.effects = [] ∨ d.effects = [1]
  else if d.function.id = p.entries.language.function then d.effects = []
  else d.effects = [] ∨ d.effects = [1]

instance (p : Program) (d : Defined) : Decidable (EffectSetValid p d) := by
  unfold EffectSetValid
  infer_instance

structure DefinedValid (p : Program) (d : Defined) : Prop where
  name : UserName d.function.name
  view : d.function.view = none
  effects : EffectSetValid p d
  typed : HasType p.signatures d.function.valueContext [] d.function.body d.function.result
  policy : V2.FunctionPolicy p d

def checkDefined (p : Program) (d : Defined) : Bool :=
  decide (UserName d.function.name ∧ d.function.view = none ∧ EffectSetValid p d) &&
  decide (checkTerm p.signatures d.function.valueContext [] d.function.body = some d.function.result) &&
  V2.checkFunctionPolicy p d

def DeclarationValid (p : Program) : Declaration → Prop
  | .defined d => DefinedValid p d
  | .primitive d => V2.PrimitiveValid p d

def checkDeclaration (p : Program) : Declaration → Bool
  | .defined d => checkDefined p d
  | .primitive d => V2.checkPrimitive p d

structure RolesValid (p : Program) : Prop where
  boot : V2.RoleValid p p.entries.boot.function [wordTy, wordTy]
  hardware : V2.RoleValid p p.entries.hardware.function [wordTy, wordTy, wordTy]
  language : V2.RoleValid p p.entries.language.function [byteTy]
  bootTail : ∀ d, p.functions[p.entries.boot.function]? = some (.defined d) → HasTail d.function.body
  hardwareTail : ∀ d, p.functions[p.entries.hardware.function]? = some (.defined d) → HasTail d.function.body
  languageBody : ∀ d, p.functions[p.entries.language.function]? = some (.defined d) → d.function.body = handler

def checkRoles (p : Program) : Bool :=
  V2.checkRole p p.entries.boot.function [wordTy, wordTy] &&
  V2.checkRole p p.entries.hardware.function [wordTy, wordTy, wordTy] &&
  V2.checkRole p p.entries.language.function [byteTy] &&
  V2.roleBodyCheck p p.entries.boot.function (fun body => (designatedTail body).isSome) &&
  V2.roleBodyCheck p p.entries.hardware.function (fun body => (designatedTail body).isSome) &&
  V2.roleBodyCheck p p.entries.language.function isHandler

structure WellFormedProgram (p : Program) : Prop where
  metadata : MetadataValid p
  ordered : V2.Ordered false p.functions
  ids : p.functions.map V2.Declaration.id = List.range p.functions.length
  names : (p.functions.map V2.Declaration.name).Nodup
  declarations : ∀ d ∈ p.functions, DeclarationValid p d
  roles : RolesValid p
  discovery : V2.DiscoveryValid p
  acyclic : V2.Acyclic p

def checkProgram (p : Program) : Bool :=
  checkMetadata p && V2.checkOrdered false p.functions &&
  decide (p.functions.map V2.Declaration.id = List.range p.functions.length) &&
  decide (p.functions.map V2.Declaration.name).Nodup &&
  p.functions.all (checkDeclaration p) && checkRoles p && V2.checkDiscovery p && V2.checkGraph p

end ANL.Boot.V3
