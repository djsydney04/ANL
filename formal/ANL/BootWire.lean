import ANL.BootCheck
import ANL.WordsWire

namespace ANL.Boot.Wire
open Lean

abbrev Decode := ANL.Memory.Wire.Decode
abbrev DecodeError := ANL.Memory.Wire.DecodeError
abbrev ErrorKind := ANL.Memory.Wire.ErrorKind
abbrev invalid := ANL.Memory.Wire.invalid
abbrev coreByteLimit := ANL.Memory.Wire.coreByteLimit
abbrev logicalDepthLimit := ANL.Memory.Wire.logicalDepthLimit
abbrev jsonDepthLimit := ANL.Memory.Wire.jsonDepthLimit

open ANL.Words.Wire (fields field str array nat unsigned ty optional mode term parse)

def naturals (j : Json) : Decode (List Nat) := do
  return (← (← array j).mapM nat).toList

def types (j : Json) : Decode (List ANL.Words.Ty) := do
  return (← (← array j).mapM ty).toList

def targetProfile (j : Json) : Decode TargetProfile := do
  fields j ["id", "generated_isa", "abi", "endianness", "privilege", "translation",
    "harts", "ram_base", "ram_bytes"]
  return ⟨← str (← field j "id"), ← str (← field j "generated_isa"),
    ← str (← field j "abi"), ← str (← field j "endianness"),
    ← str (← field j "privilege"), ← str (← field j "translation"),
    ← nat (← field j "harts"), ← unsigned (← field j "ram_base"),
    ← nat (← field j "ram_bytes")⟩

def image (j : Json) : Decode Image := do
  fields j ["base", "limit"]
  return ⟨← unsigned (← field j "base"), ← nat (← field j "limit")⟩

def stack (j : Json) : Decode Stack := do
  fields j ["id", "name", "bytes", "alignment"]
  return ⟨← nat (← field j "id"), ← str (← field j "name"),
    ← nat (← field j "bytes"), ← nat (← field j "alignment")⟩

def device (j : Json) : Decode Device := do
  fields j ["id", "name", "authority", "base", "size", "read8", "write8"]
  return ⟨← nat (← field j "id"), ← str (← field j "name"),
    ← nat (← field j "authority"), ← unsigned (← field j "base"),
    ← nat (← field j "size"), ← naturals (← field j "read8"),
    ← naturals (← field j "write8")⟩

def role (j : Json) : Decode Role := do
  fields j ["function", "stack"]
  return ⟨← nat (← field j "function"), ← nat (← field j "stack")⟩

def entries (j : Json) : Decode Entries := do
  fields j ["boot", "hardware", "language"]
  return ⟨← role (← field j "boot"), ← role (← field j "hardware"),
    ← role (← field j "language")⟩

def operation (j : Json) : Decode Operation := do
  match ← str (← field j "tag") with
  | "mmio_read8" =>
    fields j ["tag", "region", "offset"]
    return .read8 (← nat (← field j "region")) (← nat (← field j "offset"))
  | "mmio_write8" =>
    fields j ["tag", "region", "offset"]
    return .write8 (← nat (← field j "region")) (← nat (← field j "offset"))
  | "io_fence" =>
    fields j ["tag", "region"]
    return .fence (← nat (← field j "region"))
  | "csr_clear" =>
    fields j ["tag", "authority", "register", "mask"]
    return .csrClear (← nat (← field j "authority")) (← str (← field j "register"))
      (← unsigned (← field j "mask"))
  | "csr_write" =>
    fields j ["tag", "authority", "register", "value"]
    return .csrWrite (← nat (← field j "authority")) (← str (← field j "register"))
      (← unsigned (← field j "value"))
  | "install_trap" =>
    fields j ["tag", "authority", "handler"]
    return .installTrap (← nat (← field j "authority")) (← nat (← field j "handler"))
  | _ => throw (invalid "unknown boot primitive operation")

def declaration (j : Json) : Decode Declaration := do
  match ← str (← field j "kind") with
  | "defined" =>
    fields j ["kind", "id", "name", "view", "params", "result", "effects", "body"]
    let function : ANL.Words.Function := ⟨← nat (← field j "id"), ← str (← field j "name"),
      ← optional mode (← field j "view"), ← types (← field j "params"),
      ← ty (← field j "result"), ← term logicalDepthLimit (← field j "body")⟩
    return .defined ⟨function, ← naturals (← field j "effects")⟩
  | "primitive" =>
    fields j ["kind", "id", "name", "operation", "params", "result", "effects"]
    return .primitive ⟨← nat (← field j "id"), ← str (← field j "name"),
      ← operation (← field j "operation"), ← types (← field j "params"),
      ← ty (← field j "result"), ← naturals (← field j "effects")⟩
  | _ => throw (invalid "unknown boot declaration kind")

def core (j : Json) : Decode Program := do
  fields j ["schema", "semantic_revision", "ordinary_semantic_revision", "target_profile",
    "image", "stacks", "devices", "entries", "functions"]
  return ⟨← str (← field j "schema"), ← str (← field j "semantic_revision"),
    ← str (← field j "ordinary_semantic_revision"), ← targetProfile (← field j "target_profile"),
    ← image (← field j "image"), (← (← array (← field j "stacks")).mapM stack).toList,
    (← (← array (← field j "devices")).mapM device).toList,
    ← entries (← field j "entries"),
    (← (← array (← field j "functions")).mapM declaration).toList⟩

def readCore (text : String) : Decode Program := do
  core (← parse text coreByteLimit)

def checkCoreDocument (text : String) : Decode Program := do
  let p ← readCore text
  if checkProgram p then return p
  else throw (invalid "boot Core static policy rejected")

end ANL.Boot.Wire
