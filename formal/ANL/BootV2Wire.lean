import ANL.BootV2Check
import ANL.BootWire

namespace ANL.Boot.V2.Wire
open Lean

abbrev Decode := ANL.Memory.Wire.Decode
abbrev DecodeError := ANL.Memory.Wire.DecodeError
abbrev invalid := ANL.Memory.Wire.invalid
abbrev coreByteLimit := ANL.Memory.Wire.coreByteLimit

open ANL.Words.Wire (fields field str array nat ty parse)
open ANL.Boot.Wire (naturals types)

def operation (j : Json) : Decode Operation := do
  match ← str (← field j "tag") with
  | "illegal_instruction" =>
    fields j ["tag", "authority"]
    return .illegalInstruction (← nat (← field j "authority"))
  | _ => return .legacy (← ANL.Boot.Wire.operation j)

def declaration (j : Json) : Decode Declaration := do
  match ← str (← field j "kind") with
  | "defined" =>
    match ← ANL.Boot.Wire.declaration j with
    | .defined d => return .defined d
    | .primitive _ => throw (invalid "defined declaration decoded as primitive")
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
    ← str (← field j "ordinary_semantic_revision"), ← ANL.Boot.Wire.targetProfile (← field j "target_profile"),
    ← ANL.Boot.Wire.image (← field j "image"),
    (← (← array (← field j "stacks")).mapM ANL.Boot.Wire.stack).toList,
    (← (← array (← field j "devices")).mapM ANL.Boot.Wire.device).toList,
    ← ANL.Boot.Wire.entries (← field j "entries"),
    (← (← array (← field j "functions")).mapM declaration).toList⟩

def readCore (text : String) : Decode Program := do
  core (← parse text coreByteLimit)

def checkCoreDocument (text : String) : Decode Program := do
  let p ← readCore text
  if checkProgram p then return p
  else throw (invalid "v2 boot Core static policy rejected")

end ANL.Boot.V2.Wire
