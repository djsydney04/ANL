import ANL.BootReferenceRequest
import ANL.WordsWireSafety

namespace ANL.Boot.Reference
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session
open ANL.Words.Wire (fields field str array nat unsigned parse)

def requestSchema : String := "anl-boot-reference-request-v1"
def requestByteLimit : Nat := 1048576
def requestDepthLimit : Nat := 16

/-- This additional transport guard runs before the unchanged strict parser. It does not certify JSON syntax. -/
def requestDepth (bytes : ByteArray) : Decode Unit := do
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for b in bytes do
    let n := b.toNat
    if quoted then
      if escaped then escaped := false
      else if n == 92 then escaped := true
      else if n == 34 then quoted := false
    else if n == 34 then quoted := true
    else if n == 123 || n == 91 then
      if depth ≥ requestDepthLimit then throw (limit "reference request JSON depth limit")
      depth := depth + 1
    else if n == 125 || n == 93 then depth := depth - 1
  return ()

def boundedArray (j : Json) (bound : Nat) (message : String) : Decode (Array Json) := do
  let values ← array j
  if values.size > bound then throw (limit message)
  return values

def readByte (j : Json) : Decode Nat := do
  let value ← nat j
  if value ≥ byteModulus then throw (invalid "reference read is not a byte")
  return value

def readInitial (j : Json) : Decode Environment := do
  fields j ["sstatus", "sie", "hart", "opaque_dtb"]
  return ⟨← unsigned (← field j "sstatus"), ← unsigned (← field j "sie"),
    ← unsigned (← field j "hart"), ← unsigned (← field j "opaque_dtb"), [], none⟩

def readTailEdge (j : Json) : Decode Origin.Edge := do
  fields j ["edge"]
  match ← str (← field j "edge") with
  | "letValue" => return .letValue
  | "letBody" => return .letBody
  | _ => throw (invalid "invalid delivery origin edge")

def readOrigin (j : Json) : Decode Origin.Location := do
  fields j ["function", "core_path"]
  let function ← nat (← field j "function")
  let path ← boundedArray (← field j "core_path") originLimit "reference delivery origin limit"
  return ⟨function, (← path.mapM readTailEdge).toList⟩

def readLandmark (j : Json) : Decode Landmark := do
  match ← str (← field j "kind") with
  | "before_primitive" | "after_primitive" =>
    fields j ["kind", "ordinal", "declaration"]
    let ordinal ← nat (← field j "ordinal")
    if ordinal == 0 then throw (invalid "zero delivery ordinal")
    let declaration ← nat (← field j "declaration")
    if (← str (← field j "kind")) == "before_primitive" then
      return .beforePrimitive ordinal declaration
    else return .afterPrimitive ordinal declaration
  | "boot_park" =>
    fields j ["kind", "origin"]
    return .bootPark (← readOrigin (← field j "origin"))
  | _ => throw (invalid "unknown delivery landmark")

def readDelivery (j : Json) : Decode (Option Delivery) := do
  match j with
  | .null => return none
  | _ =>
    fields j ["landmark", "scause", "sepc", "stval"]
    return some ⟨← readLandmark (← field j "landmark"), ← unsigned (← field j "scause"),
      ← unsigned (← field j "sepc"), ← unsigned (← field j "stval")⟩

def readAction (j : Json) : Decode Action := do
  fields j ["kind", "transitions"]
  let kind ← match ← str (← field j "kind") with
    | "run" => pure ActionKind.run
    | "continue" => pure ActionKind.continue
    | "resume" => pure ActionKind.resume
    | _ => throw (invalid "unknown reference action")
  return ⟨kind, ← nat (← field j "transitions")⟩

def decodeRequest (j : Json) : Decode Request := do
  fields j ["schema", "initial", "reads", "delivery", "actions"]
  if (← str (← field j "schema")) != requestSchema then throw (invalid "unknown reference request schema")
  let initial ← readInitial (← field j "initial")
  let reads ← boundedArray (← field j "reads") readLimit "reference read vector limit"
  let readValues ← reads.mapM readByte
  let delivery ← readDelivery (← field j "delivery")
  let actions ← boundedArray (← field j "actions") actionLimit "reference action count limit"
  let actionValues ← actions.mapM readAction
  return ⟨{initial with reads := readValues.toList, delivery := delivery}, actionValues.toList⟩

def readRequest (text : String) : Decode Request := do
  if text.utf8ByteSize > requestByteLimit then throw (limit "reference request byte limit")
  requestDepth text.toUTF8
  decodeRequest (← parse text requestByteLimit)

def checkRequestDocument (p : Program) (text : String) : Decode Request := do
  checkRequest p (← readRequest text)

structure Input where
  program : Program
  request : Request
  deriving Repr

/-- Core admission/static checking precedes even request parsing. No runtime state is created here. -/
def checkDocuments (coreText requestText : String) : Decode Input := do
  let p ← checkCoreDocument coreText
  let request ← checkRequestDocument p requestText
  return ⟨p, request⟩

end ANL.Boot.Reference
