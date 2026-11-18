import ANL.WordsTyping
import ANL.WordsMirTyping
import ANL.MemoryWire

namespace ANL.Words.Wire
open Lean

abbrev ErrorKind := ANL.Memory.Wire.ErrorKind
abbrev DecodeError := ANL.Memory.Wire.DecodeError
abbrev Decode := ANL.Memory.Wire.Decode
abbrev invalid := ANL.Memory.Wire.invalid
abbrev limit := ANL.Memory.Wire.limit
abbrev lift {α : Type} (x : Except String α) : Decode α := ANL.Memory.Wire.lift x
abbrev coreByteLimit := ANL.Memory.Wire.coreByteLimit
abbrev mirByteLimit := ANL.Memory.Wire.mirByteLimit
abbrev logicalDepthLimit := ANL.Memory.Wire.logicalDepthLimit
abbrev jsonDepthLimit := ANL.Memory.Wire.jsonDepthLimit
abbrev wireNatMax := ANL.Memory.Wire.wireNatMax
abbrev preflight := ANL.Memory.Wire.preflight
abbrev parse := ANL.Memory.Wire.parse
abbrev fields := ANL.Memory.Wire.fields
abbrev field := ANL.Memory.Wire.field
abbrev str := ANL.Memory.Wire.str
abbrev boolean := ANL.Memory.Wire.boolean
abbrev array := ANL.Memory.Wire.array
abbrev nat := ANL.Memory.Wire.nat

def unsignedDigits : List UInt8 → Nat → Option Nat
  | [], value => if value ≤ wireNatMax then some value else none
  | byte :: rest, value =>
    let n := byte.toNat
    if n < 48 || n > 57 then none
    else
      let digit := n - 48
      if value > (wireNatMax - digit) / 10 then none
      else unsignedDigits rest (value * 10 + digit)

def unsignedText (text : String) : Option Nat := do
  if text.utf8ByteSize == 0 || text.utf8ByteSize > 20 then none else do
    let value ← unsignedDigits text.toUTF8.data.toList 0
    if toString value == text then some value else none

def unsigned (j : Json) : Decode Nat := do
  let text ← str j
  match unsignedText text with
  | some value => return value
  | none => throw (invalid "noncanonical or out-of-range unsigned literal")

def scalar (j : Json) : Decode ScalarTy := do
  match ← str j with
  | "u8" => return .word .w8
  | "u16" => return .word .w16
  | "u32" => return .word .w32
  | "u64" => return .word .w64
  | _ => return .legacy (← lift (APL.Wire.ty j))

def uop (j : Json) : Decode UOp := do
  match ← str j with
  | "bit_not" => return .bitNot
  | _ => return .legacy (← lift (APL.Wire.uop j))

def bop (j : Json) : Decode BOp := do
  match ← str j with
  | "wrap_add" => return .wrapAdd
  | "wrap_sub" => return .wrapSub
  | "wrap_mul" => return .wrapMul
  | "bit_and" => return .bitAnd
  | "bit_xor" => return .bitXor
  | "bit_or" => return .bitOr
  | "shl" => return .shl
  | "shr" => return .shr
  | _ => return .legacy (← lift (APL.Wire.bop j))

def convertMode (j : Json) : Decode ConvertMode := do
  match ← str j with
  | "checked" => return .checked
  | "truncate" => return .truncate
  | _ => throw (invalid "unknown conversion mode")

def ty (j : Json) : Decode Ty := do
  match j with
  | .str _ => return .scalar (← scalar j)
  | _ =>
    fields j ["tuple"]
    let raw ← array (← field j "tuple")
    if raw.size == 0 || raw.size > 8 then throw (invalid "invalid tuple width")
    let xs ← raw.mapM scalar
    match APL.FlatProducts.Flat.make xs.toList with
    | some shape => return .tuple shape
    | none => throw (invalid "invalid tuple shape")

abbrev mode := ANL.Memory.Wire.mode
abbrev optional {α : Type} (reader : Json → Decode α) (j : Json) : Decode (Option α) :=
  ANL.Memory.Wire.optional reader j
abbrev profile := ANL.Memory.Wire.profile

def terms (reader : Json → Decode Term) (j : Json) : Decode (List Term) := do
  Array.toList <$> ((← array j).mapM reader)

def term : Nat → Json → Decode Term
  | 0, _ => throw (limit "Core expression depth limit")
  | depth + 1, j => do
    let t ← ty (← field j "ty")
    let tag ← str (← field j "tag")
    let child key := do term depth (← field j key)
    let num key := do nat (← field j key)
    match tag with
    | "word" =>
      fields j ["tag", "ty", "width", "value"]
      return .word t (← num "width") (← unsigned (← field j "value"))
    | "convert" =>
      fields j ["tag", "ty", "mode", "target", "operand"]
      return .convert t (← convertMode (← field j "mode")) (← scalar (← field j "target")) (← child "operand")
    | "integer" =>
      fields j ["tag", "ty", "value"]
      return .lit t (← lift (APL.Wire.integer (← field j "value")))
    | "boolean" =>
      fields j ["tag", "ty", "value"]
      return .lit t (.bool (← boolean (← field j "value")))
    | "unit" =>
      fields j ["tag", "ty"]
      return .lit t .unit
    | "local" =>
      fields j ["tag", "ty", "index"]
      return .local t (← num "index")
    | "let" | "let_mut" =>
      fields j ["tag", "ty", "value", "body"]
      let a ← child "value"
      let b ← child "body"
      return if tag == "let" then .letE t a b else .letMut t a b
    | "assign" =>
      fields j ["tag", "ty", "index", "value"]
      return .assign t (← num "index") (← child "value")
    | "while" =>
      fields j ["tag", "ty", "condition", "body"]
      return .whileE t (← child "condition") (← child "body")
    | "if" =>
      fields j ["tag", "ty", "condition", "then", "else"]
      return .ifE t (← child "condition") (← child "then") (← child "else")
    | "unary" =>
      fields j ["tag", "ty", "op", "operand"]
      return .unary t (← uop (← field j "op")) (← child "operand")
    | "binary" =>
      fields j ["tag", "ty", "op", "left", "right"]
      return .binary t (← bop (← field j "op")) (← child "left") (← child "right")
    | "call" =>
      fields j ["tag", "ty", "function", "arguments"]
      return .call t (← num "function") (← terms (term depth) (← field j "arguments"))
    | "tuple" =>
      fields j ["tag", "ty", "fields"]
      return .tuple t (← terms (term depth) (← field j "fields"))
    | "project" =>
      fields j ["tag", "ty", "value", "index"]
      return .project t (← child "value") (← num "index")
    | "heap" =>
      fields j ["tag", "ty", "site", "length", "initial", "success", "failure"]
      return .heap t (← num "site") (← child "length") (← child "initial")
        (← child "success") (← child "failure")
    | "buffer_length" =>
      fields j ["tag", "ty", "resource"]
      return .bufferLength t (← num "resource")
    | "buffer_read" =>
      fields j ["tag", "ty", "resource", "index"]
      return .bufferRead t (← num "resource") (← child "index")
    | "buffer_write" =>
      fields j ["tag", "ty", "resource", "index", "value"]
      return .bufferWrite t (← num "resource") (← child "index") (← child "value")
    | "call_view" =>
      fields j ["tag", "ty", "function", "resource", "mode", "arguments"]
      return .callView t (← num "function") (← num "resource")
        (← mode (← field j "mode")) (← terms (term depth) (← field j "arguments"))
    | _ => throw (invalid "unknown Core constructor")

def coreFunction (j : Json) : Decode Function := do
  fields j ["id", "name", "view", "params", "result", "body"]
  return ⟨← nat (← field j "id"), ← str (← field j "name"),
    ← optional mode (← field j "view"),
    (← (← array (← field j "params")).mapM ty).toList,
    ← ty (← field j "result"), ← term logicalDepthLimit (← field j "body")⟩

def core (j : Json) : Decode Program := do
  fields j ["schema", "semantic_revision", "allocation_profile", "functions", "entry"]
  return ⟨← str (← field j "schema"), ← str (← field j "semantic_revision"),
    ← profile (← field j "allocation_profile"),
    ← (← array (← field j "functions")).mapM coreFunction, ← nat (← field j "entry")⟩

def temp (j : Json) : Decode Mir.Temp := do
  fields j ["id", "ty"]
  return ⟨← nat (← field j "id"), ← ty (← field j "ty")⟩

def slot (j : Json) : Decode Mir.Slot := do
  let t ← temp j
  return ⟨t.id, t.ty⟩

def temps (j : Json) : Decode (List Mir.Temp) := do
  Array.toList <$> ((← array j).mapM temp)

/-- Child-block recursion is provided once; a flat instruction does not spend depth. -/
def operation (childBlock : Json → Decode Mir.Block) (j : Json) : Decode Mir.Operation := do
  let tag ← str (← field j "tag")
  let ref key := do temp (← field j key)
  let num key := do nat (← field j key)
  let child key := do childBlock (← field j key)
  match tag with
  | "word" =>
    fields j ["tag", "width", "value"]
    return .word (← num "width") (← unsigned (← field j "value"))
  | "convert" =>
    fields j ["tag", "mode", "target", "operand"]
    return .convert (← convertMode (← field j "mode")) (← scalar (← field j "target")) (← ref "operand")
  | "integer" =>
    fields j ["tag", "value"]
    match ← lift (APL.Wire.integer (← field j "value")) with
    | .int n => return .integer n
    | _ => throw (invalid "invalid integer")
  | "boolean" =>
    fields j ["tag", "value"]
    return .boolean (← boolean (← field j "value"))
  | "unit" =>
    fields j ["tag"]
    return .unit
  | "tuple" =>
    fields j ["tag", "fields"]
    return .tuple (← temps (← field j "fields"))
  | "project" =>
    fields j ["tag", "value", "index"]
    return .project (← ref "value") (← num "index")
  | "unary" =>
    fields j ["tag", "op", "operand"]
    return .unary (← uop (← field j "op")) (← ref "operand")
  | "binary" =>
    fields j ["tag", "op", "left", "right"]
    return .binary (← bop (← field j "op")) (← ref "left") (← ref "right")
  | "call" =>
    fields j ["tag", "function", "arguments"]
    return .call (← num "function") (← temps (← field j "arguments"))
  | "mutable_scope" =>
    fields j ["tag", "slot", "initial", "body"]
    return .mutableScope (← slot (← field j "slot")) (← ref "initial") (← child "body")
  | "load" =>
    fields j ["tag", "slot"]
    return .load (← slot (← field j "slot"))
  | "store" =>
    fields j ["tag", "slot", "value"]
    return .store (← slot (← field j "slot")) (← ref "value")
  | "while" =>
    fields j ["tag", "condition", "body"]
    return .whileE (← child "condition") (← child "body")
  | "branch" =>
    fields j ["tag", "condition", "then", "else"]
    return .branch (← ref "condition") (← child "then") (← child "else")
  | "heap_scope" =>
    fields j ["tag", "site", "owner", "length", "initial", "success", "failure"]
    return .heapScope (← num "site") (← num "owner") (← ref "length")
      (← child "initial") (← child "success") (← child "failure")
  | "buffer_length" =>
    fields j ["tag", "resource"]
    return .bufferLength (← num "resource")
  | "buffer_read" =>
    fields j ["tag", "resource", "index"]
    return .bufferRead (← num "resource") (← ref "index")
  | "buffer_write" =>
    fields j ["tag", "resource", "index", "value"]
    return .bufferWrite (← num "resource") (← ref "index") (← child "value")
  | "call_view" =>
    fields j ["tag", "function", "resource", "mode", "arguments"]
    return .callView (← num "function") (← num "resource")
      (← mode (← field j "mode")) (← temps (← field j "arguments"))
  | _ => throw (invalid "unknown MIR operation")

def block : Nat → Json → Decode Mir.Block
  | 0, _ => throw (limit "MIR block depth limit")
  | depth + 1, j => do
    fields j ["instructions", "yield"]
    let instructions ← (← array (← field j "instructions")).mapM fun i => do
      fields i ["destination", "operation"]
      let destination ← temp (← field i "destination")
      let op ← operation (block depth) (← field i "operation")
      return (⟨destination, op⟩ : Mir.Instruction)
    return Mir.Block.fromInstructions instructions.toList (← temp (← field j "yield"))

def mirView (j : Json) : Decode (ViewMode × Nat) := do
  fields j ["mode", "resource"]
  return (← mode (← field j "mode"), ← nat (← field j "resource"))

def mirFunction (j : Json) : Decode Mir.Function := do
  fields j ["id", "view", "params", "result", "body", "temp_count", "slot_count", "resource_count"]
  return ⟨← nat (← field j "id"), ← optional mirView (← field j "view"),
    ← temps (← field j "params"), ← ty (← field j "result"),
    ← block logicalDepthLimit (← field j "body"),
    ← nat (← field j "temp_count"), ← nat (← field j "slot_count"), ← nat (← field j "resource_count")⟩

def mir (j : Json) : Decode Mir.Program := do
  fields j ["schema", "semantic_revision", "allocation_profile", "functions", "entry"]
  return ⟨← str (← field j "schema"), ← str (← field j "semantic_revision"),
    ← profile (← field j "allocation_profile"),
    ← (← array (← field j "functions")).mapM mirFunction, ← nat (← field j "entry")⟩

def readCore (text : String) : Decode Program := do core (← parse text coreByteLimit)
def readMir (text : String) : Decode Mir.Program := do mir (← parse text mirByteLimit)

def checkCoreDocument (text : String) : Decode Program := do
  let p ← readCore text
  if checkProgram p then return p else throw (invalid "Core static check failed")

def checkMirDocument (text : String) : Decode Mir.Program := do
  let p ← readMir text
  if Mir.checkProgram p then return p else throw (invalid "MIR static check failed")

end ANL.Words.Wire
