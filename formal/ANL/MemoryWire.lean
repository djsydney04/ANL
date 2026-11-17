import ANL.MemoryPair
import APL.Wire

namespace ANL.Memory.Wire
open Lean

inductive ErrorKind where
  | invalid | resourceLimit
  deriving DecidableEq, Repr

structure DecodeError where
  kind : ErrorKind
  message : String
  deriving Repr

abbrev Decode := Except DecodeError

def invalid (message : String) : DecodeError := ⟨.invalid, message⟩
def limit (message : String) : DecodeError := ⟨.resourceLimit, message⟩
def lift (x : Except String α) : Decode α := x.mapError invalid

def coreByteLimit : Nat := 1048576
def mirByteLimit : Nat := 8388608
def logicalDepthLimit : Nat := 128
def jsonDepthLimit : Nat := 1024
def wireNatMax : Nat := 18446744073709551615

/-- One pass; numeric accumulation is bounded before every multiplication. -/
def preflight (bytes : ByteArray) (byteLimit : Nat) : Decode Unit := do
  if bytes.size > byteLimit then throw (limit "raw byte limit")
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  let mut numeric := false
  let mut leadingZero := false
  let mut number := 0
  for b in bytes do
    let n := b.toNat
    if quoted then
      if escaped then escaped := false
      else if n == 92 then escaped := true
      else if n == 34 then quoted := false
    else if 48 ≤ n && n ≤ 57 then
      let digit := n - 48
      if numeric then
        if leadingZero then throw (invalid "leading zero in JSON number")
        if number > (wireNatMax - digit) / 10 then
          throw (invalid "JSON number exceeds uint64")
      else
        numeric := true
        leadingZero := digit == 0
      number := number * 10 + digit
    else
      if numeric && !(n == 32 || n == 9 || n == 10 || n == 13 ||
          n == 44 || n == 93 || n == 125 || n == 58) then
        throw (invalid "noncanonical JSON number")
      numeric := false
      number := 0
      if n == 34 then quoted := true
      else if n == 123 || n == 91 then
        if depth ≥ jsonDepthLimit then throw (limit "JSON container depth limit")
        depth := depth + 1
      else if n == 125 || n == 93 then
        if depth == 0 then throw (invalid "unmatched JSON container close")
        depth := depth - 1
      else if n == 45 || n == 43 || n == 46 then
        throw (invalid "noncanonical JSON number")
  return ()

def parse (text : String) (byteLimit : Nat) : Decode Json := do
  preflight text.toUTF8 byteLimit
  lift (Json.parse text)

def fields (j : Json) (keys : List String) : Decode Unit := lift (APL.Wire.fields j keys)
def field (j : Json) (key : String) : Decode Json := lift (j.getObjVal? key)
def str (j : Json) : Decode String := lift j.getStr?
def boolean (j : Json) : Decode Bool := lift j.getBool?
def array (j : Json) : Decode (Array Json) := lift j.getArr?
def nat (j : Json) : Decode Nat := do
  let n ← lift j.getNat?
  if n > wireNatMax then throw (invalid "natural exceeds uint64")
  return n

def scalar (j : Json) : Decode APL.Ty := lift (APL.Wire.ty j)
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

def mode (j : Json) : Decode ViewMode := do
  match ← str j with
  | "read" => return .read
  | "edit" => return .edit
  | _ => throw (invalid "unknown view mode")

def optional (reader : Json → Decode α) (j : Json) : Decode (Option α) :=
  match j with
  | .null => pure none
  | _ => some <$> reader j

def profile (j : Json) : Decode Profile := do
  fields j ["abi", "char_bits", "i64_bytes", "i64_align", "size_bits", "ptrdiff_bits"]
  return ⟨← str (← field j "abi"), ← nat (← field j "char_bits"),
    ← nat (← field j "i64_bytes"), ← nat (← field j "i64_align"),
    ← nat (← field j "size_bits"), ← nat (← field j "ptrdiff_bits")⟩

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
      return .unary t (← lift (APL.Wire.uop (← field j "op"))) (← child "operand")
    | "binary" =>
      fields j ["tag", "ty", "op", "left", "right"]
      return .binary t (← lift (APL.Wire.bop (← field j "op"))) (← child "left") (← child "right")
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
    return .unary (← lift (APL.Wire.uop (← field j "op"))) (← ref "operand")
  | "binary" =>
    fields j ["tag", "op", "left", "right"]
    return .binary (← lift (APL.Wire.bop (← field j "op"))) (← ref "left") (← ref "right")
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

def checkDocuments (coreText mirText : String) : Decode (Program × Mir.Program) := do
  let c ← readCore coreText
  let m ← readMir mirText
  if Pair.check c m then return (c, m)
  else throw (invalid "independent typing or canonical pair check failed")

end ANL.Memory.Wire
