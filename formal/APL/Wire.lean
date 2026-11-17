import APL.Program
import Lean.Data.Json

namespace APL.Wire
open Lean
open Program

abbrev Decode := Except String

def asciiDigit (c : Char) : Bool := c ≥ '0' && c ≤ '9'
def numericChar (c : Char) : Bool := asciiDigit c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

partial def lexicalCheck (cs : List Char) (depth : Nat := 0) (quoted := false) (escaped := false) : Decode Unit := do
  match cs with
  | [] => pure ()
  | c :: rest =>
    if quoted then
      if escaped then lexicalCheck rest depth true false
      else if c == '\\' then lexicalCheck rest depth true true
      else lexicalCheck rest depth (c != '"') false
    else if c == '"' then lexicalCheck rest depth true false
    else if c == '{' || c == '[' then
      if depth ≥ 256 then throw "JSON nesting limit"
      lexicalCheck rest (depth + 1)
    else if c == '}' || c == ']' then lexicalCheck rest (depth - 1)
    else if asciiDigit c || c == '-' then
      let (tail, remaining) := rest.span numericChar
      let chars := c :: tail
      if !chars.all asciiDigit || chars.length > 10 then throw "invalid index representation"
      lexicalCheck remaining depth
    else lexicalCheck rest depth

def fields (j : Json) (expected : List String) : Decode Unit := do
  let obj ← j.getObj?
  let keys := obj.toList.map Prod.fst
  if keys.length != expected.length || !keys.all expected.contains then
    throw "unknown or missing object field"

def field (j : Json) (key : String) : Decode Json := j.getObjVal? key

def nat (j : Json) : Decode Nat := do
  let n ← j.getNat?
  if n > 4294967295 then throw "index out of range"
  return n

def ty (j : Json) : Decode Ty := do
  match ← j.getStr? with
  | "i64" => pure .i64
  | "bool" => pure .bool
  | "unit" => pure .unit
  | _ => throw "unknown scalar type"

def uop (j : Json) : Decode UOp := do
  match ← j.getStr? with
  | "neg" => pure .neg
  | "not" => pure .not
  | _ => throw "unknown unary operator"

def bop (j : Json) : Decode BOp := do
  match ← j.getStr? with
  | "add" => pure .add | "sub" => pure .sub | "mul" => pure .mul
  | "div" => pure .div | "rem" => pure .rem
  | "lt" => pure .lt | "le" => pure .le | "gt" => pure .gt | "ge" => pure .ge
  | "eq" => pure .eq | "ne" => pure .ne | "and" => pure .and | "or" => pure .or
  | _ => throw "unknown binary operator"

def integer (j : Json) : Decode Val := do
  let s ← j.getStr?
  if s.utf8ByteSize > 20 then throw "integer outside i64"
  let some n := s.toInt? | throw "invalid integer"
  if toString n != s then throw "noncanonical integer"
  if h : InRange n then return .int ⟨n, h⟩ else throw "integer outside i64"

def needSome (x : Option α) : Decode α := match x with | some v => .ok v | none => .error "invalid type or reference"

def term (fs : Signatures) : Nat → Ctx → Json → Decode (Program.Term × Ty)
  | 0, _, _ => throw "expression depth limit"
  | depth + 1, Γ, j => do
    let declared ← ty (← field j "ty")
    let tag ← (← field j "tag").getStr?
    let (e, actual) ← match tag with
      | "integer" => do
        fields j ["tag", "ty", "value"]
        let v ← integer (← field j "value")
        pure (.lit v, .i64)
      | "boolean" => do
        fields j ["tag", "ty", "value"]
        pure (.lit (.bool (← (← field j "value").getBool?)), .bool)
      | "unit" => do
        fields j ["tag", "ty"]
        pure (.lit .unit, .unit)
      | "local" => do
        fields j ["tag", "ty", "index"]
        let i ← nat (← field j "index")
        pure (.local i, ← needSome Γ[i]?)
      | "let" => do
        fields j ["tag", "ty", "value", "body"]
        let (a, ta) ← term fs depth Γ (← field j "value")
        let (b, tb) ← term fs depth (ta :: Γ) (← field j "body")
        pure (.letE a b, tb)
      | "if" => do
        fields j ["tag", "ty", "condition", "then", "else"]
        let (c, tc) ← term fs depth Γ (← field j "condition")
        let (a, ta) ← term fs depth Γ (← field j "then")
        let (b, tb) ← term fs depth Γ (← field j "else")
        if tc ≠ .bool ∨ ta ≠ tb then throw "invalid conditional types"
        pure (.ifE c a b, ta)
      | "unary" => do
        fields j ["tag", "ty", "op", "operand"]
        let op ← uop (← field j "op")
        let (a, ta) ← term fs depth Γ (← field j "operand")
        if ta ≠ op.input then throw "invalid unary operand"
        pure (.unary op a, op.output)
      | "binary" => do
        fields j ["tag", "ty", "op", "left", "right"]
        let op ← bop (← field j "op")
        let (a, ta) ← term fs depth Γ (← field j "left")
        let (b, tb) ← term fs depth Γ (← field j "right")
        pure (.binary op a b, ← needSome (binaryType op ta tb))
      | "call" => do
        fields j ["tag", "ty", "function", "arguments"]
        let f ← nat (← field j "function")
        let (params, result) ← needSome fs[f]?
        let args ← (← (← field j "arguments").getArr?).toList.mapM (term fs depth Γ)
        if args.map Prod.snd ≠ params then throw "invalid call arguments"
        pure (.call f (args.map Prod.fst), result)
      | _ => throw "unknown expression constructor"
    if actual ≠ declared then throw "incorrect serialized type"
    return (e, actual)

def identifier (s : String) : Bool :=
  let start c := c == '_' || (c ≥ 'a' && c ≤ 'z') || (c ≥ 'A' && c ≤ 'Z')
  match s.toList with
  | [] => false
  | c :: cs => start c && cs.all (fun c => start c || asciiDigit c) &&
      !["fn", "let", "if", "else", "true", "false", "i64", "bool", "unit"].contains s

def signature (index : Nat) (j : Json) : Decode (String × Signature) := do
  fields j ["id", "name", "params", "result", "body"]
  let id ← nat (← field j "id")
  if id ≠ index then throw "function ID differs from table index"
  let name ← (← field j "name").getStr?
  if !identifier name then throw "invalid function name"
  let params ← (← (← field j "params").getArr?).toList.mapM ty
  let result ← ty (← field j "result")
  return (name, params, result)

inductive Input where
  | expression (e : Expr)
  | program (fs : Functions) (entry : Nat)

def document (j : Json) : Decode Input := do
  let revision ← (← field j "semantic_revision").getStr?
  if revision != "m1-2026-11-16" then throw "unknown semantic revision"
  match ← (← field j "schema").getStr? with
  | "apl-expr-v0" =>
    fields j ["schema", "semantic_revision", "expression"]
    let (t, expected) ← term #[] 128 [] (← field j "expression")
    let e ← needSome (toExpr t)
    if APL.infer [] e ≠ some expected then throw "expression checker disagreement"
    return .expression e
  | "apl-core-v0" =>
    fields j ["schema", "semantic_revision", "functions", "entry"]
    let functions ← (← field j "functions").getArr?
    let named ← functions.toList.zipIdx.mapM fun (j, i) => signature i j
    let names := named.map Prod.fst
    if names.eraseDups.length != names.length then throw "duplicate function name"
    let sigs := (named.map Prod.snd).toArray
    let fs ← functions.toList.zipIdx.mapM fun (j, i) => do
      let (name, params, result) ← signature i j
      let (body, actual) ← term sigs 128 params.reverse (← field j "body")
      if actual ≠ result then throw "function result mismatch"
      if Program.infer sigs params.reverse body ≠ some result then throw "program checker disagreement"
      pure ({ name, params, result, body } : Function)
    let entry ← nat (← field j "entry")
    let main ← needSome fs[entry]?
    if main.params ≠ [] ∨ main.result ≠ .i64 then throw "invalid entry signature"
    return .program fs.toArray entry
  | _ => throw "unknown schema"

def decode (s : String) : Decode Input := do
  if s.utf8ByteSize > 1048576 then throw "input file size limit"
  lexicalCheck s.toList
  document (← Json.parse s)

def decodeError (message : String) : Program.Error :=
  if ["JSON nesting limit", "expression depth limit", "input file size limit"].contains message then
    .resourceLimit
  else .invalid

def outcome (r : Except Program.Error Val) : Json :=
  match r with
  | .ok (.int n) => Json.mkObj [("outcome", .str "value"), ("type", .str "i64"), ("value", .str (toString n.val))]
  | .ok (.bool b) => Json.mkObj [("outcome", .str "value"), ("type", .str "bool"), ("value", .bool b)]
  | .ok .unit => Json.mkObj [("outcome", .str "value"), ("type", .str "unit"), ("value", .null)]
  | .error (.trap t) => Json.mkObj [("outcome", .str "trap"), ("trap", .str
      (match t with | .arithmeticOverflow => "arithmetic_overflow" | .divisionByZero => "division_by_zero"))]
  | .error .resourceLimit => Json.mkObj [("outcome", .str "resource_limit")]
  | .error .invalid => Json.mkObj [("outcome", .str "invalid_ir")]

def execute (input : Input) (fuel : Nat) : Except Program.Error Val :=
  match input with
  | .expression e => match run fuel (.eval e [] []) with
    | some (.ret v []) => .ok v
    | some (.trap t) => .error (.trap t)
    | none => .error .resourceLimit
    | _ => .error .invalid
  | .program fs entry => match fs[entry]? with
    | some main => (Program.eval fs 256 [] main.body fuel).map Prod.fst
    | none => .error .invalid

end APL.Wire
