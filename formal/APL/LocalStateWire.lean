import APL.LocalState
import APL.Wire

namespace APL.LocalStateWire
open Lean
open LocalState
open Wire (Decode fields field nat ty uop bop integer needSome signature lexicalCheck)

/-- Reconstruct permissions and types from syntax; serialized type labels are checked. -/
def term (fs : Signatures) : Nat → LocalState.Ctx → Json → Decode (LocalState.Term × Ty)
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
        let (t, _) ← needSome Γ[i]?
        pure (.local i, t)
      | "let" | "let_mut" => do
        fields j ["tag", "ty", "value", "body"]
        let (a, ta) ← term fs depth Γ (← field j "value")
        let mutable := tag == "let_mut"
        let (b, tb) ← term fs depth ((ta, mutable) :: Γ) (← field j "body")
        pure ((if mutable then .letMut a b else .letE a b), tb)
      | "assign" => do
        fields j ["tag", "ty", "index", "value"]
        let i ← nat (← field j "index")
        let (target, mutable) ← needSome Γ[i]?
        let (a, actual) ← term fs depth Γ (← field j "value")
        if !mutable || actual != target then throw "invalid assignment target or type"
        pure (.assign i a, .unit)
      | "while" => do
        fields j ["tag", "ty", "condition", "body"]
        let (c, tc) ← term fs depth Γ (← field j "condition")
        let (b, tb) ← term fs depth Γ (← field j "body")
        if tc ≠ .bool ∨ tb ≠ .unit then throw "invalid loop types"
        pure (.whileE c b, .unit)
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

inductive Input where
  | expression (e : LocalState.Term)
  | program (fs : Functions) (entry : Nat)

def document (j : Json) : Decode Input := do
  let revision ← (← field j "semantic_revision").getStr?
  if revision != "local-state-2026-11-17" then throw "unknown semantic revision"
  match ← (← field j "schema").getStr? with
  | "apl-expr-v1" =>
    fields j ["schema", "semantic_revision", "expression"]
    -- An empty signature table rejects every call, including in dead branches.
    let (e, expected) ← term #[] 128 [] (← field j "expression")
    if LocalState.infer #[] [] e ≠ some expected then throw "expression checker disagreement"
    return .expression e
  | "apl-core-v1" =>
    fields j ["schema", "semantic_revision", "functions", "entry"]
    let functions ← (← field j "functions").getArr?
    let named ← functions.toList.zipIdx.mapM fun (j, i) => signature i j
    let names := named.map Prod.fst
    if names.eraseDups.length != names.length then throw "duplicate function name"
    let sigs := (named.map Prod.snd).toArray
    let fs ← functions.toList.zipIdx.mapM fun (j, i) => do
      let (name, params, result) ← signature i j
      let context := immutable params.reverse
      let (body, actual) ← term sigs 128 context (← field j "body")
      if actual ≠ result then throw "function result mismatch"
      if LocalState.infer sigs context body ≠ some result then throw "program checker disagreement"
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

/-- Fuel counts local-state machine transitions, independently of Rust expression fuel. -/
def execute (input : Input) (fuel : Nat) : Except Program.Error Val :=
  let (fs, initial) := match input with
    | .expression e => (#[], LocalState.State.eval e [] [])
    | .program fs entry => (fs, LocalState.State.invoke entry [] [] [])
  match LocalState.run fs fuel initial with
  | some (.ret v _ []) => .ok v
  | some (.trap kind) => .error (.trap kind)
  | none => .error .resourceLimit
  | _ => .error .invalid

end APL.LocalStateWire
