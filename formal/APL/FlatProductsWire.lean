import APL.FlatProductsMachine
import APL.Wire

namespace APL.FlatProductsWire
open Lean
open FlatProducts
open Wire (Decode fields field nat uop bop integer needSome lexicalCheck identifier)

def ty (j : Json) : Decode FlatProducts.Ty := do
  match j with
  | .str _ => return .scalar (← Wire.ty j)
  | _ =>
    fields j ["tuple"]
    let raw ← (← field j "tuple").getArr?
    if raw.size == 0 || raw.size > 8 then throw "invalid tuple width"
    let scalars ← raw.toList.mapM Wire.ty
    return .tuple (← needSome (Flat.make scalars))

def signature (index : Nat) (j : Json) : Decode (String × (List FlatProducts.Ty × FlatProducts.Ty)) := do
  fields j ["id", "name", "params", "result", "body"]
  let id ← nat (← field j "id")
  if id ≠ index then throw "function ID differs from table index"
  let name ← (← field j "name").getStr?
  if !identifier name then throw "invalid function name"
  let params ← (← (← field j "params").getArr?).toList.mapM ty
  let result ← ty (← field j "result")
  return (name, params, result)

/-- Reconstruct permissions and types from syntax; serialized type labels are checked. -/
def term (fs : Signatures) : Nat → FlatProducts.Ctx → Json → Decode (FlatProducts.Term × FlatProducts.Ty)
  | 0, _, _ => throw "expression depth limit"
  | depth + 1, Γ, j => do
    let declared ← ty (← field j "ty")
    let tag ← (← field j "tag").getStr?
    let (e, actual) ← match tag with
      | "integer" => do
        fields j ["tag", "ty", "value"]
        let v ← integer (← field j "value")
        pure (.lit (.scalar v), .scalar .i64)
      | "boolean" => do
        fields j ["tag", "ty", "value"]
        pure (.lit (.scalar (.bool (← (← field j "value").getBool?))), .scalar .bool)
      | "unit" => do
        fields j ["tag", "ty"]
        pure (.lit (.scalar .unit), .scalar .unit)
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
        pure (.assign i a, .scalar .unit)
      | "while" => do
        fields j ["tag", "ty", "condition", "body"]
        let (c, tc) ← term fs depth Γ (← field j "condition")
        let (b, tb) ← term fs depth Γ (← field j "body")
        if tc ≠ .scalar .bool ∨ tb ≠ .scalar .unit then throw "invalid loop types"
        pure (.whileE c b, .scalar .unit)
      | "if" => do
        fields j ["tag", "ty", "condition", "then", "else"]
        let (c, tc) ← term fs depth Γ (← field j "condition")
        let (a, ta) ← term fs depth Γ (← field j "then")
        let (b, tb) ← term fs depth Γ (← field j "else")
        if tc ≠ .scalar .bool ∨ ta ≠ tb then throw "invalid conditional types"
        pure (.ifE c a b, ta)
      | "unary" => do
        fields j ["tag", "ty", "op", "operand"]
        let op ← uop (← field j "op")
        let (a, ta) ← term fs depth Γ (← field j "operand")
        if ta ≠ .scalar op.input then throw "invalid unary operand"
        pure (.unary op a, .scalar op.output)
      | "binary" => do
        fields j ["tag", "ty", "op", "left", "right"]
        let op ← bop (← field j "op")
        let (a, ta) ← term fs depth Γ (← field j "left")
        let (b, tb) ← term fs depth Γ (← field j "right")
        pure (.binary op a b, ← needSome (FlatProducts.binaryType op ta tb))
      | "call" => do
        fields j ["tag", "ty", "function", "arguments"]
        let f ← nat (← field j "function")
        let (params, result) ← needSome fs[f]?
        let args ← (← (← field j "arguments").getArr?).toList.mapM (term fs depth Γ)
        if args.map Prod.snd ≠ params then throw "invalid call arguments"
        pure (.call f (args.map Prod.fst), result)
      | "tuple" => do
        fields j ["tag", "ty", "fields"]
        let raw ← (← field j "fields").getArr?
        if raw.size == 0 || raw.size > 8 then throw "invalid tuple width"
        let items ← raw.toList.mapM (term fs depth Γ)
        let scalars ← items.mapM fun (_, t) => needSome t.asScalar
        let shape ← needSome (Flat.make scalars)
        pure (.tuple (items.map Prod.fst), .tuple shape)
      | "project" => do
        fields j ["tag", "ty", "value", "index"]
        let index ← nat (← field j "index")
        if index ≥ 8 then throw "invalid tuple projection index"
        let (base, actual) ← term fs depth Γ (← field j "value")
        let .tuple shape := actual | throw "scalar projection base"
        let result ← needSome shape.fields[index]?
        pure (.project base index, .scalar result)
      | _ => throw "unknown expression constructor"
    if actual ≠ declared then throw "incorrect serialized type"
    return (e, actual)

inductive Input where
  | expression (e : FlatProducts.Term)
  | program (fs : Functions) (entry : Nat)

def document (j : Json) : Decode Input := do
  let revision ← (← field j "semantic_revision").getStr?
  if revision != "flat-products-2026-11-17" then throw "unknown semantic revision"
  match ← (← field j "schema").getStr? with
  | "apl-expr-v2" =>
    fields j ["schema", "semantic_revision", "expression"]
    -- An empty signature table rejects every call, including in dead branches.
    let (e, expected) ← term #[] 128 [] (← field j "expression")
    if FlatProducts.infer #[] [] e ≠ some expected then throw "expression checker disagreement"
    return .expression e
  | "apl-core-v2" =>
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
      if FlatProducts.infer sigs context body ≠ some result then throw "program checker disagreement"
      pure ({ name, params, result, body } : Function)
    let entry ← nat (← field j "entry")
    let main ← needSome fs[entry]?
    if main.params ≠ [] ∨ main.result ≠ .scalar .i64 then throw "invalid entry signature"
    return .program fs.toArray entry
  | _ => throw "unknown schema"

def decode (s : String) : Decode Input := do
  if s.utf8ByteSize > 1048576 then throw "input file size limit"
  lexicalCheck s.toList
  document (← Json.parse s)

/-- Fuel counts local-state machine transitions, independently of Rust expression fuel. -/
def execute (input : Input) (fuel : Nat) : Except Program.Error FlatProducts.Val :=
  let (fs, initial) := match input with
    | .expression e => (#[], FlatProducts.State.eval e [] [])
    | .program fs entry => (fs, FlatProducts.State.invoke entry [] [] [])
  match FlatProducts.run fs fuel initial with
  | some (.ret v _ []) => .ok v
  | some (.trap kind) => .error (.trap kind)
  | none => .error .resourceLimit
  | _ => .error .invalid

def scalarTypeJson : APL.Ty → Json
  | .i64 => .str "i64"
  | .bool => .str "bool"
  | .unit => .str "unit"

def scalarValueJson : APL.Val → Json
  | .int n => .str (toString n.val)
  | .bool b => .bool b
  | .unit => .null

def outcome (r : Except Program.Error FlatProducts.Val) : Json :=
  match r with
  | .ok (.scalar v) => Wire.outcome (.ok v)
  | .ok (.tuple fields) => Json.mkObj [
      ("outcome", .str "value"),
      ("type", Json.mkObj [("tuple", .arr (fields.fields.map (scalarTypeJson ∘ APL.Val.type)).toArray)]),
      ("value", .arr (fields.fields.map scalarValueJson).toArray)]
  | .error err => Wire.outcome (.error err)

partial def hasProducts : FlatProducts.Term → Bool
  | .lit (.tuple _) | .tuple _ | .project _ _ => true
  | .lit (.scalar _) | .local _ => false
  | .letE a b | .letMut a b | .whileE a b | .binary _ a b => hasProducts a || hasProducts b
  | .assign _ a | .unary _ a => hasProducts a
  | .ifE c a b => hasProducts c || hasProducts a || hasProducts b
  | .call _ args => args.any hasProducts

partial def hasState : FlatProducts.Term → Bool
  | .letMut _ _ | .assign _ _ | .whileE _ _ => true
  | .lit _ | .local _ => false
  | .letE a b | .binary _ a b => hasState a || hasState b
  | .project a _ | .unary _ a => hasState a
  | .ifE c a b => hasState c || hasState a || hasState b
  | .tuple items | .call _ items => items.any hasState

def productType : FlatProducts.Ty → Bool
  | .scalar _ => false
  | .tuple _ => true

def semanticRevision (input : Input) : String :=
  let products := match input with
    | .expression e => hasProducts e
    | .program fs _ => fs.any fun fn =>
        fn.params.any productType || productType fn.result || hasProducts fn.body
  let state := match input with
    | .expression e => hasState e
    | .program fs _ => fs.any fun fn => hasState fn.body
  if products then "flat-products-2026-11-17"
  else if state then "local-state-2026-11-17"
  else "m1-2026-11-16"

end APL.FlatProductsWire
