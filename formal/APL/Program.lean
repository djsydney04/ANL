import APL.Semantics

namespace APL.Program

inductive Term where
  | lit (v : Val)
  | local (index : Nat)
  | letE (value body : Term)
  | ifE (condition yes no : Term)
  | unary (op : UOp) (operand : Term)
  | binary (op : BOp) (left right : Term)
  | call (function : Nat) (arguments : List Term)
  deriving Repr

structure Function where
  name : String
  params : List Ty
  result : Ty
  body : Term
  deriving Repr
abbrev Functions := Array Function
abbrev Signature := List Ty × Ty
abbrev Signatures := Array Signature

partial def infer (fs : Signatures) (Γ : Ctx) : Term → Option Ty
  | .lit v => some v.type
  | .local i => Γ[i]?
  | .letE a b => do let u ← infer fs Γ a; infer fs (u :: Γ) b
  | .ifE c a b => do
      let ct ← infer fs Γ c
      let ta ← infer fs Γ a
      let tb ← infer fs Γ b
      if ct = .bool ∧ ta = tb then some ta else none
  | .unary op a => do
      let t ← infer fs Γ a
      if t = op.input then some op.output else none
  | .binary op a b => do
      let u ← infer fs Γ a
      let v ← infer fs Γ b
      binaryType op u v
  | .call f args => do
      let (params, result) ← fs[f]?
      let actual ← args.mapM (infer fs Γ)
      if actual = params then some result else none

partial def toExpr : Term → Option Expr
  | .lit v => some (.lit v)
  | .local i => some (.local i)
  | .letE a b => return .letE (← toExpr a) (← toExpr b)
  | .ifE c a b => return .ifE (← toExpr c) (← toExpr a) (← toExpr b)
  | .unary op a => return .unary op (← toExpr a)
  | .binary op a b => return .binary op (← toExpr a) (← toExpr b)
  | .call _ _ => none

inductive Error where
  | trap (kind : Trap)
  | resourceLimit
  | invalid
  deriving Repr

abbrev EvalM := StateT Nat (Except Error)

def takeFuel : EvalM Unit := do
  let fuel ← get
  if fuel = 0 then throw .resourceLimit
  set (fuel - 1)

def liftResult : Result → EvalM Val
  | .value v => pure v
  | .trap t => throw (.trap t)
  | .invalid => throw .invalid

def eval (fs : Functions) : Nat → Env → Term → EvalM Val
  | 0, _, _ => throw .resourceLimit
  | depth + 1, env, e => do
    takeFuel
    match e with
    | .lit v => return v
    | .local i => match env[i]? with | some v => pure v | none => throw .invalid
    | .letE a b =>
        let v ← eval fs depth env a
        eval fs depth (v :: env) b
    | .ifE c a b =>
        match ← eval fs depth env c with
        | .bool test => eval fs depth env (if test then a else b)
        | _ => throw .invalid
    | .unary op a => liftResult (unary op (← eval fs depth env a))
    | .binary op a b =>
        let va ← eval fs depth env a
        if shortCircuit op va then return va
        liftResult (binary op va (← eval fs depth env b))
    | .call f args =>
        let values ← args.mapM (eval fs depth env)
        match fs[f]? with
        | some fn => eval fs depth values.reverse fn.body
        | none => throw .invalid

end APL.Program
