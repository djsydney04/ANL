import APL.ProgramTyping

namespace APL.LocalState

abbrev Binding := Ty × Bool
abbrev Ctx := List Binding
abbrev Signatures := Program.Signatures

def immutable (ts : List Ty) : Ctx := ts.map (fun t => (t, false))

inductive Term where
  | lit (v : Val)
  | local (index : Nat)
  | letE (value body : Term)
  | letMut (value body : Term)
  | assign (index : Nat) (value : Term)
  | whileE (condition body : Term)
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

def infer (fs : Signatures) (Γ : Ctx) : Term → Option Ty
  | .lit v => some v.type
  | .local i => (Γ[i]?).map Prod.fst
  | .letE a b => do let u ← infer fs Γ a; infer fs ((u, false) :: Γ) b
  | .letMut a b => do let u ← infer fs Γ a; infer fs ((u, true) :: Γ) b
  | .assign i a => do
      let (t, mutable) ← Γ[i]?
      let u ← infer fs Γ a
      if mutable = true ∧ u = t then some .unit else none
  | .whileE c b => do
      let ct ← infer fs Γ c
      let bt ← infer fs Γ b
      if ct = .bool ∧ bt = .unit then some .unit else none
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

/-- Runtime cells carry values only. Permission is checked in the static context. -/
def update : Env → Nat → Val → Option Env
  | [], _, _ => none
  | _ :: vs, 0, v => some (v :: vs)
  | a :: vs, i + 1, v => (update vs i v).map (a :: ·)

inductive Frame where
  | bind (mutable : Bool) (body : Term)
  | scope
  | assign (index : Nat)
  | ifF (yes no : Term)
  | unary (op : UOp)
  | left (op : BOp) (right : Term)
  | right (op : BOp) (left : Val)
  | arguments (function : Nat) (remaining : List Term) (reversed : List Val)
  | callReturn (caller : Env)
  | condition (condition body : Term)
  | body (condition body : Term)

inductive State where
  | eval (term : Term) (env : Env) (kont : List Frame)
  | ret (value : Val) (env : Env) (kont : List Frame)
  | invoke (function : Nat) (reversed : List Val) (caller : Env) (kont : List Frame)
  | trap (kind : Trap)
  | invalid

def resume (r : Result) (env : Env) (k : List Frame) : State :=
  match r with
  | .value v => .ret v env k
  | .trap kind => .trap kind
  | .invalid => .invalid

inductive Step (fs : Functions) : State → State → Prop where
  | lit : Step fs (.eval (.lit v) env k) (.ret v env k)
  | localFound : env[i]? = some v → Step fs (.eval (.local i) env k) (.ret v env k)
  | localMissing : env[i]? = none → Step fs (.eval (.local i) env k) .invalid
  | letEval : Step fs (.eval (.letE a b) env k) (.eval a env (.bind false b :: k))
  | letMutEval : Step fs (.eval (.letMut a b) env k) (.eval a env (.bind true b :: k))
  | bindReturn : Step fs (.ret v env (.bind permission b :: k)) (.eval b (v :: env) (.scope :: k))
  | scopeReturn : Step fs (.ret v (a :: env) (.scope :: k)) (.ret v env k)
  | scopeMissing : Step fs (.ret v [] (.scope :: k)) .invalid
  | assignEval : Step fs (.eval (.assign i a) env k) (.eval a env (.assign i :: k))
  | assignReturn : update env i v = some env' →
      Step fs (.ret v env (.assign i :: k)) (.ret .unit env' k)
  | assignMissing : update env i v = none → Step fs (.ret v env (.assign i :: k)) .invalid
  | ifEval : Step fs (.eval (.ifE c a b) env k) (.eval c env (.ifF a b :: k))
  | ifTrue : Step fs (.ret (.bool true) env (.ifF a b :: k)) (.eval a env k)
  | ifFalse : Step fs (.ret (.bool false) env (.ifF a b :: k)) (.eval b env k)
  | ifInt : Step fs (.ret (.int n) env (.ifF a b :: k)) .invalid
  | ifUnit : Step fs (.ret .unit env (.ifF a b :: k)) .invalid
  | unaryEval : Step fs (.eval (.unary op a) env k) (.eval a env (.unary op :: k))
  | unaryReturn : Step fs (.ret v env (.unary op :: k)) (resume (unary op v) env k)
  | binaryEval : Step fs (.eval (.binary op a b) env k) (.eval a env (.left op b :: k))
  | short : shortCircuit op v = true → Step fs (.ret v env (.left op b :: k)) (.ret v env k)
  | rightEval : shortCircuit op v = false →
      Step fs (.ret v env (.left op b :: k)) (.eval b env (.right op v :: k))
  | binaryReturn : Step fs (.ret v env (.right op a :: k)) (resume (binary op a v) env k)
  | callEmpty : Step fs (.eval (.call f []) env k) (.invoke f [] env k)
  | callFirst : Step fs (.eval (.call f (a :: args)) env k)
      (.eval a env (.arguments f args [] :: k))
  | argumentNext : Step fs (.ret v env (.arguments f (a :: args) values :: k))
      (.eval a env (.arguments f args (v :: values) :: k))
  | argumentsDone : Step fs (.ret v env (.arguments f [] values :: k)) (.invoke f (v :: values) env k)
  | invoke : fs[f]? = some fn →
      Step fs (.invoke f values env k) (.eval fn.body values (.callReturn env :: k))
  | invalidFunction : fs[f]? = none → Step fs (.invoke f values env k) .invalid
  | callReturn : Step fs (.ret v callee (.callReturn caller :: k)) (.ret v caller k)
  | whileEval : Step fs (.eval (.whileE c b) env k) (.eval c env (.condition c b :: k))
  | whileTrue : Step fs (.ret (.bool true) env (.condition c b :: k)) (.eval b env (.body c b :: k))
  | whileFalse : Step fs (.ret (.bool false) env (.condition c b :: k)) (.ret .unit env k)
  | whileInt : Step fs (.ret (.int n) env (.condition c b :: k)) .invalid
  | whileUnit : Step fs (.ret .unit env (.condition c b :: k)) .invalid
  | whileAgain : Step fs (.ret .unit env (.body c b :: k)) (.eval c env (.condition c b :: k))
  | bodyInt : Step fs (.ret (.int n) env (.body c b :: k)) .invalid
  | bodyBool : Step fs (.ret (.bool v) env (.body c b :: k)) .invalid

inductive Terminal : State → Prop where
  | value : Terminal (.ret v env [])
  | trap : Terminal (.trap kind)

inductive Steps (fs : Functions) : State → State → Prop where
  | refl : Steps fs s s
  | head : Step fs s s' → Steps fs s' last → Steps fs s last

/-- One abstract-machine transition; the relation above is defined independently. -/
def step (fs : Functions) : State → Option State
  | .eval e env k => some (match e with
    | .lit v => .ret v env k
    | .local i => match env[i]? with | some v => .ret v env k | none => .invalid
    | .letE a b => .eval a env (.bind false b :: k)
    | .letMut a b => .eval a env (.bind true b :: k)
    | .assign i a => .eval a env (.assign i :: k)
    | .whileE c b => .eval c env (.condition c b :: k)
    | .ifE c a b => .eval c env (.ifF a b :: k)
    | .unary op a => .eval a env (.unary op :: k)
    | .binary op a b => .eval a env (.left op b :: k)
    | .call f [] => .invoke f [] env k
    | .call f (a :: args) => .eval a env (.arguments f args [] :: k))
  | .ret _ _ [] => none
  | .ret v env (f :: k) => some (match f with
    | .bind _ b => .eval b (v :: env) (.scope :: k)
    | .scope => match env with | _ :: rest => .ret v rest k | [] => .invalid
    | .assign i => match update env i v with | some env' => .ret .unit env' k | none => .invalid
    | .ifF a b => match v with | .bool test => .eval (if test then a else b) env k | _ => .invalid
    | .unary op => resume (unary op v) env k
    | .left op b => if shortCircuit op v then .ret v env k else .eval b env (.right op v :: k)
    | .right op a => resume (binary op a v) env k
    | .arguments f [] values => .invoke f (v :: values) env k
    | .arguments f (a :: args) values => .eval a env (.arguments f args (v :: values) :: k)
    | .callReturn caller => .ret v caller k
    | .condition c b => match v with
      | .bool true => .eval b env (.body c b :: k)
      | .bool false => .ret .unit env k
      | _ => .invalid
    | .body c b => match v with
      | .unit => .eval c env (.condition c b :: k)
      | _ => .invalid)
  | .invoke f values env k => some (match fs[f]? with
      | some fn => .eval fn.body values (.callReturn env :: k)
      | none => .invalid)
  | .trap _ | .invalid => none

/-- This budget counts machine transitions, not Rust expression entries. -/
def run (fs : Functions) : Nat → State → Option State
  | 0, s => if (step fs s).isNone then some s else none
  | n + 1, s => match step fs s with | none => some s | some s' => run fs n s'

end APL.LocalState
