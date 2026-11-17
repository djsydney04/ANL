import APL.Program

namespace APL.Program

inductive Frame where
  | letF (env : Env) (body : Term)
  | ifF (env : Env) (yes no : Term)
  | unary (op : UOp)
  | left (op : BOp) (env : Env) (right : Term)
  | right (op : BOp) (left : Val)
  | arguments (function : Nat) (caller : Env) (remaining : List Term) (reversed : List Val)

inductive State where
  | eval (term : Term) (env : Env) (kont : List Frame)
  | ret (value : Val) (kont : List Frame)
  | invoke (function : Nat) (reversed : List Val) (kont : List Frame)
  | trap (kind : Trap)
  | invalid

def resume (r : Result) (k : List Frame) : State :=
  match r with
  | .value v => .ret v k
  | .trap kind => .trap kind
  | .invalid => .invalid

inductive Step (fs : Functions) : State → State → Prop where
  | lit : Step fs (.eval (.lit v) env k) (.ret v k)
  | localFound : env[i]? = some v → Step fs (.eval (.local i) env k) (.ret v k)
  | localMissing : env[i]? = none → Step fs (.eval (.local i) env k) .invalid
  | letEval : Step fs (.eval (.letE a b) env k) (.eval a env (.letF env b :: k))
  | ifEval : Step fs (.eval (.ifE c a b) env k) (.eval c env (.ifF env a b :: k))
  | unaryEval : Step fs (.eval (.unary op a) env k) (.eval a env (.unary op :: k))
  | binaryEval : Step fs (.eval (.binary op a b) env k) (.eval a env (.left op env b :: k))
  | letReturn : Step fs (.ret v (.letF env b :: k)) (.eval b (v :: env) k)
  | ifTrue : Step fs (.ret (.bool true) (.ifF env a b :: k)) (.eval a env k)
  | ifFalse : Step fs (.ret (.bool false) (.ifF env a b :: k)) (.eval b env k)
  | ifInt : Step fs (.ret (.int n) (.ifF env a b :: k)) .invalid
  | ifUnit : Step fs (.ret .unit (.ifF env a b :: k)) .invalid
  | unaryReturn : Step fs (.ret v (.unary op :: k)) (resume (unary op v) k)
  | short : shortCircuit op v = true → Step fs (.ret v (.left op env b :: k)) (.ret v k)
  | rightEval : shortCircuit op v = false →
      Step fs (.ret v (.left op env b :: k)) (.eval b env (.right op v :: k))
  | binaryReturn : Step fs (.ret v (.right op a :: k)) (resume (binary op a v) k)
  | callEmpty : Step fs (.eval (.call f []) env k) (.invoke f [] k)
  | callFirst : Step fs (.eval (.call f (a :: args)) env k)
      (.eval a env (.arguments f env args [] :: k))
  | argumentNext : Step fs (.ret v (.arguments f env (a :: args) values :: k))
      (.eval a env (.arguments f env args (v :: values) :: k))
  | argumentsDone : Step fs (.ret v (.arguments f env [] values :: k)) (.invoke f (v :: values) k)
  | invoke : fs[f]? = some fn → Step fs (.invoke f values k) (.eval fn.body values k)
  | invalidFunction : fs[f]? = none → Step fs (.invoke f values k) .invalid

inductive Terminal : State → Prop where
  | value : Terminal (.ret v [])
  | trap : Terminal (.trap kind)

inductive Steps (fs : Functions) : State → State → Prop where
  | refl : Steps fs s s
  | head : Step fs s s' → Steps fs s' last → Steps fs s last

end APL.Program
