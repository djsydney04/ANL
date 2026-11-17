import ANL.MemoryTyping
import ANL.MemoryHeap

namespace ANL.Memory

abbrev Env := APL.FlatProducts.Env

structure Binding where
  mode : Mode
  ref : Ref
  length : Nat
  deriving DecidableEq, Repr

abbrev Resources := List Binding

structure Loan where
  source : Binding
  mode : ViewMode
  deriving DecidableEq, Repr

def Loan.binding (loan : Loan) : Binding := { loan.source with mode := loan.mode.mode }
def loanResources : Option Loan → Resources
  | none => []
  | some loan => [loan.binding]

def Loan.Valid (loan : Loan) (resources : Resources) : Prop :=
  loan.source ∈ resources ∧ loan.source.mode.CanLend loan.mode

def LoanOption.Valid (loan : Option Loan) (resources : Resources) : Prop :=
  match loan with | none => True | some loan => loan.Valid resources

def loanMode : Option Loan → Option ViewMode := Option.map Loan.mode

structure Activation where
  function : Nat
  env : Env
  resources : Resources
  deriving Repr

inductive MemoryTrap where
  | scalar (kind : APL.Trap)
  | invalidLength
  | indexOutOfBounds
  deriving DecidableEq, Repr

inductive Frame where
  | bind (mutable : Bool) (body : Term)
  | scope
  | assign (index : Nat)
  | ifF (yes no : Term)
  | unary (op : APL.UOp)
  | left (op : APL.BOp) (right : Term)
  | right (op : APL.BOp) (left : Val)
  | arguments (function : Nat) (loan : Option Loan) (remaining : List Term) (reversed : List Val)
  | callReturn (caller : Activation) (loan : Option Loan)
  | condition (condition body : Term)
  | body (condition body : Term)
  | fields (remaining : List Term) (reversed : List APL.Val)
  | project (index : Nat)
  | heapLength (site : Site) (initial success failure : Term)
  | heapInitial (site : Site) (length : Nat) (success failure : Term)
  | owner (binding : Binding) (site : Site)
  | readIndex (binding : Binding)
  | writeIndex (binding : Binding) (value : Term)
  | writeValue (binding : Binding) (index : Nat)
  deriving Repr

/-- Administrative controls expose the evaluation and preflight boundaries. -/
inductive Control where
  | eval (term : Term)
  | ret (value : Val)
  | lengthReady (site : Site) (value : Val) (initial success failure : Term)
  | allocate (site : Site) (length : Nat) (initial : APL.I64) (success failure : Term)
  | readCheck (binding : Binding) (index : Val)
  | readCell (binding : Binding) (index : Nat)
  | writeCheck (binding : Binding) (index : Val) (value : Term)
  | store (binding : Binding) (index : Nat) (value : APL.I64)
  | invoke (function : Nat) (loan : Option Loan) (reversed : List Val)
  | grant (function : Nat) (loan : Option Loan) (reversed : List Val)
  | close (binding : Binding) (site : Site) (value : Val)
  | revoke (value : Val)
  | restore (value : Val)
  | trap (kind : MemoryTrap)
  | invalid
  deriving Repr

structure State where
  control : Control
  current : Activation
  kont : List Frame
  world : World
  deriving Repr

/-- At restore the callee descriptors remain only as passive metadata. -/
def State.accessible (s : State) : Resources :=
  match s.control with | .restore _ => [] | _ => s.current.resources

def resume (result : APL.FlatProducts.Result) (a : Activation) (k : List Frame) (w : World) : State :=
  match result with
  | .value value => ⟨.ret value, a, k, w⟩
  | .trap kind => ⟨.trap (.scalar kind), a, k, w⟩
  | .invalid => ⟨.invalid, a, k, w⟩

def beginArguments (function : Nat) (loan : Option Loan) (args : List Term)
    (reversed : List Val) (a : Activation) (k : List Frame) (w : World) : State :=
  match args with
  | [] => ⟨.invoke function loan reversed, a, k, w⟩
  | arg :: rest => ⟨.eval arg, a, .arguments function loan rest reversed :: k, w⟩

def initial (p : Program) : State :=
  ⟨.invoke p.entry none [], ⟨p.entry, [], []⟩, [], .initial⟩

inductive Step (p : Program) (responses : Responses) : State → State → Prop where
  | lit : Step p responses ⟨.eval (.lit t v), a, k, w⟩ ⟨.ret (.scalar v), a, k, w⟩
  | localFound : a.env[i]? = some v →
      Step p responses ⟨.eval (.local t i), a, k, w⟩ ⟨.ret v, a, k, w⟩
  | localMissing : a.env[i]? = none →
      Step p responses ⟨.eval (.local t i), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | letEval : Step p responses ⟨.eval (.letE t e b), a, k, w⟩ ⟨.eval e, a, .bind false b :: k, w⟩
  | letMutEval : Step p responses ⟨.eval (.letMut t e b), a, k, w⟩ ⟨.eval e, a, .bind true b :: k, w⟩
  | assignEval : Step p responses ⟨.eval (.assign t i e), a, k, w⟩ ⟨.eval e, a, .assign i :: k, w⟩
  | whileEval : Step p responses ⟨.eval (.whileE t c b), a, k, w⟩ ⟨.eval c, a, .condition c b :: k, w⟩
  | ifEval : Step p responses ⟨.eval (.ifE t c y n), a, k, w⟩ ⟨.eval c, a, .ifF y n :: k, w⟩
  | unaryEval : Step p responses ⟨.eval (.unary t op e), a, k, w⟩ ⟨.eval e, a, .unary op :: k, w⟩
  | binaryEval : Step p responses ⟨.eval (.binary t op e b), a, k, w⟩ ⟨.eval e, a, .left op b :: k, w⟩
  | call : Step p responses ⟨.eval (.call t f args), a, k, w⟩ (beginArguments f none args [] a k w)
  | tupleEmpty : Step p responses ⟨.eval (.tuple t []), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | tupleFirst : Step p responses ⟨.eval (.tuple t (e :: rest)), a, k, w⟩
      ⟨.eval e, a, .fields rest [] :: k, w⟩
  | projectEval : Step p responses ⟨.eval (.project t e i), a, k, w⟩ ⟨.eval e, a, .project i :: k, w⟩
  | heapEval : Step p responses ⟨.eval (.heap t h len init yes no), a, k, w⟩
      ⟨.eval len, a, .heapLength ⟨a.function, h⟩ init yes no :: k, w⟩
  | lengthFound : a.resources[i]? = some binding →
      Step p responses ⟨.eval (.bufferLength t i), a, k, w⟩
        (resume (APL.FlatProducts.embedResult (APL.checked (binding.length : Int))) a k w)
  | lengthMissing : a.resources[i]? = none →
      Step p responses ⟨.eval (.bufferLength t i), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | readEval : a.resources[i]? = some binding →
      Step p responses ⟨.eval (.bufferRead t i index), a, k, w⟩
        ⟨.eval index, a, .readIndex binding :: k, w⟩
  | readMissing : a.resources[i]? = none →
      Step p responses ⟨.eval (.bufferRead t i index), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | writeEval : a.resources[i]? = some binding → binding.mode.CanWrite →
      Step p responses ⟨.eval (.bufferWrite t i index value), a, k, w⟩
        ⟨.eval index, a, .writeIndex binding value :: k, w⟩
  | writeMissing : a.resources[i]? = none →
      Step p responses ⟨.eval (.bufferWrite t i index value), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | writeDenied : a.resources[i]? = some binding → ¬ binding.mode.CanWrite →
      Step p responses ⟨.eval (.bufferWrite t i index value), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | callView : a.resources[i]? = some binding → binding.mode.CanLend mode →
      Step p responses ⟨.eval (.callView t f i mode args), a, k, w⟩
        (beginArguments f (some ⟨binding, mode⟩) args [] a k w)
  | viewMissing : a.resources[i]? = none →
      Step p responses ⟨.eval (.callView t f i mode args), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | viewDenied : a.resources[i]? = some binding → ¬ binding.mode.CanLend mode →
      Step p responses ⟨.eval (.callView t f i mode args), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | bindReturn : Step p responses ⟨.ret v, a, .bind permission b :: k, w⟩
      ⟨.eval b, {a with env := v :: a.env}, .scope :: k, w⟩
  | scopeReturn : a.env = cell :: rest → Step p responses ⟨.ret v, a, .scope :: k, w⟩
      ⟨.ret v, {a with env := rest}, k, w⟩
  | scopeMissing : a.env = [] → Step p responses ⟨.ret v, a, .scope :: k, w⟩ ⟨.invalid, a, .scope :: k, w⟩
  | assignReturn : APL.FlatProducts.update a.env i v = some env →
      Step p responses ⟨.ret v, a, .assign i :: k, w⟩ ⟨.ret (.scalar .unit), {a with env}, k, w⟩
  | assignMissing : APL.FlatProducts.update a.env i v = none →
      Step p responses ⟨.ret v, a, .assign i :: k, w⟩ ⟨.invalid, a, .assign i :: k, w⟩
  | ifTrue : Step p responses ⟨.ret (.scalar (.bool true)), a, .ifF y n :: k, w⟩ ⟨.eval y, a, k, w⟩
  | ifFalse : Step p responses ⟨.ret (.scalar (.bool false)), a, .ifF y n :: k, w⟩ ⟨.eval n, a, k, w⟩
  | ifWrong : v.type ≠ .scalar .bool →
      Step p responses ⟨.ret v, a, .ifF y n :: k, w⟩ ⟨.invalid, a, .ifF y n :: k, w⟩
  | unaryReturn : Step p responses ⟨.ret v, a, .unary op :: k, w⟩
      (resume (APL.FlatProducts.unary op v) a k w)
  | short : APL.FlatProducts.shortCircuit op v = true →
      Step p responses ⟨.ret v, a, .left op e :: k, w⟩ ⟨.ret v, a, k, w⟩
  | rightEval : APL.FlatProducts.shortCircuit op v = false →
      Step p responses ⟨.ret v, a, .left op e :: k, w⟩ ⟨.eval e, a, .right op v :: k, w⟩
  | binaryReturn : Step p responses ⟨.ret v, a, .right op left :: k, w⟩
      (resume (APL.FlatProducts.binary op left v) a k w)
  | argumentReturn : Step p responses ⟨.ret v, a, .arguments f loan rest values :: k, w⟩
      (beginArguments f loan rest (v :: values) a k w)
  | callResult : Step p responses ⟨.ret v, a, .callReturn caller loan :: k, w⟩
      ⟨.revoke v, a, .callReturn caller loan :: k, w⟩
  | whileTrue : Step p responses ⟨.ret (.scalar (.bool true)), a, .condition c b :: k, w⟩
      ⟨.eval b, a, .body c b :: k, w⟩
  | whileFalse : Step p responses ⟨.ret (.scalar (.bool false)), a, .condition c b :: k, w⟩
      ⟨.ret (.scalar .unit), a, k, w⟩
  | whileWrong : v.type ≠ .scalar .bool →
      Step p responses ⟨.ret v, a, .condition c b :: k, w⟩ ⟨.invalid, a, .condition c b :: k, w⟩
  | whileAgain : Step p responses ⟨.ret (.scalar .unit), a, .body c b :: k, w⟩
      ⟨.eval c, a, .condition c b :: k, w⟩
  | bodyWrong : v.type ≠ .scalar .unit →
      Step p responses ⟨.ret v, a, .body c b :: k, w⟩ ⟨.invalid, a, .body c b :: k, w⟩
  | fieldNext : Step p responses ⟨.ret (.scalar v), a, .fields (e :: rest) values :: k, w⟩
      ⟨.eval e, a, .fields rest (v :: values) :: k, w⟩
  | fieldsDone : Step p responses ⟨.ret (.scalar v), a, .fields [] values :: k, w⟩
      (resume (APL.FlatProducts.construct (v :: values).reverse) a k w)
  | fieldTuple : Step p responses ⟨.ret (.tuple values), a, .fields rest prior :: k, w⟩
      ⟨.invalid, a, .fields rest prior :: k, w⟩
  | projectReturn : Step p responses ⟨.ret v, a, .project i :: k, w⟩
      (resume (APL.FlatProducts.project v i) a k w)
  | heapLengthReturn : Step p responses ⟨.ret v, a, .heapLength site init yes no :: k, w⟩
      ⟨.lengthReady site v init yes no, a, k, w⟩
  | heapInitialReturn : Step p responses ⟨.ret (.scalar (.int v)), a, .heapInitial site n yes no :: k, w⟩
      ⟨.allocate site n v yes no, a, k, w⟩
  | heapInitialWrong : v.type ≠ .scalar .i64 →
      Step p responses ⟨.ret v, a, .heapInitial site n yes no :: k, w⟩
        ⟨.invalid, a, .heapInitial site n yes no :: k, w⟩
  | ownerReturn : Step p responses ⟨.ret v, a, .owner binding site :: k, w⟩
      ⟨.close binding site v, a, .owner binding site :: k, w⟩
  | readIndexReturn : Step p responses ⟨.ret v, a, .readIndex binding :: k, w⟩
      ⟨.readCheck binding v, a, k, w⟩
  | writeIndexReturn : Step p responses ⟨.ret v, a, .writeIndex binding value :: k, w⟩
      ⟨.writeCheck binding v value, a, k, w⟩
  | writeValueReturn : Step p responses ⟨.ret (.scalar (.int v)), a, .writeValue binding i :: k, w⟩
      ⟨.store binding i v, a, k, w⟩
  | writeValueWrong : v.type ≠ .scalar .i64 →
      Step p responses ⟨.ret v, a, .writeValue binding i :: k, w⟩
        ⟨.invalid, a, .writeValue binding i :: k, w⟩
  | negativeLength : n.val < 0 →
      Step p responses ⟨.lengthReady site (.scalar (.int n)) init yes no, a, k, w⟩
        ⟨.trap .invalidLength, a, k, w⟩
  | nonnegativeLength : ¬ n.val < 0 →
      Step p responses ⟨.lengthReady site (.scalar (.int n)) init yes no, a, k, w⟩
        ⟨.eval init, a, .heapInitial site n.val.toNat yes no :: k, w⟩
  | lengthWrong : v.type ≠ .scalar .i64 →
      Step p responses ⟨.lengthReady site v init yes no, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | allocated : allocate p.profile responses w site n init = (.allocated ref, next) →
      Step p responses ⟨.allocate site n init yes no, a, k, w⟩
        ⟨.eval yes, {a with resources := ⟨.owner, ref, n⟩ :: a.resources},
          .owner ⟨.owner, ref, n⟩ site :: k, next⟩
  | allocationRefused : allocate p.profile responses w site n init = (.refused, next) →
      Step p responses ⟨.allocate site n init yes no, a, k, w⟩ ⟨.eval no, a, k, next⟩
  | allocationRejected : allocate p.profile responses w site n init = (.targetRejected, next) →
      Step p responses ⟨.allocate site n init yes no, a, k, w⟩ ⟨.eval no, a, k, next⟩
  | readChecked : checkedIndex binding.length index.val = some i →
      Step p responses ⟨.readCheck binding (.scalar (.int index)), a, k, w⟩ ⟨.readCell binding i, a, k, w⟩
  | readBounds : checkedIndex binding.length index.val = none →
      Step p responses ⟨.readCheck binding (.scalar (.int index)), a, k, w⟩ ⟨.trap .indexOutOfBounds, a, k, w⟩
  | readWrong : v.type ≠ .scalar .i64 →
      Step p responses ⟨.readCheck binding v, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | readValue : w.read binding.ref i = some value →
      Step p responses ⟨.readCell binding i, a, k, w⟩ ⟨.ret (.scalar (.int value)), a, k, w⟩
  | readUnavailable : w.read binding.ref i = none →
      Step p responses ⟨.readCell binding i, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | writeChecked : checkedIndex binding.length index.val = some i →
      Step p responses ⟨.writeCheck binding (.scalar (.int index)) value, a, k, w⟩
        ⟨.eval value, a, .writeValue binding i :: k, w⟩
  | writeBounds : checkedIndex binding.length index.val = none →
      Step p responses ⟨.writeCheck binding (.scalar (.int index)) value, a, k, w⟩
        ⟨.trap .indexOutOfBounds, a, k, w⟩
  | writeWrong : v.type ≠ .scalar .i64 →
      Step p responses ⟨.writeCheck binding v value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | stored : w.write binding.ref i value = some next →
      Step p responses ⟨.store binding i value, a, k, w⟩ ⟨.ret (.scalar .unit), a, k, next⟩
  | storeUnavailable : w.write binding.ref i value = none →
      Step p responses ⟨.store binding i value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | invoke : p.functions[f]? = some fn → fn.view = loanMode loan →
      Step p responses ⟨.invoke f loan values, a, k, w⟩ ⟨.grant f loan values, a, k, w⟩
  | invokeMissing : p.functions[f]? = none →
      Step p responses ⟨.invoke f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | invokeMode : p.functions[f]? = some fn → fn.view ≠ loanMode loan →
      Step p responses ⟨.invoke f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | grant : p.functions[f]? = some fn →
      Step p responses ⟨.grant f loan values, a, k, w⟩
        ⟨.eval fn.body, ⟨f, values, loanResources loan⟩, .callReturn a loan :: k, w⟩
  | grantMissing : p.functions[f]? = none →
      Step p responses ⟨.grant f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | closed : w.close binding.ref site = some next →
      Step p responses ⟨.close binding site value, a, .owner binding site :: k, w⟩
        ⟨.ret value, {a with resources := a.resources.tail}, k, next⟩
  | closeUnavailable : w.close binding.ref site = none →
      Step p responses ⟨.close binding site value, a, .owner binding site :: k, w⟩
        ⟨.invalid, a, .owner binding site :: k, w⟩
  | closeWrong : (∀ k, kont ≠ .owner binding site :: k) →
      Step p responses ⟨.close binding site value, a, kont, w⟩ ⟨.invalid, a, kont, w⟩
  | revoke : Step p responses ⟨.revoke value, a, .callReturn caller loan :: k, w⟩
      ⟨.restore value, a, .callReturn caller loan :: k, w⟩
  | revokeWrong : (∀ caller loan k, kont ≠ .callReturn caller loan :: k) →
      Step p responses ⟨.revoke value, a, kont, w⟩ ⟨.invalid, a, kont, w⟩
  | restore : Step p responses ⟨.restore value, a, .callReturn caller loan :: k, w⟩
      ⟨.ret value, caller, k, w⟩
  | restoreWrong : (∀ caller loan k, kont ≠ .callReturn caller loan :: k) →
      Step p responses ⟨.restore value, a, kont, w⟩ ⟨.invalid, a, kont, w⟩

inductive Terminal : State → Prop where
  | value : Terminal ⟨.ret value, a, [], w⟩
  | trap : Terminal ⟨.trap kind, a, k, w⟩

inductive Steps (p : Program) (responses : Responses) : State → State → Prop where
  | refl : Steps p responses s s
  | head : Step p responses s middle → Steps p responses middle last → Steps p responses s last

end ANL.Memory
