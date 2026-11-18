import ANL.BootOriginFrames
import ANL.BootCarrier

namespace ANL.Boot.Origin
open ANL.Words

inductive Action where
  | keep
  | push (edge : Edge)
  | pop
  | within (edge : Edge)
  | select (edge : Edge)
  | enter (function : Nat)
  deriving DecidableEq, Repr

def applyAction : Action → Metadata → Option Metadata
  | .keep, m => some m
  | .push edge, m => some ⟨m.control.child edge, m.control :: m.frames⟩
  | .pop, ⟨_, parent :: rest⟩ => some ⟨parent, rest⟩
  | .within edge, ⟨_, parent :: rest⟩ => some ⟨parent.child edge, parent :: rest⟩
  | .select edge, ⟨_, parent :: rest⟩ => some ⟨parent.child edge, rest⟩
  | .enter function, m => some ⟨.root function, m.control :: m.frames⟩
  | _, _ => none

inductive Applies : Action → Metadata → Metadata → Prop where
  | keep : Applies .keep m m
  | push : Applies (.push edge) m ⟨m.control.child edge, m.control :: m.frames⟩
  | pop : Applies .pop ⟨current, parent :: rest⟩ ⟨parent, rest⟩
  | within : Applies (.within edge) ⟨current, parent :: rest⟩ ⟨parent.child edge, parent :: rest⟩
  | select : Applies (.select edge) ⟨current, parent :: rest⟩ ⟨parent.child edge, rest⟩
  | enter : Applies (.enter function) m ⟨.root function, m.control :: m.frames⟩

def action (s next : State) : Option Action :=
  match s.control with
  | .eval e => match e with
      | .lit .. | .word .. | .local .. => some .keep
      | .convert .. => some (.push .convertOperand)
      | .letE .. | .letMut .. => some (.push .letValue)
      | .assign .. => some (.push .assignValue)
      | .whileE .. => some (.push .whileCondition)
      | .ifE .. => some (.push .ifCondition)
      | .unary .. => some (.push .unaryOperand)
      | .binary .. => some (.push .binaryLeft)
      | .call _ _ [] | .tuple _ [] => some .keep
      | .call _ _ (_ :: _) => some (.push (.callArgument 0))
      | .tuple _ (_ :: _) => some (.push (.tupleField 0))
      | .project .. => some (.push .projectOperand)
      | _ => none
  | .ret v => match s.kont with
      | .bind .. :: _ => some (.within .letBody)
      | .scope :: _ | .assign .. :: _ =>
          match next.control with | .invalid => some .keep | _ => some .pop
      | .ifF .. :: _ => match v with
          | .scalar (.legacy (.bool true)) => some (.select .ifThen)
          | .scalar (.legacy (.bool false)) => some (.select .ifElse)
          | _ => some .keep
      | .convert .. :: _ | .unary .. :: _ | .right .. :: _ | .project .. :: _ => some .pop
      | .left op _ :: _ => if shortCircuit op v then some .pop else some (.within .binaryRight)
      | .arguments _ _ [] _ :: _ => some .pop
      | .arguments _ _ (_ :: _) values :: _ => some (.within (.callArgument (values.length + 1)))
      | .callReturn .. :: _ => some .keep
      | .condition .. :: _ => match v with
          | .scalar (.legacy (.bool true)) => some (.within .whileBody)
          | .scalar (.legacy (.bool false)) => some .pop
          | _ => some .keep
      | .body .. :: _ => match v with
          | .scalar (.legacy .unit) => some (.within .whileCondition)
          | _ => some .keep
      | .fields remaining values :: _ => match v, remaining with
          | .scalar _, [] => some .pop
          | .scalar _, _ :: _ => some (.within (.tupleField (values.length + 1)))
          | .tuple _, _ => some .keep
      | _ => none
  | .invoke .. | .revoke .. => some .keep
  | .grant f .. => some (.enter f)
  | .restore .. => some .pop
  | _ => none

/-- Independent structural movement rules. Ordinary Step separately constrains next. -/
inductive Chooses : Control → List Frame → Control → Action → Prop where
  | lit : Chooses (.eval (.lit t v)) k next .keep
  | word : Chooses (.eval (.word t w v)) k next .keep
  | local : Chooses (.eval (.local t i)) k next .keep
  | convertEval : Chooses (.eval (.convert t mode target e)) k next (.push .convertOperand)
  | letEval : Chooses (.eval (.letE t a b)) k next (.push .letValue)
  | mutEval : Chooses (.eval (.letMut t a b)) k next (.push .letValue)
  | assignEval : Chooses (.eval (.assign t i e)) k next (.push .assignValue)
  | whileEval : Chooses (.eval (.whileE t c b)) k next (.push .whileCondition)
  | ifEval : Chooses (.eval (.ifE t c y n)) k next (.push .ifCondition)
  | unaryEval : Chooses (.eval (.unary t op e)) k next (.push .unaryOperand)
  | binaryEval : Chooses (.eval (.binary t op a b)) k next (.push .binaryLeft)
  | callEmpty : Chooses (.eval (.call t f [])) k next .keep
  | callFirst : Chooses (.eval (.call t f (arg :: args))) k next (.push (.callArgument 0))
  | tupleEmpty : Chooses (.eval (.tuple t [])) k next .keep
  | tupleFirst : Chooses (.eval (.tuple t (arg :: args))) k next (.push (.tupleField 0))
  | projectEval : Chooses (.eval (.project t e i)) k next (.push .projectOperand)
  | bind : Chooses (.ret v) (.bind permission body :: k) next (.within .letBody)
  | scopeGood : next ≠ .invalid → Chooses (.ret v) (.scope :: k) next .pop
  | scopeBad : Chooses (.ret v) (.scope :: k) .invalid .keep
  | assignGood : next ≠ .invalid → Chooses (.ret v) (.assign i :: k) next .pop
  | assignBad : Chooses (.ret v) (.assign i :: k) .invalid .keep
  | ifTrue : Chooses (.ret (.scalar (.legacy (.bool true)))) (.ifF y n :: k) next (.select .ifThen)
  | ifFalse : Chooses (.ret (.scalar (.legacy (.bool false)))) (.ifF y n :: k) next (.select .ifElse)
  | ifWrong : v.type ≠ .scalar (.legacy .bool) → Chooses (.ret v) (.ifF y n :: k) next .keep
  | convertReturn : Chooses (.ret v) (.convert mode target :: k) next .pop
  | unaryReturn : Chooses (.ret v) (.unary op :: k) next .pop
  | right : Chooses (.ret v) (.right op left :: k) next .pop
  | projectReturn : Chooses (.ret v) (.project i :: k) next .pop
  | short : shortCircuit op v = true → Chooses (.ret v) (.left op e :: k) next .pop
  | rightEval : shortCircuit op v = false → Chooses (.ret v) (.left op e :: k) next (.within .binaryRight)
  | argumentsDone : Chooses (.ret v) (.arguments f loan [] values :: k) next .pop
  | argumentNext : Chooses (.ret v) (.arguments f loan (arg :: args) values :: k) next
      (.within (.callArgument (values.length + 1)))
  | callReturn : Chooses (.ret v) (.callReturn caller loan :: k) next .keep
  | whileTrue : Chooses (.ret (.scalar (.legacy (.bool true)))) (.condition c b :: k) next (.within .whileBody)
  | whileFalse : Chooses (.ret (.scalar (.legacy (.bool false)))) (.condition c b :: k) next .pop
  | whileWrong : v.type ≠ .scalar (.legacy .bool) → Chooses (.ret v) (.condition c b :: k) next .keep
  | whileAgain : Chooses (.ret (.scalar (.legacy .unit))) (.body c b :: k) next (.within .whileCondition)
  | bodyWrong : v.type ≠ .scalar (.legacy .unit) → Chooses (.ret v) (.body c b :: k) next .keep
  | fieldsDone : Chooses (.ret (.scalar v)) (.fields [] values :: k) next .pop
  | fieldNext : Chooses (.ret (.scalar v)) (.fields (arg :: args) values :: k) next
      (.within (.tupleField (values.length + 1)))
  | fieldTuple : Chooses (.ret (.tuple v)) (.fields remaining values :: k) next .keep
  | invoke : Chooses (.invoke f loan values) k next .keep
  | grant : Chooses (.grant f loan values) k next (.enter f)
  | revoke : Chooses (.revoke v) k next .keep
  | restore : Chooses (.restore v) k next .pop

/-- No future boot/hardware semantics are introduced; each edge erases to old Words.Step. -/
inductive Step (p : Program) (responses : ANL.Memory.Responses) :
    State → Metadata → State → Metadata → Prop where
  | ordinary : Admitted p s → ANL.Words.Step p.carrier responses s next →
      Chooses s.control s.kont next.control a → Applies a metadata result →
      Step p responses s metadata next result

def advance (s next : State) (metadata : Metadata) : Option Metadata := do
  let selected ← action s next
  applyAction selected metadata

def step (p : Program) (responses : ANL.Memory.Responses) (s : State)
    (metadata : Metadata) : Option (State × Metadata) := do
  if checkAdmitted p s then
    let next ← ANL.Words.step p.carrier responses s
    let result ← advance s next metadata
    return (next, result)
  else none

end ANL.Boot.Origin
