import ANL.WordsMachine

namespace ANL.Words

open ANL.Memory

def step (p : Program) (responses : Responses) (s : State) : Option State :=
  let a := s.current
  let k := s.kont
  let w := s.world
  let invalid : State := ⟨.invalid, a, k, w⟩
  match s.control with
  | .eval e => some (match e with
    | .lit _ v => ⟨.ret (.scalar (.legacy v)), a, k, w⟩
    | .word _ width value => resume (wordLiteral width value) a k w
    | .convert _ mode target e => ⟨.eval e, a, .convert mode target :: k, w⟩
    | .local _ i => match a.env[i]? with
      | some v => ⟨.ret v, a, k, w⟩ | none => invalid
    | .letE _ e b => ⟨.eval e, a, .bind false b :: k, w⟩
    | .letMut _ e b => ⟨.eval e, a, .bind true b :: k, w⟩
    | .assign _ i e => ⟨.eval e, a, .assign i :: k, w⟩
    | .whileE _ c b => ⟨.eval c, a, .condition c b :: k, w⟩
    | .ifE _ c y n => ⟨.eval c, a, .ifF y n :: k, w⟩
    | .unary _ op e => ⟨.eval e, a, .unary op :: k, w⟩
    | .binary _ op e b => ⟨.eval e, a, .left op b :: k, w⟩
    | .call _ f args => beginArguments f none args [] a k w
    | .tuple _ [] => invalid
    | .tuple _ (e :: rest) => ⟨.eval e, a, .fields rest [] :: k, w⟩
    | .project _ e i => ⟨.eval e, a, .project i :: k, w⟩
    | .heap _ h len init yes no => ⟨.eval len, a, .heapLength ⟨a.function, h⟩ init yes no :: k, w⟩
    | .bufferLength _ i => match a.resources[i]? with
      | none => invalid
      | some binding => resume (legacyResult (APL.checked (binding.length : Int))) a k w
    | .bufferRead _ i index => match a.resources[i]? with
      | none => invalid
      | some binding => ⟨.eval index, a, .readIndex binding :: k, w⟩
    | .bufferWrite _ i index value => match a.resources[i]? with
      | none => invalid
      | some binding => if binding.mode.CanWrite then
          ⟨.eval index, a, .writeIndex binding value :: k, w⟩ else invalid
    | .callView _ f i mode args => match a.resources[i]? with
      | none => invalid
      | some binding => if binding.mode.CanLend mode then
          beginArguments f (some ⟨binding, mode⟩) args [] a k w else invalid)
  | .ret v => match k with
    | [] => none
    | frame :: rest => some (match frame with
      | .bind _ b => ⟨.eval b, {a with env := v :: a.env}, .scope :: rest, w⟩
      | .scope => match a.env with
        | [] => invalid | _ :: env => ⟨.ret v, {a with env}, rest, w⟩
      | .assign i => match update a.env i v with
        | none => invalid | some env => ⟨.ret (.scalar (.legacy .unit)), {a with env}, rest, w⟩
      | .ifF y n => match v with
        | .scalar (.legacy (.bool test)) => ⟨.eval (if test then y else n), a, rest, w⟩ | _ => invalid
      | .convert mode target => resume (convert mode target v) a rest w
      | .unary op => resume (unary op v) a rest w
      | .left op e => if shortCircuit op v then
          ⟨.ret v, a, rest, w⟩ else ⟨.eval e, a, .right op v :: rest, w⟩
      | .right op left => resume (binary op left v) a rest w
      | .arguments f loan args values => beginArguments f loan args (v :: values) a rest w
      | .callReturn _ _ => ⟨.revoke v, a, k, w⟩
      | .condition c b => match v with
        | .scalar (.legacy (.bool true)) => ⟨.eval b, a, .body c b :: rest, w⟩
        | .scalar (.legacy (.bool false)) => ⟨.ret (.scalar (.legacy .unit)), a, rest, w⟩
        | _ => invalid
      | .body c b => match v with
        | .scalar (.legacy .unit) => ⟨.eval c, a, .condition c b :: rest, w⟩ | _ => invalid
      | .fields args values => match v with
        | .tuple _ => invalid
        | .scalar value => match args with
          | [] => resume (construct (value :: values).reverse) a rest w
          | e :: fields => ⟨.eval e, a, .fields fields (value :: values) :: rest, w⟩
      | .project i => resume (project v i) a rest w
      | .heapLength site init yes no => ⟨.lengthReady site v init yes no, a, rest, w⟩
      | .heapInitial site n yes no => match v with
        | .scalar (.legacy (.int value)) => ⟨.allocate site n value yes no, a, rest, w⟩ | _ => invalid
      | .owner binding site => ⟨.close binding site v, a, k, w⟩
      | .readIndex binding => ⟨.readCheck binding v, a, rest, w⟩
      | .writeIndex binding value => ⟨.writeCheck binding v value, a, rest, w⟩
      | .writeValue binding i => match v with
        | .scalar (.legacy (.int value)) => ⟨.store binding i value, a, rest, w⟩ | _ => invalid)
  | .lengthReady site value init yes no => some (match value with
    | .scalar (.legacy (.int n)) => if n.val < 0 then ⟨.trap .invalidLength, a, k, w⟩
        else ⟨.eval init, a, .heapInitial site n.val.toNat yes no :: k, w⟩
    | _ => invalid)
  | .allocate site n init yes no => some (match allocate p.profile responses w site n init with
    | (.allocated ref, next) => ⟨.eval yes, {a with resources := ⟨.owner, ref, n⟩ :: a.resources},
        .owner ⟨.owner, ref, n⟩ site :: k, next⟩
    | (.refused, next) | (.targetRejected, next) => ⟨.eval no, a, k, next⟩)
  | .readCheck binding index => some (match index with
    | .scalar (.legacy (.int index)) => match checkedIndex binding.length index.val with
      | none => ⟨.trap .indexOutOfBounds, a, k, w⟩
      | some i => ⟨.readCell binding i, a, k, w⟩
    | _ => invalid)
  | .readCell binding i => some (match w.read binding.ref i with
    | none => invalid | some v => ⟨.ret (.scalar (.legacy (.int v))), a, k, w⟩)
  | .writeCheck binding index value => some (match index with
    | .scalar (.legacy (.int index)) => match checkedIndex binding.length index.val with
      | none => ⟨.trap .indexOutOfBounds, a, k, w⟩
      | some i => ⟨.eval value, a, .writeValue binding i :: k, w⟩
    | _ => invalid)
  | .store binding i value => some (match w.write binding.ref i value with
    | none => invalid | some next => ⟨.ret (.scalar (.legacy .unit)), a, k, next⟩)
  | .invoke f loan values => some (match p.functions[f]? with
    | none => invalid
    | some fn => if fn.view = loanMode loan then ⟨.grant f loan values, a, k, w⟩ else invalid)
  | .grant f loan values => some (match p.functions[f]? with
    | none => invalid
    | some fn => ⟨.eval fn.body, ⟨f, values, loanResources loan⟩, .callReturn a loan :: k, w⟩)
  | .close binding site value => some (match k with
    | .owner top opened :: rest => if top = binding ∧ opened = site then
        match w.close binding.ref site with
        | none => invalid
        | some next => ⟨.ret value, {a with resources := a.resources.tail}, rest, next⟩
      else invalid
    | _ => invalid)
  | .revoke value => some (match k with
    | .callReturn _ _ :: _ => ⟨.restore value, a, k, w⟩ | _ => invalid)
  | .restore value => some (match k with
    | .callReturn caller _ :: rest => ⟨.ret value, caller, rest, w⟩ | _ => invalid)
  | .trap _ | .invalid => none

def isStopped (s : State) : Bool :=
  match s.control with
  | .ret _ => s.kont.isEmpty
  | .trap _ | .invalid => true
  | _ => false

def RawStopped (s : State) : Prop := Terminal s ∨ s.control = .invalid

inductive RunResult where
  | completed (state : State)
  | exhausted (state : State)
  deriving Repr

def RunResult.state : RunResult → State
  | .completed state | .exhausted state => state

/-- Retains the exact cutoff state. Budget zero never evaluates a semantic transition. -/
def execute (p : Program) (responses : Responses) : Nat → State → RunResult
  | 0, s => if isStopped s then .completed s else .exhausted s
  | budget + 1, s => match step p responses s with
    | none => .completed s
    | some next => execute p responses budget next

inductive StepsN (p : Program) (responses : Responses) : Nat → State → State → Prop where
  | zero : StepsN p responses 0 s s
  | succ : Step p responses s middle → StepsN p responses n middle last → StepsN p responses (n + 1) s last

end ANL.Words
