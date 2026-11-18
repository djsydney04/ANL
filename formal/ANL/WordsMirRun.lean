import ANL.WordsMirMachine

namespace ANL.Words.Mir

open ANL.Memory

def step (p : Program) (responses : Responses) (s : State) : Option State :=
  let a := s.current
  let k := s.kont
  let w := s.world
  let invalid : State := ⟨.invalid, a, k, w⟩
  match s.control with
  | .block body => some ⟨.sequence body, a, .blockEnd a.temps :: k, w⟩
  | .sequence body => some (match body with
    | .yield value => match a.temp value with
      | none => invalid | some v => ⟨.ret v, a, k, w⟩
    | .next destination op rest => ⟨.operation op, a, .instruction destination rest :: k, w⟩)
  | .operation op => some (match op with
    | .integer value => ⟨.ret (.scalar (.legacy (.int value))), a, k, w⟩
    | .word width value => resume (wordLiteral width value) a k w
    | .convert mode target operand => match a.temp operand with
      | none => invalid | some value => resume (convert mode target value) a k w
    | .boolean value => ⟨.ret (.scalar (.legacy (.bool value))), a, k, w⟩
    | .unit => ⟨.ret (.scalar (.legacy .unit)), a, k, w⟩
    | .tuple fields => match a.capture fields with
      | none => invalid | some values => resume (constructTuple values) a k w
    | .project value index => match a.temp value with
      | none => invalid | some v => resume (ANL.Words.project v index) a k w
    | .unary op operand => match a.temp operand with
      | none => invalid | some v => resume (ANL.Words.unary op v) a k w
    | .binary op left right => match a.pair left right with
      | none => invalid | some (l, r) => resume (ANL.Words.binary op l r) a k w
    | .call f arguments => match a.capture arguments with
      | none => invalid | some values => ⟨.invoke f none values, a, k, w⟩
    | .mutableScope slot initial body => match a.temp initial with
      | none => invalid
      | some v => ⟨.block body, { a with slots := (slot.id, v) :: a.slots }, .slotScope slot.id :: k, w⟩
    | .load slot => match a.slot slot with
      | none => invalid | some v => ⟨.ret v, a, k, w⟩
    | .store slot value => match a.temp value with
      | none => invalid
      | some v => match updateId slot.id v a.slots with
        | none => invalid | some slots => ⟨.ret (.scalar (.legacy .unit)), { a with slots }, k, w⟩
    | .whileE condition body => ⟨.block condition, a, .condition condition body :: k, w⟩
    | .branch condition yes no => match a.temp condition with
      | some (.scalar (.legacy (.bool test))) => ⟨.block (if test then yes else no), a, k, w⟩
      | _ => invalid
    | .heapScope site owner length init yes no => match a.temp length with
      | none => invalid
      | some value => ⟨.lengthReady ⟨a.function, site⟩ owner value init yes no, a, k, w⟩
    | .bufferLength resource => match a.resource resource with
      | none => invalid
      | some binding => resume (ANL.Words.legacyResult (APL.checked (binding.length : Int))) a k w
    | .bufferRead resource index => match a.resource resource, a.temp index with
      | some binding, some value => ⟨.readCheck binding value, a, k, w⟩
      | _, _ => invalid
    | .bufferWrite resource index value => match a.resource resource, a.temp index with
      | some binding, some index => if binding.mode.CanWrite then
          ⟨.writeCheck binding index value, a, k, w⟩ else invalid
      | _, _ => invalid
    | .callView f resource mode arguments => match a.resource resource, a.capture arguments with
      | some binding, some values => if binding.mode.CanLend mode then
          ⟨.invoke f (some ⟨binding, mode⟩) values, a, k, w⟩ else invalid
      | _, _ => invalid)
  | .ret value => match k with
    | [] => none
    | frame :: rest => some (match frame with
      | .instruction destination remaining =>
          ⟨.sequence remaining, { a with temps := (destination.id, value) :: a.temps }, rest, w⟩
      | .blockEnd temps => ⟨.ret value, { a with temps }, rest, w⟩
      | .slotScope id => match a.slots with
        | (found, _) :: slots => if id = found then
            ⟨.ret value, { a with slots }, rest, w⟩ else invalid
        | [] => invalid
      | .condition condition body => match value with
        | .scalar (.legacy (.bool true)) => ⟨.block body, a, .body condition body :: rest, w⟩
        | .scalar (.legacy (.bool false)) => ⟨.ret (.scalar (.legacy .unit)), a, rest, w⟩
        | _ => invalid
      | .body condition body => match value with
        | .scalar (.legacy .unit) => ⟨.block condition, a, .condition condition body :: rest, w⟩
        | _ => invalid
      | .heapInitial site owner length yes no => match value with
        | .scalar (.legacy (.int v)) => ⟨.allocate site owner length v yes no, a, rest, w⟩
        | _ => invalid
      | .owner id binding site => ⟨.close id binding site value, a, k, w⟩
      | .writeValue binding index => match value with
        | .scalar (.legacy (.int v)) => ⟨.store binding index v, a, rest, w⟩
        | _ => invalid
      | .callReturn _ _ => ⟨.revoke value, a, k, w⟩)
  | .lengthReady site owner value init yes no => some (match value with
    | .scalar (.legacy (.int n)) => if n.val < 0 then ⟨.trap .invalidLength, a, k, w⟩
        else ⟨.block init, a, .heapInitial site owner n.val.toNat yes no :: k, w⟩
    | _ => invalid)
  | .allocate site owner n init yes no => some (match allocate p.allocationProfile responses w site n init with
    | (.allocated ref, next) =>
        let binding : Binding := ⟨.owner, ref, n⟩
        ⟨.block yes, { a with resources := (owner, binding) :: a.resources },
          .owner owner binding site :: k, next⟩
    | (.refused, next) | (.targetRejected, next) => ⟨.block no, a, k, next⟩)
  | .readCheck binding index => some (match index with
    | .scalar (.legacy (.int index)) => match checkedIndex binding.length index.val with
      | none => ⟨.trap .indexOutOfBounds, a, k, w⟩
      | some i => ⟨.readCell binding i, a, k, w⟩
    | _ => invalid)
  | .readCell binding i => some (match w.read binding.ref i with
    | none => invalid | some value => ⟨.ret (.scalar (.legacy (.int value))), a, k, w⟩)
  | .writeCheck binding index value => some (match index with
    | .scalar (.legacy (.int index)) => match checkedIndex binding.length index.val with
      | none => ⟨.trap .indexOutOfBounds, a, k, w⟩
      | some i => ⟨.block value, a, .writeValue binding i :: k, w⟩
    | _ => invalid)
  | .store binding index value => some (match w.write binding.ref index value with
    | none => invalid | some next => ⟨.ret (.scalar (.legacy .unit)), a, k, next⟩)
  | .invoke f loan values => some (match p.functions[f]? with
    | none => invalid
    | some fn => if fn.signature.view = loanMode loan then
        ⟨.grant f loan values, a, k, w⟩ else invalid)
  | .grant f loan values => some (match p.functions[f]? with
    | none => invalid
    | some fn => match callee f fn loan values with
      | none => invalid
      | some activation => ⟨.block fn.body, activation, .callReturn a loan :: k, w⟩)
  | .close id binding site value => some (match k, a.resources with
    | .owner openedId top openedSite :: rest, (resourceId, resource) :: resources =>
        if openedId = id ∧ top = binding ∧ openedSite = site ∧ resourceId = id ∧ resource = binding then
          match w.close binding.ref site with
          | none => invalid
          | some next => ⟨.ret value, { a with resources }, rest, next⟩
        else invalid
    | _, _ => invalid)
  | .revoke value => some (match k with
    | .callReturn _ _ :: _ => ⟨.restore value, a, k, w⟩ | _ => invalid)
  | .restore value => some (match k with
    | .callReturn caller _ :: rest => ⟨.ret value, caller, rest, w⟩ | _ => invalid)
  | .trap _ | .invalid => none

inductive RunResult where
  | completed (state : State)
  | exhausted (state : State)
  deriving Repr

def RunResult.state : RunResult → State
  | .completed s | .exhausted s => s

/-- This budget counts MIR transitions, not source expression/fill fuel. -/
def run (p : Program) (responses : Responses) : Nat → State → RunResult
  | 0, s => if isStopped s then .completed s else .exhausted s
  | budget + 1, s => match step p responses s with
    | none => .completed s | some next => run p responses budget next

end ANL.Words.Mir
