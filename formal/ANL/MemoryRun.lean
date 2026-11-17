import ANL.MemoryMachine

namespace ANL.Memory

def step (p : Program) (responses : Responses) (s : State) : Option State :=
  let a := s.current
  let k := s.kont
  let w := s.world
  let invalid : State := ⟨.invalid, a, k, w⟩
  match s.control with
  | .eval e => some (match e with
    | .lit _ v => ⟨.ret (.scalar v), a, k, w⟩
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
      | some binding => resume (APL.FlatProducts.embedResult (APL.checked (binding.length : Int))) a k w
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
      | .assign i => match APL.FlatProducts.update a.env i v with
        | none => invalid | some env => ⟨.ret (.scalar .unit), {a with env}, rest, w⟩
      | .ifF y n => match v with
        | .scalar (.bool test) => ⟨.eval (if test then y else n), a, rest, w⟩ | _ => invalid
      | .unary op => resume (APL.FlatProducts.unary op v) a rest w
      | .left op e => if APL.FlatProducts.shortCircuit op v then
          ⟨.ret v, a, rest, w⟩ else ⟨.eval e, a, .right op v :: rest, w⟩
      | .right op left => resume (APL.FlatProducts.binary op left v) a rest w
      | .arguments f loan args values => beginArguments f loan args (v :: values) a rest w
      | .callReturn _ _ => ⟨.revoke v, a, k, w⟩
      | .condition c b => match v with
        | .scalar (.bool true) => ⟨.eval b, a, .body c b :: rest, w⟩
        | .scalar (.bool false) => ⟨.ret (.scalar .unit), a, rest, w⟩
        | _ => invalid
      | .body c b => match v with
        | .scalar .unit => ⟨.eval c, a, .condition c b :: rest, w⟩ | _ => invalid
      | .fields args values => match v with
        | .tuple _ => invalid
        | .scalar value => match args with
          | [] => resume (APL.FlatProducts.construct (value :: values).reverse) a rest w
          | e :: fields => ⟨.eval e, a, .fields fields (value :: values) :: rest, w⟩
      | .project i => resume (APL.FlatProducts.project v i) a rest w
      | .heapLength site init yes no => ⟨.lengthReady site v init yes no, a, rest, w⟩
      | .heapInitial site n yes no => match v with
        | .scalar (.int value) => ⟨.allocate site n value yes no, a, rest, w⟩ | _ => invalid
      | .owner binding site => ⟨.close binding site v, a, k, w⟩
      | .readIndex binding => ⟨.readCheck binding v, a, rest, w⟩
      | .writeIndex binding value => ⟨.writeCheck binding v value, a, rest, w⟩
      | .writeValue binding i => match v with
        | .scalar (.int value) => ⟨.store binding i value, a, rest, w⟩ | _ => invalid)
  | .lengthReady site value init yes no => some (match value with
    | .scalar (.int n) => if n.val < 0 then ⟨.trap .invalidLength, a, k, w⟩
        else ⟨.eval init, a, .heapInitial site n.val.toNat yes no :: k, w⟩
    | _ => invalid)
  | .allocate site n init yes no => some (match allocate p.profile responses w site n init with
    | (.allocated ref, next) => ⟨.eval yes, {a with resources := ⟨.owner, ref, n⟩ :: a.resources},
        .owner ⟨.owner, ref, n⟩ site :: k, next⟩
    | (.refused, next) | (.targetRejected, next) => ⟨.eval no, a, k, next⟩)
  | .readCheck binding index => some (match index with
    | .scalar (.int index) => match checkedIndex binding.length index.val with
      | none => ⟨.trap .indexOutOfBounds, a, k, w⟩
      | some i => ⟨.readCell binding i, a, k, w⟩
    | _ => invalid)
  | .readCell binding i => some (match w.read binding.ref i with
    | none => invalid | some v => ⟨.ret (.scalar (.int v)), a, k, w⟩)
  | .writeCheck binding index value => some (match index with
    | .scalar (.int index) => match checkedIndex binding.length index.val with
      | none => ⟨.trap .indexOutOfBounds, a, k, w⟩
      | some i => ⟨.eval value, a, .writeValue binding i :: k, w⟩
    | _ => invalid)
  | .store binding i value => some (match w.write binding.ref i value with
    | none => invalid | some next => ⟨.ret (.scalar .unit), a, k, next⟩)
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

/-- The budget counts abstract transitions, independently of tool expression/fill fuel. -/
def run (p : Program) (responses : Responses) : Nat → State → Option State
  | 0, s => if (step p responses s).isNone then some s else none
  | fuel + 1, s => match step p responses s with
    | none => some s | some next => run p responses fuel next

theorem step_complete (h : Step p responses s next) : step p responses s = some next := by
  cases h <;> simp_all [step]
  all_goals split <;> simp_all [APL.FlatProducts.Val.type, APL.Val.type]
  all_goals split <;> simp_all

theorem bool_canonical {v : Val} (h : v.type = .scalar .bool) : ∃ b, v = .scalar (.bool b) := by
  cases v with
  | tuple fields => cases h
  | scalar value => cases value <;> simp_all [APL.FlatProducts.Val.type, APL.Val.type]

theorem int_canonical {v : Val} (h : v.type = .scalar .i64) : ∃ n, v = .scalar (.int n) := by
  cases v with
  | tuple fields => cases h
  | scalar value => cases value <;> simp_all [APL.FlatProducts.Val.type, APL.Val.type]

theorem unit_canonical {v : Val} (h : v.type = .scalar .unit) : v = .scalar .unit := by
  cases v with
  | tuple fields => cases h
  | scalar value => cases value <;> simp_all [APL.FlatProducts.Val.type, APL.Val.type]

set_option linter.unusedSimpArgs false in
theorem step_sound (h : step p responses s = some next) : Step p responses s next := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp only [step] at h
  all_goals repeat' split at h
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals try contradiction
  all_goals subst next
  all_goals try simp_all only [Bool.not_eq_true]
  all_goals try obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
  all_goals first
    | solve_by_elim (maxDepth := 6) [Step.lit, Step.localFound, Step.localMissing, Step.letEval, Step.letMutEval, Step.assignEval, Step.whileEval, Step.ifEval, Step.unaryEval, Step.binaryEval, Step.call, Step.tupleEmpty, Step.tupleFirst, Step.projectEval, Step.heapEval, Step.lengthFound, Step.lengthMissing, Step.readEval, Step.readMissing, Step.writeEval, Step.writeMissing, Step.writeDenied, Step.callView, Step.viewMissing, Step.viewDenied, Step.bindReturn, Step.scopeReturn, Step.scopeMissing, Step.assignReturn, Step.assignMissing, Step.ifTrue, Step.ifFalse, Step.ifWrong, Step.unaryReturn, Step.short, Step.rightEval, Step.binaryReturn, Step.argumentReturn, Step.callResult, Step.whileTrue, Step.whileFalse, Step.whileWrong, Step.whileAgain, Step.bodyWrong, Step.fieldNext, Step.fieldsDone, Step.fieldTuple, Step.projectReturn, Step.heapLengthReturn, Step.heapInitialReturn, Step.heapInitialWrong, Step.ownerReturn, Step.readIndexReturn, Step.writeIndexReturn, Step.writeValueReturn, Step.writeValueWrong, Step.negativeLength, Step.nonnegativeLength, Step.lengthWrong, Step.allocated, Step.allocationRefused, Step.allocationRejected, Step.readChecked, Step.readBounds, Step.readWrong, Step.readValue, Step.readUnavailable, Step.writeChecked, Step.writeBounds, Step.writeWrong, Step.stored, Step.storeUnavailable, Step.invoke, Step.invokeMissing, Step.invokeMode, Step.grant, Step.grantMissing, Step.closed, Step.closeUnavailable, Step.closeWrong, Step.revoke, Step.revokeWrong, Step.restore, Step.restoreWrong]
    | skip
  all_goals first
    | (apply Step.ifWrong; intro ht; obtain ⟨test, rfl⟩ := bool_canonical ht; simp_all)
    | (apply Step.whileWrong; intro ht; obtain ⟨test, rfl⟩ := bool_canonical ht; cases test <;> simp_all)
    | (apply Step.bodyWrong; intro ht; have he := unit_canonical ht; simp_all)
    | (apply Step.heapInitialWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.writeValueWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.lengthWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.readWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.writeWrong; intro ht; obtain ⟨value, rfl⟩ := int_canonical ht; simp_all)
    | (apply Step.closeWrong; intro k he; cases he; simp_all)

theorem step_iff : step p responses s = some next ↔ Step p responses s next :=
  ⟨step_sound, step_complete⟩

theorem deterministic (ha : Step p responses s a) (hb : Step p responses s b) : a = b :=
  Option.some.inj ((step_complete ha).symm.trans (step_complete hb))

theorem terminal_iff {s : State} : Terminal s ↔
    (∃ value, s.control = .ret value ∧ s.kont = []) ∨ ∃ kind, s.control = .trap kind := by
  constructor
  · intro h; cases h
    · exact .inl ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl⟩
  · intro h
    rcases s with ⟨control, a, k, w⟩
    rcases h with ⟨value, rfl, rfl⟩ | ⟨kind, rfl⟩
    · exact .value
    · exact .trap

theorem stopped_iff : step p responses s = none ↔ Terminal s ∨ s.control = .invalid := by
  rcases s with ⟨control, a, k, w⟩
  cases control <;> simp [step, terminal_iff]
  case ret value => cases k <;> simp

theorem run_sound (h : run p responses fuel s = some last) : Steps p responses s last ∧ step p responses last = none := by
  induction fuel generalizing s with
  | zero =>
    simp only [run] at h
    split at h
    next stop =>
      have stop : step p responses s = none := Option.isNone_iff_eq_none.mp stop
      cases h
      exact ⟨.refl, stop⟩
    · contradiction
  | succ fuel ih =>
    simp only [run] at h
    cases hs : step p responses s with
    | none => simp only [hs] at h; cases h; exact ⟨.refl, hs⟩
    | some s' =>
      simp only [hs] at h
      obtain ⟨rest, stop⟩ := ih h
      exact ⟨.head (step_sound hs) rest, stop⟩

theorem run_complete (h : Steps p responses s last) (stop : step p responses last = none) :
    ∃ fuel, run p responses fuel s = some last := by
  induction h with
  | refl => exact ⟨0, by simp [run, stop]⟩
  | head hs _ ih =>
    obtain ⟨fuel, hf⟩ := ih stop
    exact ⟨fuel + 1, by simp [run, step_complete hs, hf]⟩

theorem run_iff : (∃ fuel, run p responses fuel s = some last) ↔ Steps p responses s last ∧ step p responses last = none := by
  constructor
  · rintro ⟨fuel, h⟩; exact run_sound h
  · rintro ⟨hs, stop⟩; exact run_complete hs stop

end ANL.Memory
