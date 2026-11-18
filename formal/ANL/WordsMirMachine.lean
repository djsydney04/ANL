import ANL.WordsMirTyping
import ANL.MemoryMirMachine

namespace ANL.Words.Mir

open ANL.Memory

abbrev Binding := ANL.Memory.Mir.Binding
abbrev Loan := ANL.Memory.Mir.Loan
abbrev loanMode := ANL.Memory.Mir.loanMode
abbrev lookupId := @ANL.Memory.Mir.lookupId
abbrev updateId := @ANL.Memory.Mir.updateId
abbrev Values := List (Nat × Val)
abbrev Resources := List (Nat × Binding)
abbrev Trap := ANL.Words.Trap

structure Activation where
  function : Nat
  temps : Values
  slots : Values
  resources : Resources
  deriving Repr

def Activation.temp (a : Activation) (v : Temp) : Option Val := lookupId v.id a.temps
def Activation.slot (a : Activation) (s : Slot) : Option Val := lookupId s.id a.slots
def Activation.resource (a : Activation) (r : Nat) : Option Binding := lookupId r a.resources
def Activation.capture (a : Activation) (args : List Temp) : Option (List Val) := args.mapM a.temp
def Activation.pair (a : Activation) (left right : Temp) : Option (Val × Val) := do
  let l ← a.temp left
  let r ← a.temp right
  pure (l, r)

/-- Exact recursive arity matching; annotations are checked by the independent static judgment. -/
def bindParameters : List Temp → List Val → Option Values
  | [], [] => some []
  | p :: ps, v :: vs => (bindParameters ps vs).map ((p.id, v) :: ·)
  | _, _ => none

def bindView : Option (ViewMode × Nat) → Option Loan → Option Resources
  | none, none => some []
  | some (mode, id), some loan =>
      if mode = loan.mode then some [(id, loan.binding)] else none
  | _, _ => none

def callee (f : Nat) (fn : Function) (loan : Option Loan) (values : List Val) : Option Activation := do
  let temps ← bindParameters fn.params values
  let resources ← bindView fn.view loan
  pure ⟨f, temps, [], resources⟩

def constructTuple (values : List Val) : ANL.Words.Result :=
  match values.mapM (fun v => match v with | .scalar x => some x | .tuple _ => none) with
  | none => .invalid
  | some scalars => ANL.Words.construct scalars

inductive Frame where
  | instruction (destination : Temp) (rest : Block)
  | blockEnd (savedTemps : Values)
  | slotScope (slot : Nat)
  | condition (condition body : Block)
  | body (condition body : Block)
  | heapInitial (site : Site) (owner length : Nat) (success failure : Block)
  | owner (id : Nat) (binding : Binding) (site : Site)
  | writeValue (binding : Binding) (index : Nat)
  | callReturn (caller : Activation) (loan : Option Loan)
  deriving Repr

inductive Control where
  | block (body : Block)
  | sequence (body : Block)
  | operation (op : Operation)
  | ret (value : Val)
  | lengthReady (site : Site) (owner : Nat) (value : Val) (initial success failure : Block)
  | allocate (site : Site) (owner length : Nat) (initial : APL.I64) (success failure : Block)
  | readCheck (binding : Binding) (index : Val)
  | readCell (binding : Binding) (index : Nat)
  | writeCheck (binding : Binding) (index : Val) (value : Block)
  | store (binding : Binding) (index : Nat) (value : APL.I64)
  | invoke (function : Nat) (loan : Option Loan) (values : List Val)
  | grant (function : Nat) (loan : Option Loan) (values : List Val)
  | close (id : Nat) (binding : Binding) (site : Site) (value : Val)
  | revoke (value : Val)
  | restore (value : Val)
  | trap (kind : Trap)
  | invalid
  deriving Repr

structure State where
  control : Control
  current : Activation
  kont : List Frame
  world : World
  deriving Repr

/-- Revoked callee descriptors are passive metadata until the caller is restored. -/
def State.accessible (s : State) : Resources :=
  match s.control with | .restore _ => [] | _ => s.current.resources

def resume (result : ANL.Words.Result) (a : Activation) (k : List Frame) (w : World) : State :=
  match result with
  | .value value => ⟨.ret value, a, k, w⟩
  | .trap kind => ⟨.trap kind, a, k, w⟩
  | .invalid => ⟨.invalid, a, k, w⟩

def initial (p : Program) : State :=
  ⟨.invoke p.entry none [], ⟨p.entry, [], [], []⟩, [], .initial⟩

def CloseReady (k : List Frame) (resources : Resources) (id : Nat) (binding : Binding) (site : Site) : Prop :=
  match k, resources with
  | .owner openedId top openedSite :: _, (resourceId, resource) :: _ =>
      openedId = id ∧ top = binding ∧ openedSite = site ∧ resourceId = id ∧ resource = binding
  | _, _ => False

/-- Independent raw transition rules, without reference to the executable step function. -/
inductive Step (p : Program) (responses : Responses) : State → State → Prop where
  | block : Step p responses ⟨.block body, a, k, w⟩ ⟨.sequence body, a, .blockEnd a.temps :: k, w⟩
  | instruction : Step p responses ⟨.sequence (.next d op rest), a, k, w⟩
      ⟨.operation op, a, .instruction d rest :: k, w⟩
  | yieldFound : a.temp value = some v →
      Step p responses ⟨.sequence (.yield value), a, k, w⟩ ⟨.ret v, a, k, w⟩
  | yieldMissing : a.temp value = none →
      Step p responses ⟨.sequence (.yield value), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | integer : Step p responses ⟨.operation (.integer n), a, k, w⟩ ⟨.ret (.scalar (.legacy (.int n))), a, k, w⟩
  | word : Step p responses ⟨.operation (.word width value), a, k, w⟩
      (resume (wordLiteral width value) a k w)
  | convertFound : a.temp operand = some value →
      Step p responses ⟨.operation (.convert mode target operand), a, k, w⟩
        (resume (convert mode target value) a k w)
  | convertMissing : a.temp operand = none →
      Step p responses ⟨.operation (.convert mode target operand), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | boolean : Step p responses ⟨.operation (.boolean v), a, k, w⟩ ⟨.ret (.scalar (.legacy (.bool v))), a, k, w⟩
  | unit : Step p responses ⟨.operation .unit, a, k, w⟩ ⟨.ret (.scalar (.legacy .unit)), a, k, w⟩
  | tupleFound : a.capture fields = some values →
      Step p responses ⟨.operation (.tuple fields), a, k, w⟩ (resume (constructTuple values) a k w)
  | tupleMissing : a.capture fields = none →
      Step p responses ⟨.operation (.tuple fields), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | projectFound : a.temp value = some v →
      Step p responses ⟨.operation (.project value index), a, k, w⟩
        (resume (ANL.Words.project v index) a k w)
  | projectMissing : a.temp value = none →
      Step p responses ⟨.operation (.project value index), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | unaryFound : a.temp value = some v →
      Step p responses ⟨.operation (.unary op value), a, k, w⟩
        (resume (ANL.Words.unary op v) a k w)
  | unaryMissing : a.temp value = none →
      Step p responses ⟨.operation (.unary op value), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | binaryFound : a.pair left right = some (l, r) →
      Step p responses ⟨.operation (.binary op left right), a, k, w⟩
        (resume (ANL.Words.binary op l r) a k w)
  | binaryMissing : a.pair left right = none →
      Step p responses ⟨.operation (.binary op left right), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | callFound : a.capture args = some values →
      Step p responses ⟨.operation (.call f args), a, k, w⟩ ⟨.invoke f none values, a, k, w⟩
  | callMissing : a.capture args = none →
      Step p responses ⟨.operation (.call f args), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | mutableFound : a.temp value = some v →
      Step p responses ⟨.operation (.mutableScope slot value body), a, k, w⟩
        ⟨.block body, { a with slots := (slot.id, v) :: a.slots }, .slotScope slot.id :: k, w⟩
  | mutableMissing : a.temp value = none →
      Step p responses ⟨.operation (.mutableScope slot value body), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | loadFound : a.slot slot = some v →
      Step p responses ⟨.operation (.load slot), a, k, w⟩ ⟨.ret v, a, k, w⟩
  | loadMissing : a.slot slot = none →
      Step p responses ⟨.operation (.load slot), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | storeValueMissing : a.temp value = none →
      Step p responses ⟨.operation (.store slot value), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | storeSlotMissing : a.temp value = some v → updateId slot.id v a.slots = none →
      Step p responses ⟨.operation (.store slot value), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | storeSlot : a.temp value = some v → updateId slot.id v a.slots = some slots →
      Step p responses ⟨.operation (.store slot value), a, k, w⟩
        ⟨.ret (.scalar (.legacy .unit)), { a with slots }, k, w⟩
  | whileStart : Step p responses ⟨.operation (.whileE c b), a, k, w⟩
      ⟨.block c, a, .condition c b :: k, w⟩
  | branchTrue : a.temp condition = some (.scalar (.legacy (.bool true))) →
      Step p responses ⟨.operation (.branch condition yes no), a, k, w⟩ ⟨.block yes, a, k, w⟩
  | branchFalse : a.temp condition = some (.scalar (.legacy (.bool false))) →
      Step p responses ⟨.operation (.branch condition yes no), a, k, w⟩ ⟨.block no, a, k, w⟩
  | branchWrong : (∀ b, a.temp condition ≠ some (.scalar (.legacy (.bool b)))) →
      Step p responses ⟨.operation (.branch condition yes no), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | heapFound : a.temp length = some value →
      Step p responses ⟨.operation (.heapScope site owner length init yes no), a, k, w⟩
        ⟨.lengthReady ⟨a.function, site⟩ owner value init yes no, a, k, w⟩
  | heapMissing : a.temp length = none →
      Step p responses ⟨.operation (.heapScope site owner length init yes no), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | lengthFound : a.resource r = some binding →
      Step p responses ⟨.operation (.bufferLength r), a, k, w⟩
        (resume (ANL.Words.legacyResult (APL.checked (binding.length : Int))) a k w)
  | lengthMissing : a.resource r = none →
      Step p responses ⟨.operation (.bufferLength r), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | readFound : a.resource r = some binding → a.temp index = some value →
      Step p responses ⟨.operation (.bufferRead r index), a, k, w⟩ ⟨.readCheck binding value, a, k, w⟩
  | readMissing : a.resource r = none ∨ a.temp index = none →
      Step p responses ⟨.operation (.bufferRead r index), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | writeFound : a.resource r = some binding → a.temp index = some value → binding.mode.CanWrite →
      Step p responses ⟨.operation (.bufferWrite r index rhs), a, k, w⟩ ⟨.writeCheck binding value rhs, a, k, w⟩
  | writeMissing : a.resource r = none ∨ a.temp index = none →
      Step p responses ⟨.operation (.bufferWrite r index rhs), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | writeDenied : a.resource r = some binding → a.temp index = some value → ¬ binding.mode.CanWrite →
      Step p responses ⟨.operation (.bufferWrite r index rhs), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | viewFound : a.resource r = some binding → a.capture args = some values → binding.mode.CanLend mode →
      Step p responses ⟨.operation (.callView f r mode args), a, k, w⟩
        ⟨.invoke f (some ⟨binding, mode⟩) values, a, k, w⟩
  | viewMissing : a.resource r = none ∨ a.capture args = none →
      Step p responses ⟨.operation (.callView f r mode args), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | viewDenied : a.resource r = some binding → a.capture args = some values → ¬ binding.mode.CanLend mode →
      Step p responses ⟨.operation (.callView f r mode args), a, k, w⟩ ⟨.invalid, a, k, w⟩
  | instructionReturn : Step p responses ⟨.ret value, a, .instruction destination remaining :: k, w⟩
      ⟨.sequence remaining, { a with temps := (destination.id, value) :: a.temps }, k, w⟩
  | blockReturn : Step p responses ⟨.ret value, a, .blockEnd temps :: k, w⟩
      ⟨.ret value, { a with temps }, k, w⟩
  | slotReturn : a.slots = (bindingId, prior) :: slots →
      Step p responses ⟨.ret value, a, .slotScope bindingId :: k, w⟩ ⟨.ret value, { a with slots }, k, w⟩
  | slotWrong : (∀ prior slots, a.slots ≠ (bindingId, prior) :: slots) →
      Step p responses ⟨.ret value, a, .slotScope bindingId :: k, w⟩ ⟨.invalid, a, .slotScope bindingId :: k, w⟩
  | whileTrue : Step p responses ⟨.ret (.scalar (.legacy (.bool true))), a, .condition c b :: k, w⟩
      ⟨.block b, a, .body c b :: k, w⟩
  | whileFalse : Step p responses ⟨.ret (.scalar (.legacy (.bool false))), a, .condition c b :: k, w⟩
      ⟨.ret (.scalar (.legacy .unit)), a, k, w⟩
  | whileWrong : value.type ≠ .scalar (.legacy .bool) →
      Step p responses ⟨.ret value, a, .condition c b :: k, w⟩ ⟨.invalid, a, .condition c b :: k, w⟩
  | whileAgain : Step p responses ⟨.ret (.scalar (.legacy .unit)), a, .body c b :: k, w⟩
      ⟨.block c, a, .condition c b :: k, w⟩
  | bodyWrong : value.type ≠ .scalar (.legacy .unit) →
      Step p responses ⟨.ret value, a, .body c b :: k, w⟩ ⟨.invalid, a, .body c b :: k, w⟩
  | heapInitialReturn : Step p responses ⟨.ret (.scalar (.legacy (.int value))), a, .heapInitial site owner n yes no :: k, w⟩
      ⟨.allocate site owner n value yes no, a, k, w⟩
  | heapInitialWrong : value.type ≠ .scalar (.legacy .i64) →
      Step p responses ⟨.ret value, a, .heapInitial site owner n yes no :: k, w⟩
        ⟨.invalid, a, .heapInitial site owner n yes no :: k, w⟩
  | ownerReturn : Step p responses ⟨.ret value, a, .owner bindingId binding site :: k, w⟩
      ⟨.close bindingId binding site value, a, .owner bindingId binding site :: k, w⟩
  | writeValueReturn : Step p responses ⟨.ret (.scalar (.legacy (.int value))), a, .writeValue binding index :: k, w⟩
      ⟨.store binding index value, a, k, w⟩
  | writeValueWrong : value.type ≠ .scalar (.legacy .i64) →
      Step p responses ⟨.ret value, a, .writeValue binding index :: k, w⟩
        ⟨.invalid, a, .writeValue binding index :: k, w⟩
  | callReturn : Step p responses ⟨.ret value, a, .callReturn caller loan :: k, w⟩
      ⟨.revoke value, a, .callReturn caller loan :: k, w⟩
  | negativeLength : n.val < 0 →
      Step p responses ⟨.lengthReady site owner (.scalar (.legacy (.int n))) init yes no, a, k, w⟩
        ⟨.trap .invalidLength, a, k, w⟩
  | nonnegativeLength : ¬ n.val < 0 →
      Step p responses ⟨.lengthReady site owner (.scalar (.legacy (.int n))) init yes no, a, k, w⟩
        ⟨.block init, a, .heapInitial site owner n.val.toNat yes no :: k, w⟩
  | lengthWrong : value.type ≠ .scalar (.legacy .i64) →
      Step p responses ⟨.lengthReady site owner value init yes no, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | allocated : allocate p.allocationProfile responses w site n init = (.allocated ref, next) →
      Step p responses ⟨.allocate site owner n init yes no, a, k, w⟩
        ⟨.block yes, { a with resources := (owner, ⟨.owner, ref, n⟩) :: a.resources },
          .owner owner ⟨.owner, ref, n⟩ site :: k, next⟩
  | allocationRefused : allocate p.allocationProfile responses w site n init = (.refused, next) →
      Step p responses ⟨.allocate site owner n init yes no, a, k, w⟩ ⟨.block no, a, k, next⟩
  | allocationRejected : allocate p.allocationProfile responses w site n init = (.targetRejected, next) →
      Step p responses ⟨.allocate site owner n init yes no, a, k, w⟩ ⟨.block no, a, k, next⟩
  | readChecked : checkedIndex binding.length index.val = some i →
      Step p responses ⟨.readCheck binding (.scalar (.legacy (.int index))), a, k, w⟩ ⟨.readCell binding i, a, k, w⟩
  | readBounds : checkedIndex binding.length index.val = none →
      Step p responses ⟨.readCheck binding (.scalar (.legacy (.int index))), a, k, w⟩ ⟨.trap .indexOutOfBounds, a, k, w⟩
  | readWrong : value.type ≠ .scalar (.legacy .i64) →
      Step p responses ⟨.readCheck binding value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | readValue : w.read binding.ref i = some value →
      Step p responses ⟨.readCell binding i, a, k, w⟩ ⟨.ret (.scalar (.legacy (.int value))), a, k, w⟩
  | readAbsent : w.read binding.ref i = none →
      Step p responses ⟨.readCell binding i, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | writeChecked : checkedIndex binding.length index.val = some i →
      Step p responses ⟨.writeCheck binding (.scalar (.legacy (.int index))) value, a, k, w⟩
        ⟨.block value, a, .writeValue binding i :: k, w⟩
  | writeBounds : checkedIndex binding.length index.val = none →
      Step p responses ⟨.writeCheck binding (.scalar (.legacy (.int index))) value, a, k, w⟩
        ⟨.trap .indexOutOfBounds, a, k, w⟩
  | writeWrong : index.type ≠ .scalar (.legacy .i64) →
      Step p responses ⟨.writeCheck binding index value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | stored : w.write binding.ref index value = some next →
      Step p responses ⟨.store binding index value, a, k, w⟩ ⟨.ret (.scalar (.legacy .unit)), a, k, next⟩
  | storeAbsent : w.write binding.ref index value = none →
      Step p responses ⟨.store binding index value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | invokeMissing : p.functions[f]? = none →
      Step p responses ⟨.invoke f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | invokeFound : p.functions[f]? = some fn → fn.signature.view = loanMode loan →
      Step p responses ⟨.invoke f loan values, a, k, w⟩ ⟨.grant f loan values, a, k, w⟩
  | invokeWrong : p.functions[f]? = some fn → fn.signature.view ≠ loanMode loan →
      Step p responses ⟨.invoke f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | grantMissing : p.functions[f]? = none →
      Step p responses ⟨.grant f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | grantWrong : p.functions[f]? = some fn → callee f fn loan values = none →
      Step p responses ⟨.grant f loan values, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | grantFound : p.functions[f]? = some fn → callee f fn loan values = some activation →
      Step p responses ⟨.grant f loan values, a, k, w⟩
        ⟨.block fn.body, activation, .callReturn a loan :: k, w⟩
  | closeFound : a.resources = (bindingId, binding) :: resources → w.close binding.ref site = some next →
      Step p responses ⟨.close bindingId binding site value, a, .owner bindingId binding site :: k, w⟩
        ⟨.ret value, { a with resources }, k, next⟩
  | closeWrong : ¬ CloseReady k a.resources bindingId binding site →
      Step p responses ⟨.close bindingId binding site value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | closeAbsent : CloseReady k a.resources bindingId binding site → w.close binding.ref site = none →
      Step p responses ⟨.close bindingId binding site value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | revoke : Step p responses ⟨.revoke value, a, .callReturn caller loan :: k, w⟩
      ⟨.restore value, a, .callReturn caller loan :: k, w⟩
  | revokeWrong : (∀ caller loan rest, k ≠ .callReturn caller loan :: rest) →
      Step p responses ⟨.revoke value, a, k, w⟩ ⟨.invalid, a, k, w⟩
  | restore : Step p responses ⟨.restore value, a, .callReturn caller loan :: k, w⟩
      ⟨.ret value, caller, k, w⟩
  | restoreWrong : (∀ caller loan rest, k ≠ .callReturn caller loan :: rest) →
      Step p responses ⟨.restore value, a, k, w⟩ ⟨.invalid, a, k, w⟩

inductive Steps (p : Program) (responses : Responses) : State → State → Prop where
  | refl : Steps p responses s s
  | cons : Step p responses s t → Steps p responses t u → Steps p responses s u

def RawStopped (s : State) : Prop :=
  match s.control with
  | .ret _ => s.kont = []
  | .trap _ | .invalid => True
  | _ => False

/-- A finished language outcome; unlike RawStopped, this excludes invalid raw states. -/
def Terminal (s : State) : Prop :=
  match s.control with
  | .ret _ => s.kont = []
  | .trap _ => True
  | _ => False

/-- Structural only: no call to step and no speculative heap work. -/
def isStopped (s : State) : Bool :=
  match s.control with
  | .ret _ => s.kont.isEmpty
  | .trap _ | .invalid => true
  | _ => false

end ANL.Words.Mir
