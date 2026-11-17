import ANL.MemoryExecute
import ANL.MemoryOrigin

namespace ANL.Memory.Tool

abbrev maxDepth : Nat := 256
abbrev maxSlots : Nat := 65536
abbrev maxLiveCells : Nat := 1048576
abbrev maxTupleFields : Nat := 1048576
abbrev defaultFuel : Nat := 100000
abbrev maxFuel : Nat := 1000000000

inductive Limit where
  | depth | expressionFuel | slots | liveCells | fillFuel | tupleFields
  deriving DecidableEq, Repr

structure Meter where
  fuel : Nat
  slots : Nat
  liveCells : Nat
  tupleFields : Nat
  depth : Nat
  parents : List Nat
  deriving DecidableEq, Repr

def Meter.empty (fuel : Nat) : Meter := ⟨fuel, 0, 0, 0, 0, []⟩

structure Configuration where
  machine : State
  meter : Meter
  deriving Repr

inductive Preflight where
  | allowed (meter : Meter)
  | blocked (reason : Limit) (meter : Meter)
  deriving DecidableEq, Repr

def reserveSlots (m : Meter) (count : Nat) : Preflight :=
  if m.slots + count ≤ maxSlots then .allowed {m with slots := m.slots + count}
  else .blocked .slots m

def enter (m : Meter) : Preflight :=
  if m.depth < maxDepth then
    if 0 < m.fuel then .allowed {m with fuel := m.fuel - 1}
    else .blocked .expressionFuel m
  else .blocked .depth m

def reserveOwner (m : Meter) (length : Nat) : Preflight :=
  if m.liveCells + length ≤ maxLiveCells then
    if m.slots + 1 ≤ maxSlots then
      if length ≤ m.fuel then
        .allowed {m with liveCells := m.liveCells + length, slots := m.slots + 1, fuel := m.fuel - length}
      else .blocked .fillFuel m
    else .blocked .slots m
  else .blocked .liveCells m

def reserveTuple (m : Meter) (fields : Nat) : Preflight :=
  if m.tupleFields + fields ≤ maxTupleFields then
    .allowed {m with tupleFields := m.tupleFields + fields}
  else .blocked .tupleFields m

def preflight (p : Program) (s : State) (m : Meter) : Preflight :=
  match s.control with
  | .eval term => match enter m with
    | .blocked reason retained => .blocked reason retained
    | .allowed entered => match term with
      | .call _ _ args => reserveSlots entered args.length
      | .callView _ _ _ _ args => reserveSlots entered (args.length + 1)
      | _ => .allowed entered
  | .ret value => match s.kont with
    | .bind _ _ :: _ => reserveSlots m 1
    | .fields [] prior :: _ => match value with
      | .scalar _ => reserveTuple m (prior.length + 1)
      | _ => .allowed m
    | _ => .allowed m
  | .allocate _ length _ _ _ =>
    if length ≤ p.profile.maxCells then reserveOwner m length else .allowed m
  | _ => .allowed m

def Meter.pushChild (m : Meter) : Meter :=
  {m with depth := m.depth + 1, parents := m.depth :: m.parents}
def Meter.pushCall (m : Meter) : Meter := {m with parents := m.depth :: m.parents}
def Meter.parent (m : Meter) : Nat := m.parents.headD m.depth
def Meter.pop (m : Meter) : Meter := {m with depth := m.parent, parents := m.parents.tail}
def Meter.sibling (m : Meter) : Meter := {m with depth := m.parent + 1}
def Meter.tailChild (m : Meter) : Meter := {m with depth := m.parent + 1, parents := m.parents.tail}
def Meter.release (m : Meter) (slots cells : Nat) : Meter :=
  {m with slots := m.slots - slots, liveCells := m.liveCells - cells}

/-- Parallel frame metadata records recursive expression depth. -/
def finish (s next : State) (m : Meter) : Meter :=
  match next.control with
  | .invalid => m
  | _ => match s.control with
    | .eval term => match term with
      | .letE _ _ _ | .letMut _ _ _ | .assign _ _ _ | .whileE _ _ _
      | .ifE _ _ _ _ | .unary _ _ _ | .binary _ _ _ _ | .project _ _ _
      | .heap _ _ _ _ _ _ | .bufferRead _ _ _ | .bufferWrite _ _ _ _ => m.pushChild
      | .call _ _ args | .callView _ _ _ _ args =>
        if args.isEmpty then {m with depth := m.depth + 1} else m.pushChild
      | .tuple _ (_ :: _) => m.pushChild
      | _ => m
    | .ret _ => match s.kont with
      | .bind _ _ :: _ => m.sibling
      | .scope :: _ => (m.release 1 0).pop
      | .ifF _ _ :: _ => m.tailChild
      | .left _ _ :: _ => match next.control with
        | .eval _ => m.sibling
        | _ => m.pop
      | .arguments _ _ rest _ :: _ => if rest.isEmpty then m.tailChild else m.sibling
      | .condition _ _ :: _ => match next.control with
        | .eval _ => m.sibling
        | _ => m.pop
      | .body _ _ :: _ => m.sibling
      | .fields rest _ :: _ => if rest.isEmpty then m.pop else m.sibling
      | .callReturn _ _ :: _ | .owner _ _ :: _ => m
      | _ :: _ => m.pop
      | [] => m
    | .lengthReady _ _ _ _ _ | .writeCheck _ _ _ => match next.control with
      | .eval _ => m.pushChild
      | _ => m
    | .grant _ _ _ => m.pushCall
    | .close binding _ _ => (m.release 1 binding.length).pop
    | .restore _ => (m.release (s.current.env.length + s.current.resources.length) 0).pop
    | _ => m

/-- Tag allocation results directly; refunds never inspect or traverse the resulting heap. -/
def commit (p : Program) (responses : Responses) (s : State) (m : Meter) : Option Configuration :=
  match s.control with
  | .allocate site n init yes no =>
    match allocate p.profile responses s.world site n init with
    | (.allocated ref, w) => some ⟨
        ⟨.eval yes, {s.current with resources := ⟨.owner, ref, n⟩ :: s.current.resources},
          .owner ⟨.owner, ref, n⟩ site :: s.kont, w⟩, m.pushChild⟩
    | (.refused, w) => some ⟨⟨.eval no, s.current, s.kont, w⟩,
        {(m.release 1 n) with depth := m.depth + 1}⟩
    | (.targetRejected, w) => some ⟨⟨.eval no, s.current, s.kont, w⟩, {m with depth := m.depth + 1}⟩
  | _ => match step p responses s with
    | none => none
    | some next => some ⟨next, finish s next m⟩

inductive Tick where
  | completed (configuration : Configuration)
  | resourceLimit (reason : Limit) (configuration : Configuration)
  | advanced (configuration : Configuration)
  deriving Repr

def tick (p : Program) (responses : Responses) (c : Configuration) : Tick :=
  if isStopped c.machine then .completed c
  else match preflight p c.machine c.meter with
    | .blocked reason retained => .resourceLimit reason ⟨c.machine, retained⟩
    | .allowed charged => match commit p responses c.machine charged with
      | none => .completed ⟨c.machine, charged⟩
      | some next => .advanced next

inductive Result where
  | completed (configuration : Configuration)
  | resourceLimit (reason : Limit) (configuration : Configuration)
  | exhausted (configuration : Configuration)
  deriving Repr

def Result.configuration : Result → Configuration
  | .completed c | .resourceLimit _ c | .exhausted c => c

/-- Administrative budget is separate from expression/fill fuel; zero takes no preflight or semantic step. -/
def run (p : Program) (responses : Responses) : Nat → Configuration → Result
  | 0, c => if isStopped c.machine then .completed c else .exhausted c
  | budget + 1, c => match tick p responses c with
    | .completed last => .completed last
    | .resourceLimit reason last => .resourceLimit reason last
    | .advanced next => run p responses budget next

def initial (p : Program) (fuel : Nat := defaultFuel) : Configuration :=
  ⟨ANL.Memory.initial p, Meter.empty fuel⟩

def start? (p : Program) (fuel : Nat := defaultFuel) : Option Configuration :=
  if fuel ≤ maxFuel then some (initial p fuel) else none

/-- Host-only cleanup clears logical reservations while retaining the exact semantic prefix. -/
def unwind (c : Configuration) : Configuration :=
  {c with meter := {c.meter with slots := 0, liveCells := 0, depth := 0, parents := []}}

/-- Proof-only projection; execution updates the corresponding counter incrementally. -/
def savedSlots : List Frame → Nat
  | [] => 0
  | .callReturn caller _ :: rest => caller.env.length + caller.resources.length + savedSlots rest
  | .arguments _ loan remaining captured :: rest =>
      remaining.length + captured.length + 1 + (loanResources loan).length + savedSlots rest
  | _ :: rest => savedSlots rest

def pendingSlots : Control → Nat
  | .invoke _ loan captured | .grant _ loan captured => captured.length + (loanResources loan).length
  | _ => 0

def logicalSlots (s : State) : Nat :=
  s.current.env.length + s.current.resources.length + savedSlots s.kont + pendingSlots s.control

def Meter.Bounded (m : Meter) : Prop :=
  m.slots ≤ maxSlots ∧ m.liveCells ≤ maxLiveCells ∧ m.tupleFields ≤ maxTupleFields

def Aligned (s : State) (m : Meter) : Prop := m.parents.length = s.kont.length

def Accounted (s : State) (m : Meter) : Prop :=
  Aligned s m ∧ m.slots = logicalSlots s ∧ m.liveCells = s.world.liveCells ∧ m.Bounded

end ANL.Memory.Tool
