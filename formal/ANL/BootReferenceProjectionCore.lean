import ANL.BootReferenceInputBounds
import ANL.BootSessionExecutedBounds

namespace ANL.Boot.Reference.Projection
open ANL.Words ANL.Boot.Runtime ANL.Boot.Runtime.Session

inductive Value where
  | unit | byte (value : Nat)
  deriving DecidableEq, Repr

inductive ValueOf : Words.Val → Value → Prop where
  | unit : ValueOf unitValue .unit
  | byte : WordAt .w8 n value → ValueOf value (.byte n)

inductive ArgumentsOf : Operation → List Words.Val → List Value → Prop where
  | empty : op.params = [] → ArgumentsOf op [] []
  | write : WordAt .w8 n value → ArgumentsOf (.write8 region offset) [value] [.byte n]

structure PendingView where
  ordinal : Nat
  declaration : Nat
  operation : Operation
  arguments : List Value
  origin : Origin.Location
  deriving DecidableEq, Repr

structure PendingOf (raw : Pending) (view : PendingView) : Prop where
  ordinal : view.ordinal = raw.ordinal
  declaration : view.declaration = raw.declaration
  operation : view.operation = raw.operation
  arguments : ArgumentsOf raw.operation raw.arguments view.arguments
  origin : view.origin = raw.origin

inductive PhaseView where
  | ordinary
  | before (pending : PendingView)
  | commit (pending : PendingView)
  | after (pending : PendingView) (value : Value)
  | finish (pending : PendingView) (value : Value)
  | parkCheck (origin : Origin.Location)
  | parkObserved (origin : Origin.Location)
  deriving DecidableEq, Repr

inductive PhaseOf : Phase → PhaseView → Prop where
  | ordinary : PhaseOf .ordinary .ordinary
  | before : PendingOf q view → PhaseOf (.primitiveBefore q) (.before view)
  | commit : PendingOf q view → PhaseOf (.primitiveCommit q) (.commit view)
  | after : PendingOf q view → ValueOf value result → PhaseOf (.primitiveAfter q value) (.after view result)
  | finish : PendingOf q view → ValueOf value result → PhaseOf (.primitiveReturn q value) (.finish view result)
  | parkCheck : PhaseOf (.parkCheck origin) (.parkCheck origin)
  | parkObserved : PhaseOf (.parkObserved origin) (.parkObserved origin)

structure SnapshotView where
  episode : Episode
  stackRole : StackRole
  origin : Origin.Location
  phase : PhaseView
  deriving DecidableEq, Repr

structure SnapshotOf (raw : Interrupted) (view : SnapshotView) : Prop where
  episode : view.episode = raw.episode
  stackRole : view.stackRole = raw.stackRole
  origin : view.origin = raw.origins.control
  phase : PhaseOf raw.phase view.phase

inductive OptionalSnapshotOf : Option Interrupted → Option SnapshotView → Prop where
  | absent : OptionalSnapshotOf none none
  | present : SnapshotOf raw view → OptionalSnapshotOf (some raw) (some view)

structure FinalView where
  episode : Episode
  stackRole : StackRole
  origin : Origin.Location
  phase : PhaseView
  hardware : Hardware
  readCursor : Nat
  nextOrdinal : Nat
  deliveryUsed : Bool
  bootParkSeen : Bool
  episodeParkSeen : Bool
  interrupted : Option SnapshotView
  nextAction : Option ActionKind
  deriving DecidableEq, Repr

structure FinalOf (result : Session.Result) (view : FinalView) : Prop where
  episode : view.episode = result.state.episode
  stackRole : view.stackRole = result.state.stackRole
  origin : view.origin = result.state.origins.control
  phase : PhaseOf result.state.phase view.phase
  hardware : view.hardware = result.state.hardware
  cursor : view.readCursor = result.state.readCursor
  ordinal : view.nextOrdinal = result.state.nextOrdinal
  delivery : view.deliveryUsed = result.state.deliveryUsed
  bootSeen : view.bootParkSeen = result.state.bootParkSeen
  episodeSeen : view.episodeParkSeen = result.state.episodeParkSeen
  interrupted : OptionalSnapshotOf result.state.interrupted view.interrupted
  next : view.nextAction = result.frontier.next

structure UnusedView where
  readsTotal : Nat
  readsConsumed : Nat
  readsRemaining : List Nat
  delivery : Option Delivery
  deliveryState : DeliveryView
  deriving DecidableEq, Repr

structure UnusedOf (env : Environment) (state : Runtime.State) (view : UnusedView) : Prop where
  total : view.readsTotal = env.reads.length
  consumed : view.readsConsumed = state.readCursor
  remaining : view.readsRemaining = env.reads.drop state.readCursor
  delivery : view.delivery = env.delivery
  state : view.deliveryState = deliveryView env state

inductive Status where
  | observed | unobserved | exhausted | blockedRead | ineligibleDelivery
  | rejected | resourceLimit | error
  deriving DecidableEq, Repr

def Status.name : Status → String
  | .observed => "observed" | .unobserved => "unobserved" | .exhausted => "exhausted"
  | .blockedRead => "blocked_read" | .ineligibleDelivery => "ineligible_delivery"
  | .rejected => "rejected" | .resourceLimit => "resource_limit" | .error => "error"

def Status.exitCode : Status → Nat
  | .observed => 0 | .rejected => 1 | .resourceLimit => 3 | .error => 4 | _ => 5

/-- Only execution classifications use this reason map; input/IO errors are a later boundary. -/
def Status.executionReason : Status → String
  | .observed => "" | .unobserved => "delivery_unobserved"
  | .exhausted => "transition_budget_exhausted" | .blockedRead => "read_response_exhausted"
  | .ineligibleDelivery => "delivery_not_installed" | .rejected => "action_not_applicable"
  | .error | .resourceLimit => "internal_state_error"

/-- Structural reason mapping is separate from state-only observation inspection. -/
inductive ReasonStatus : StopReason → Status → Prop where
  | observed : ReasonStatus (.observed kind) .observed
  | unobserved : ReasonStatus (.unobserved kind) .unobserved
  | exhausted : ReasonStatus .exhausted .exhausted
  | blocked : ReasonStatus .blockedRead .blockedRead
  | ineligible : ReasonStatus .ineligibleDelivery .ineligibleDelivery
  | invalid : ReasonStatus .invalidState .error

inductive ResultStatus : Session.Result → Status → Prop where
  | done : result.ending = .done → ReasonStatus result.previous status → ResultStatus result status
  | rejected : result.ending = .rejected index → ResultStatus result .rejected
  | blocked : result.ending = .blocked → ResultStatus result .blockedRead
  | ineligible : result.ending = .ineligible → ResultStatus result .ineligibleDelivery
  | invalid : result.ending = .invalid → ResultStatus result .error

structure SummaryView where
  failureAction : Option Nat
  requested : Nat
  executed : Nat
  unexecuted : Nat
  totalUsed : Nat
  rows : List Row
  unused : UnusedView
  deriving Repr

/-- Existing rows are already constant-shape views; no duplicate interpreter/classifier is needed. -/
structure SummaryOf (request : Request) (result : Session.Result) (view : SummaryView) : Prop where
  failure : view.failureAction = (match result.ending with | .rejected i => some i | _ => none)
  requested : view.requested = request.actions.length
  executed : view.executed = result.rows.length
  unexecuted : view.unexecuted = request.actions.length - result.rows.length
  used : view.totalUsed = result.totalUsed
  rows : view.rows = result.rows
  unused : UnusedOf request.environment result.state view.unused

structure Identity where
  semanticRevision : String
  ordinaryRevision : String
  targetProfile : String
  deriving DecidableEq, Repr

structure IdentityOf (p : Program) (view : Identity) : Prop where
  revision : view.semanticRevision = p.semanticRevision
  ordinary : view.ordinaryRevision = p.ordinaryRevision
  profile : view.targetProfile = p.profile.id

structure TraceView where
  revEvents : List Event
  deriving DecidableEq, Repr

def TraceView.events (view : TraceView) : List Event := view.revEvents.reverse

def TraceOf (state : Runtime.State) (view : TraceView) : Prop := view.events = state.events

/-- A raw data-only report. None means unavailable, never an inferred zero count. -/
structure Report where
  identity : Identity
  status : Status
  reason : String
  summary : Option SummaryView
  final : Option FinalView
  trace : Option TraceView
  deriving Repr

structure ReportOf (p : Program) (request : Request) (result : Session.Result) (view : Report) : Prop where
  identity : IdentityOf p view.identity
  status : ResultStatus result view.status
  reason : view.reason = view.status.executionReason
  summary : ∃ summary, view.summary = some summary ∧ SummaryOf request result summary
  final : ∃ final, view.final = some final ∧ FinalOf result final
  trace : ∃ trace, view.trace = some trace ∧ TraceOf result.state trace

end ANL.Boot.Reference.Projection
