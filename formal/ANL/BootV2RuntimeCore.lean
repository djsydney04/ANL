import ANL.BootV2OriginProofs
import ANL.BootV2FaultAPI

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Hardware Episode StackRole)

/-- Raw legacy input and the separate closed forwarding input retain no proof. -/
structure Environment where
  legacy : ANL.Boot.Runtime.Environment
  fault : Fault.Input
  deriving DecidableEq, Repr

inductive Phase where
  | legacy (phase : ANL.Boot.Runtime.Phase)
  | faultBefore (request : Fault.Request)
  | faultCommit (request : Fault.Request)
  | faultPending (request : Fault.Request)
  deriving DecidableEq, Repr

inductive Event where
  | legacy (event : ANL.Boot.Runtime.Event)
  | fault (event : Fault.Event)
  deriving DecidableEq, Repr

/-- Passive inspection data; no continuation or resume operation is provided. -/
structure Interrupted where
  machine : Words.State
  origins : ANL.Boot.Origin.Metadata
  phase : Phase
  episode : Episode
  stackRole : StackRole
  deriving Repr

structure State where
  machine : Words.State
  origins : ANL.Boot.Origin.Metadata
  phase : Phase
  hardware : Hardware
  episode : Episode
  stackRole : StackRole
  readCursor : Nat
  nextOrdinal : Nat
  revEvents : List Event
  deliveryUsed : Bool
  forwardingUsed : Bool
  bootParkSeen : Bool
  episodeParkSeen : Bool
  interrupted : Option Interrupted
  deriving Repr

/-- Ordered export only. Later transitions cons to revEvents without traversing it. -/
def State.events (s : State) : List Event := s.revEvents.reverse

def State.snapshot (s : State) : Interrupted :=
  ⟨s.machine, s.origins, s.phase, s.episode, s.stackRole⟩

/-- A checking view of the active machine, not a second stored active machine. -/
def State.pendingView (s : State) (request : Fault.Request) : Fault.Pending :=
  ⟨request, s.machine, s.origins, s.episode⟩

theorem State.pendingView_machine (s : State) (request : Fault.Request) :
    (s.pendingView request).machine = s.machine := rfl

theorem State.snapshot_phase (s : State) : s.snapshot.phase = s.phase := rfl

end ANL.Boot.V2.Runtime
