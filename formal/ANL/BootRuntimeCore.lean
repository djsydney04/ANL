import ANL.BootOriginReachable

namespace ANL.Boot.Runtime
open ANL.Words

abbrev wordModulus : Nat := ANL.Word.Width.w64.modulus
abbrev byteModulus : Nat := ANL.Word.Width.w8.modulus

inductive Landmark where
  | beforePrimitive (ordinal declaration : Nat)
  | afterPrimitive (ordinal declaration : Nat)
  | bootPark (origin : Origin.Location)
  deriving DecidableEq, Repr

structure Delivery where
  landmark : Landmark
  scause : Nat
  sepc : Nat
  stval : Nat
  deriving DecidableEq, Repr

/-- Raw input remains representable before its separate validation gateway. -/
structure Environment where
  sstatus : Nat
  sie : Nat
  hart : Nat
  opaqueDtb : Nat
  reads : List Nat
  delivery : Option Delivery
  deriving DecidableEq, Repr

/-- This is only the modeled CSR/ANL-installation state, not a UART emulator. -/
structure Hardware where
  sstatus : Nat
  sie : Nat
  installedHandler : Option Nat
  deriving DecidableEq, Repr

inductive Episode where
  | boot | hardwareHandler | languageHandler
  deriving DecidableEq, Repr

inductive StackRole where
  | boot | terminal
  deriving DecidableEq, Repr

inductive Payload where
  | unit
  | read (value : Nat)
  | write (value : Nat)
  deriving DecidableEq, Repr

inductive Event where
  | primitive (ordinal declaration : Nat) (operation : Operation) (payload : Payload)
  | language (tag : Nat)
  | hardware (landmark : Landmark) (scause sepc stval : Nat)
  deriving DecidableEq, Repr

structure Pending where
  ordinal : Nat
  declaration : Nat
  operation : Operation
  arguments : List Val
  origin : Origin.Location
  deriving DecidableEq, Repr

inductive Phase where
  | ordinary
  | primitiveBefore (pending : Pending)
  | primitiveCommit (pending : Pending)
  | primitiveAfter (pending : Pending) (value : Val)
  | primitiveReturn (pending : Pending) (value : Val)
  | parkCheck (origin : Origin.Location)
  | parkObserved (origin : Origin.Location)
  deriving DecidableEq, Repr

/-- Passive inspection data only; there is no resume operation. -/
structure Interrupted where
  machine : Words.State
  origins : Origin.Metadata
  phase : Phase
  episode : Episode
  stackRole : StackRole
  deriving Repr

structure State where
  machine : Words.State
  origins : Origin.Metadata
  phase : Phase
  hardware : Hardware
  episode : Episode
  stackRole : StackRole
  readCursor : Nat
  nextOrdinal : Nat
  revEvents : List Event
  deliveryUsed : Bool
  bootParkSeen : Bool
  episodeParkSeen : Bool
  interrupted : Option Interrupted
  deriving Repr

/-- Ordered export only; transitions cons to revEvents and never call this projection. -/
def State.events (s : State) : List Event := s.revEvents.reverse

def State.snapshot (s : State) : Interrupted :=
  ⟨s.machine, s.origins, s.phase, s.episode, s.stackRole⟩

/-- Every stopped outcome retains the input state. Unobserved delivery and budgets belong to the later runner. -/
inductive TickResult where
  | advance (state : State)
  | blockedRead (state : State)
  | ineligibleDelivery (state : State)
  | invalidState (state : State)
  deriving Repr

def TickResult.state : TickResult → State
  | .advance s | .blockedRead s | .ineligibleDelivery s | .invalidState s => s

/-- Only the three ordinary language failures have hardware-profile language tags. -/
def languageTag : Trap → Option Nat
  | .arithmeticOverflow => some 1
  | .divisionByZero => some 2
  | .invalidShift => some 3
  | .invalidLength | .indexOutOfBounds => none

inductive LanguageTag : Trap → Nat → Prop where
  | overflow : LanguageTag .arithmeticOverflow 1
  | division : LanguageTag .divisionByZero 2
  | shift : LanguageTag .invalidShift 3

def Hardware.Valid (h : Hardware) : Prop := h.sstatus < wordModulus ∧ h.sie < wordModulus
instance : Decidable (Hardware.Valid h) := inferInstanceAs (Decidable (_ ∧ _))

end ANL.Boot.Runtime
