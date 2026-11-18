import ANL.BootV2Check
import ANL.BootRuntimeCore

namespace ANL.Boot.V2.Fault
open ANL.Words

abbrev modulus := ANL.Word.Width.w64.modulus
abbrev Location := ANL.Boot.Origin.Location
abbrev Metadata := ANL.Boot.Origin.Metadata
abbrev Hardware := ANL.Boot.Runtime.Hardware
abbrev Episode := ANL.Boot.Runtime.Episode

/-- Closed platform response; it does not carry a caller-chosen cause or value. -/
inductive ForwardResponse where
  | forward
  deriving DecidableEq, Repr

/-- F is independent of the old optional scheduled delivery D. -/
structure Input where
  illegalSitePc : Option Nat
  forwarding : Option ForwardResponse
  deriving DecidableEq, Repr

def HasIllegal (p : Program) : Prop :=
  ∃ row ∈ p.primitives, row.operation = .illegalInstruction 0

instance (p : Program) : Decidable (HasIllegal p) := by
  unfold HasIllegal
  infer_instance

def hasIllegal (p : Program) : Bool :=
  p.primitives.any (fun row => decide (row.operation = .illegalInstruction 0))

/-- Bounds the entire emitted slot; no resumed PC or architectural length is inferred. -/
def SiteValid (p : Program) (pc : Nat) : Prop :=
  pc < modulus ∧ pc % 4 = 0 ∧ pc + 4 ≤ modulus ∧
    p.image.base ≤ pc ∧ pc + 4 ≤ p.image.base + p.image.limit

instance (p : Program) (pc : Nat) : Decidable (SiteValid p pc) := by
  unfold SiteValid
  infer_instance

structure InputValid (p : Program) (input : Input) : Prop where
  presence : input.illegalSitePc.isSome = true ↔ HasIllegal p
  site : ∀ pc, input.illegalSitePc = some pc → SiteValid p pc
  responseScope : input.forwarding.isSome = true → HasIllegal p

def checkInput (p : Program) (input : Input) : Bool :=
  (input.illegalSitePc.isSome == hasIllegal p) &&
    (match input.illegalSitePc with | none => true | some pc => decide (SiteValid p pc)) &&
    (!input.forwarding.isSome || hasIllegal p)

/-- A raw occurrence/counter identity. Validity is a separate judgment. -/
structure Request where
  ordinal : Nat
  declaration : Nat
  origin : Location
  pc : Nat
  deriving DecidableEq, Repr

/-- Passive fault snapshot. It is not a resumable old carrier invocation. -/
structure Pending where
  request : Request
  machine : ANL.Words.State
  origins : Metadata
  episode : Episode
  deriving Repr

inductive Event where
  | raised (request : Request)
  | forwarded (request : Request)
  deriving DecidableEq, Repr

def Event.scause (_ : Event) : Nat := 2
def Event.stval (_ : Event) : Nat := 0

/-- Raw intended entry payload, not an execution of a handler or an asserted reset. -/
structure HandlerTransfer where
  function : Nat
  stack : Nat
  scause : Nat
  sepc : Nat
  stval : Nat
  deriving DecidableEq, Repr

def TransferValid (p : Program) (request : Request) (transfer : HandlerTransfer) : Prop :=
  transfer.function = p.entries.hardware.function ∧ transfer.stack = p.entries.hardware.stack ∧
    transfer.scause = 2 ∧ transfer.sepc = request.pc ∧ transfer.stval = 0

/-- Local boundary checks only. Full typed/origin-stack reachability is a later invariant. -/
structure PendingValid (p : Program) (input : Input) (hardware : Hardware)
    (nextOrdinal : Nat) (pending : Pending) : Prop where
  bootEpisode : pending.episode = .boot
  ordinal : pending.request.ordinal = nextOrdinal
  positive : 0 < nextOrdinal
  site : input.illegalSitePc = some pending.request.pc
  operation : p.operationAt pending.request.declaration = some (.illegalInstruction 0)
  installed : hardware.installedHandler = some p.entries.hardware.function
  current : pending.machine.current.function = p.entries.boot.function
  sourceFunction : pending.request.origin.function = p.entries.boot.function
  origin : pending.origins.control = pending.request.origin
  invocation : pending.machine.control = .invoke pending.request.declaration none []
  occurrence : ∃ d, p.functions[p.entries.boot.function]? = some (.defined d) ∧
    ANL.Boot.Origin.At d.function.body pending.request.origin.path
      (.call unitTy pending.request.declaration [])

/-- A value-level specification of the selected status bits, not a runtime transition. -/
def forwardedStatus (status : Nat) : Nat :=
  (status &&& (modulus - 1 - 0x122)) ||| 0x100 |||
    (if status &&& 2 = 0 then 0 else 0x20)

end ANL.Boot.V2.Fault
