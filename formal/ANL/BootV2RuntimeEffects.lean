import ANL.BootV2RuntimeEntry
import ANL.BootRuntimeEffectProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Hardware EffectResult OperationEffect operationEffect Pending)

/-- The operation engine is shared; this guard names the actual V2 hardware role. -/
structure LegacyEffect (p : Program) (env : Environment) (h : Hardware) (cursor : Nat)
    (op : ANL.Boot.Operation) (args : List Val) (result : EffectResult) : Prop where
  hardware : h.Valid
  operation : op.Valid p.entries.hardware.function
  effect : OperationEffect env.legacy h cursor op args result

def performLegacy (p : Program) (env : Environment) (hardware : Hardware) (cursor : Nat)
    (operation : ANL.Boot.Operation) (arguments : List Val) : Option EffectResult :=
  if hardware.Valid ∧ operation.Valid p.entries.hardware.function then
    operationEffect env.legacy hardware cursor operation arguments
  else none

/-- Missing data at the supplied cursor, with valid hardware/read selectors and empty arguments. -/
def LegacyReadBlocked (_p : Program) (env : Environment) (hardware : Hardware) (cursor : Nat)
    (operation : ANL.Boot.Operation) (arguments : List Val) : Prop :=
  hardware.Valid ∧ operation = .read8 0 5 ∧ arguments = [] ∧ env.legacy.reads[cursor]? = none

instance : Decidable (LegacyReadBlocked p env hardware cursor operation arguments) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- This raw update is used only with a separately validated legacy pending call. -/
def commitLegacyState (s : State) (pending : Pending) (result : EffectResult) : State :=
  { s with
    hardware := result.hardware, readCursor := result.cursor, nextOrdinal := s.nextOrdinal + 1,
    revEvents := .legacy (.primitive pending.ordinal pending.declaration pending.operation result.payload) :: s.revEvents,
    phase := .legacy (.primitiveAfter pending result.value) }

end ANL.Boot.V2.Runtime
