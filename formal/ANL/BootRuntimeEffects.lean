import ANL.BootRuntimeEntryProofs

namespace ANL.Boot.Runtime
open ANL.Words

instance : Decidable (Operation.Valid hardware op) :=
  decidable_of_iff (checkOperation hardware op = true) checkOperation_iff

abbrev unitValue : Val := .scalar (.legacy .unit)

def byteOperand : Val → Option Nat
  | .scalar (.word ⟨⟨.w8, n⟩, _⟩) => some n
  | _ => none

/-- Exact finite-word clear; CSR writes separately use Euclidean truncation. -/
def clear64 (n mask : Nat) : Nat := n &&& (wordModulus - 1 - mask)
def write64 (n : Nat) : Nat := n % wordModulus

structure EffectResult where
  hardware : Hardware
  cursor : Nat
  value : Val
  payload : Payload
  deriving DecidableEq, Repr

/-- Operation meaning before the independent profile-validity guard. -/
inductive OperationEffect (env : Environment) (h : Hardware) (cursor : Nat) :
    Operation → List Val → EffectResult → Prop where
  | read : env.reads[cursor]? = some n → WordAt .w8 n value →
      OperationEffect env h cursor (.read8 region offset) [] ⟨h, cursor + 1, value, .read n⟩
  | write : WordAt .w8 n value →
      OperationEffect env h cursor (.write8 region offset) [value] ⟨h, cursor, unitValue, .write n⟩
  | fence : OperationEffect env h cursor (.fence region) [] ⟨h, cursor, unitValue, .unit⟩
  | clear : OperationEffect env h cursor (.csrClear authority register mask) []
      ⟨{ h with sstatus := clear64 h.sstatus mask }, cursor, unitValue, .unit⟩
  | set : OperationEffect env h cursor (.csrWrite authority register value) []
      ⟨{ h with sie := write64 value }, cursor, unitValue, .unit⟩
  | install : OperationEffect env h cursor (.installTrap authority target) []
      ⟨{ h with installedHandler := some target }, cursor, unitValue, .unit⟩

structure Effect (p : Program) (env : Environment) (h : Hardware) (cursor : Nat)
    (op : Operation) (args : List Val) (result : EffectResult) : Prop where
  hardware : h.Valid
  operation : op.Valid p.entries.hardware.function
  effect : OperationEffect env h cursor op args result

def operationEffect (env : Environment) (h : Hardware) (cursor : Nat) :
    Operation → List Val → Option EffectResult
  | .read8 _ _, [] => do
      let n ← env.reads[cursor]?
      let value ← wordValue .w8 n
      return ⟨h, cursor + 1, value, .read n⟩
  | .write8 _ _, [value] => do
      let n ← byteOperand value
      return ⟨h, cursor, unitValue, .write n⟩
  | .fence _, [] => some ⟨h, cursor, unitValue, .unit⟩
  | .csrClear _ _ mask, [] => some ⟨{ h with sstatus := clear64 h.sstatus mask }, cursor, unitValue, .unit⟩
  | .csrWrite _ _ value, [] => some ⟨{ h with sie := write64 value }, cursor, unitValue, .unit⟩
  | .installTrap _ handler, [] => some ⟨{ h with installedHandler := some handler }, cursor, unitValue, .unit⟩
  | _, _ => none

def perform (p : Program) (env : Environment) (h : Hardware) (cursor : Nat)
    (op : Operation) (args : List Val) : Option EffectResult :=
  if h.Valid ∧ op.Valid p.entries.hardware.function then operationEffect env h cursor op args else none

/-- Read exhaustion is distinct from malformed operands, hardware, or operations. -/
def ReadBlocked (_p : Program) (env : Environment) (h : Hardware) (cursor : Nat)
    (op : Operation) (args : List Val) : Prop :=
  h.Valid ∧ op = .read8 0 5 ∧ args = [] ∧ env.reads[cursor]? = none

instance : Decidable (ReadBlocked p env h cursor op args) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Exactly one success event and one ordinal advancement; retained pending k does not change. -/
def commitState (s : State) (pending : Pending) (result : EffectResult) : State :=
  { s with
    hardware := result.hardware, readCursor := result.cursor, nextOrdinal := s.nextOrdinal + 1,
    revEvents := .primitive pending.ordinal pending.declaration pending.operation result.payload :: s.revEvents,
    phase := .primitiveAfter pending result.value }

end ANL.Boot.Runtime
