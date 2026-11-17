import ANL.MemoryResourceEntry
import ANL.MemoryWireSafety

namespace ANL.Memory.Reference
open Lean

abbrev maxTransitions : Nat := 262144
abbrev maxResponses : Nat := 65536
abbrev planByteLimit : Nat := 1048576
abbrev maxEvents : Nat := 65536
abbrev maxOutputBytes : Nat := 8388608

structure ResponsePlan where
  entries : Array Response
  defaultResponse : Response
  deriving Repr

def ResponsePlan.responses (plan : ResponsePlan) (ordinal : Nat) : Response :=
  plan.entries[ordinal]?.getD plan.defaultResponse

def response (j : Json) : Wire.Decode Response := do
  match ← Wire.str j with
  | "success" => return .success
  | "refused" => return .refused
  | _ => throw (Wire.invalid "unknown allocation response")

def decodeResponses (entries : Array Json) : Wire.Decode (Array Response) :=
  if entries.size ≤ maxResponses then
    (Array.mapM' response entries).map Subtype.val
  else .error (Wire.limit "response count limit")

def planDocument (j : Json) : Wire.Decode ResponsePlan := do
  Wire.fields j ["schema", "responses", "default"]
  if (← Wire.str (← Wire.field j "schema")) != "anl-memory-response-plan-v1" then
    throw (Wire.invalid "response plan schema")
  let entries ← Wire.array (← Wire.field j "responses")
  return ⟨← decodeResponses entries, ← response (← Wire.field j "default")⟩

def readPlan (text : String) : Wire.Decode ResponsePlan := do
  planDocument (← Wire.parse text planByteLimit)

/-- Evidence is introduced only at the independently checked input boundary. -/
structure CheckedProgram where
  program : Program
  wellFormed : WellFormedProgram program

def checkCore (text : String) : Wire.Decode CheckedProgram :=
  match h : Wire.checkCoreDocument text with
  | .error error => .error error
  | .ok program => .ok ⟨program, (Wire.checkCoreDocument_iff.mp h).2⟩

inductive RunError where
  | fuel | transitions
  deriving DecidableEq, Repr

/-- The only execution API requires checked input and uses the accepted resource runner. -/
def execute (checked : CheckedProgram) (plan : ResponsePlan) (fuel budget : Nat) :
    Except RunError Tool.Result :=
  if budget ≤ maxTransitions then
    match Tool.start? checked.program fuel with
    | none => .error .fuel
    | some initial => .ok (Tool.run checked.program plan.responses budget initial)
  else .error .transitions

inductive Status where
  | value | trap | resourceLimit | transitionLimit | rejected | error
  deriving DecidableEq, Repr

def Status.name : Status → String
  | .value => "value" | .trap => "trap" | .resourceLimit => "resource_limit"
  | .transitionLimit => "transition_limit" | .rejected => "rejected" | .error => "error"

def Status.exitCode : Status → UInt32
  | .value => 0 | .trap => 2 | .resourceLimit => 3
  | .transitionLimit => 5 | .rejected => 1 | .error => 4

def limitName : Tool.Limit → String
  | .depth => "depth" | .expressionFuel => "expression_fuel" | .slots => "slots"
  | .liveCells => "live_cells" | .fillFuel => "fill_fuel" | .tupleFields => "tuple_fields"

def trapName : MemoryTrap → String
  | .scalar .arithmeticOverflow => "arithmetic_overflow"
  | .scalar .divisionByZero => "division_by_zero"
  | .invalidLength => "invalid_length"
  | .indexOutOfBounds => "index_out_of_bounds"

inductive Completion where
  | value (value : APL.I64)
  | trap (kind : MemoryTrap)
  | resourceLimit (reason : Tool.Limit)
  | transitionLimit
  deriving Repr

def Completion.status : Completion → Status
  | .value _ => .value | .trap _ => .trap | .resourceLimit _ => .resourceLimit
  | .transitionLimit => .transitionLimit

def Completion.reason : Completion → String
  | .value _ | .trap _ => ""
  | .resourceLimit reason => limitName reason
  | .transitionLimit => "administrative transition budget exhausted"

/-- Defensive raw-shape classification is distinct from checked-entry safety. -/
def classify : Tool.Result → Option Completion
  | .resourceLimit reason _ => some (.resourceLimit reason)
  | .exhausted _ => some .transitionLimit
  | .completed c => match c.machine.control, c.machine.kont with
    | .ret (.scalar (.int value)), [] => some (.value value)
    | .trap kind, _ => some (.trap kind)
    | _, _ => none

structure MeterView where
  fuelRemaining : Nat
  activeSlots : Nat
  liveCells : Nat
  tupleFields : Nat
  expressionDepth : Nat
  deriving DecidableEq, Repr

def meterView (m : Tool.Meter) : MeterView :=
  ⟨m.fuel, m.slots, m.liveCells, m.tupleFields, m.depth⟩

structure Observation where
  completion : Completion
  meter : MeterView
  revEvents : List Event
  deriving Repr

def observe (result : Tool.Result) : Option Observation := do
  let completion ← classify result
  let retained := result.configuration
  return ⟨completion, meterView retained.meter, retained.machine.world.revTrace⟩

end ANL.Memory.Reference
