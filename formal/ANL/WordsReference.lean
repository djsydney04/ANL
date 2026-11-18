import ANL.WordsResourceEntry
import ANL.WordsWireSafety
import ANL.MemoryReference

namespace ANL.Words.Reference
open Lean ANL.Memory

abbrev maxTransitions := ANL.Memory.Reference.maxTransitions
abbrev maxResponses := ANL.Memory.Reference.maxResponses
abbrev planByteLimit := ANL.Memory.Reference.planByteLimit
abbrev maxEvents := ANL.Memory.Reference.maxEvents
abbrev maxOutputBytes := ANL.Memory.Reference.maxOutputBytes
abbrev ResponsePlan := ANL.Memory.Reference.ResponsePlan
abbrev ResponsePlan.responses (plan : ResponsePlan) (ordinal : Nat) : ANL.Memory.Response :=
  ANL.Memory.Reference.ResponsePlan.responses plan ordinal
abbrev response := ANL.Memory.Reference.response
abbrev decodeResponses := ANL.Memory.Reference.decodeResponses
abbrev planDocument := ANL.Memory.Reference.planDocument
abbrev readPlan := ANL.Memory.Reference.readPlan

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

def trapName : Trap → String
  | .arithmeticOverflow => "arithmetic_overflow"
  | .divisionByZero => "division_by_zero"
  | .invalidShift => "invalid_shift"
  | .invalidLength => "invalid_length"
  | .indexOutOfBounds => "index_out_of_bounds"

inductive Completion where
  | value (value : APL.I64)
  | trap (kind : Trap)
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
    | .ret (.scalar (.legacy (.int value))), [] => some (.value value)
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

end ANL.Words.Reference
