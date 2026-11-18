import ANL.WordsReferenceOutput
import ANL.MemoryReferenceIO

namespace ANL.Words.Reference.IOBoundary

structure Arguments where
  corePath : String
  planPath : String
  fuel : Nat
  transitions : Nat
  deriving Repr

abbrev boundedNat := ANL.Memory.Reference.IOBoundary.boundedNat
abbrev validPath := ANL.Memory.Reference.IOBoundary.validPath

def arguments : List String → Except String Arguments
  | [corePath, planPath, fuelText, transitionText] => do
    if !validPath corePath || !validPath planPath then throw "invalid_path_argument"
    let fuel ← match boundedNat Tool.maxFuel fuelText with
      | none => throw "invalid_fuel_argument" | some value => pure value
    let transitions ← match boundedNat maxTransitions transitionText with
      | none => throw "invalid_transition_argument" | some value => pure value
    return ⟨corePath, planPath, fuel, transitions⟩
  | _ => .error "usage: anl_words_reference_runner CORE PLAN FUEL TRANSITIONS"

def decodeFailure (base : Report) (phase : String) (error : Wire.DecodeError) : Report :=
  match error.kind with
  | .invalid => {base with status := .rejected, reason := phase ++ "_invalid: " ++ error.message}
  | .resourceLimit => {base with status := .error, reason := phase ++ "_input_limit: " ++ error.message}

def loadCore (base : Report) (path : String) : IO (Except Report CheckedProgram) := do
  try
    match ← Wire.IOBoundary.readFile path Wire.coreByteLimit with
    | .error error => return .error (decodeFailure base "core" error)
    | .ok text =>
      match checkCore text with
      | .error error => return .error (decodeFailure base "core" error)
      | .ok checked => return .ok checked
  catch error => return .error {base with reason := "core_io_error: " ++ error.toString}

def loadPlan (base : Report) (path : String) : IO (Except Report ResponsePlan) := do
  try
    match ← Wire.IOBoundary.readFile path planByteLimit with
    | .error error => return .error (decodeFailure base "response_plan" error)
    | .ok text =>
      match readPlan text with
      | .error error => return .error (decodeFailure base "response_plan" error)
      | .ok plan => return .ok plan
  catch error => return .error {base with reason := "response_plan_io_error: " ++ error.toString}

def prepare (args : List String) : IO Report := do
  match arguments args with
  | .error reason => return {status := .error, reason}
  | .ok args =>
    let base : Report := {status := .error, budgets := some (args.fuel, args.transitions)}
    match ← loadCore base args.corePath with
    | .error error => return error
    | .ok checked =>
      let base := {base with semanticRevision := checked.program.semanticRevision, profile := some checked.program.profile}
      match ← loadPlan base args.planPath with
      | .error error => return error
      | .ok plan =>
        match execute checked plan args.fuel args.transitions with
        | .error _ => return {base with reason := "internal_start_error"}
        | .ok result => return resultReport checked.program args.fuel args.transitions result

/-- This path never writes a second stdout document after a partial write. -/
def fatal (message : String) : IO UInt32 := do
  try
    let stderr ← IO.getStderr
    stderr.write (Wire.IOBoundary.reason message).toUTF8
    stderr.flush
  catch _ => pure ()
  return 4

def writeOnce (status : Status) (bytes : ByteArray) : IO UInt32 := do
  try
    let stdout ← IO.getStdout
    stdout.write bytes
    stdout.flush
    return status.exitCode
  catch error => fatal ("output_io_error: " ++ error.toString)

def emit (report : Report) : IO UInt32 := do
  match encode report with
  | .ok bytes => writeOnce report.status bytes
  | .error error =>
    let failed := exportFailure report error
    match encode failed with
    | .ok bytes => writeOnce .error bytes
    | .error _ => fatal "output_byte_limit: error report could not be encoded"

def run (args : List String) : IO UInt32 := do
  let report ← prepare args
  emit report

end ANL.Words.Reference.IOBoundary
