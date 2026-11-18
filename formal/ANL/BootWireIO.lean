import ANL.BootWire
import ANL.MemoryWireIO

namespace ANL.Boot.Wire.IOBoundary
open Lean

abbrev reason := ANL.Memory.Wire.IOBoundary.reason
abbrev readFile := ANL.Memory.Wire.IOBoundary.readFile

def fatal (message : String) : IO UInt32 := do
  try
    let stderr ← IO.getStderr
    stderr.write (reason message).toUTF8
    stderr.flush
  catch _ => pure ()
  return 4

/-- A failed/partial stdout write is never followed by a second JSON report. -/
def writeOnce (exitCode : UInt32) (bytes : ByteArray) : IO UInt32 := do
  try
    let stdout ← IO.getStdout
    stdout.write bytes
    stdout.flush
    return exitCode
  catch error => fatal ("output_io_error: " ++ error.toString)

def emit (valid : Bool) (message : String) (exitCode : UInt32) : IO UInt32 :=
  writeOnce exitCode ((Json.mkObj [
    ("raw_valid", toJson valid), ("reason", toJson (reason message))]).compress ++ "\n").toUTF8

def rejected (error : DecodeError) : IO UInt32 :=
  emit false error.message (match error.kind with | .invalid => 1 | .resourceLimit => 3)

def run (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    try
      match ← readFile path coreByteLimit with
      | .error error => rejected error
      | .ok text =>
        match checkCoreDocument text with
        | .ok _ => emit true "" 0
        | .error error => rejected error
    catch error => emit false error.toString 4
  | _ => emit false "usage: anl_boot_raw_probe CORE_PATH" 4

end ANL.Boot.Wire.IOBoundary
