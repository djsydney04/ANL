import ANL.WordsWireSafety
import ANL.MemoryWireIO
namespace ANL.Words.Wire.IOBoundary
abbrev readLoop := ANL.Memory.Wire.IOBoundary.readLoop
abbrev readFile := ANL.Memory.Wire.IOBoundary.readFile
abbrev truncateChars := ANL.Memory.Wire.IOBoundary.truncateChars
abbrev reason := ANL.Memory.Wire.IOBoundary.reason
abbrev profileJson := ANL.Memory.Wire.IOBoundary.profileJson

def fatal (message : String) : IO UInt32 := do
  try
    let stderr ← IO.getStderr
    stderr.write (reason message).toUTF8
    stderr.flush
  catch _ => pure ()
  return 4

/-- A failed or partial stdout write never causes a second document attempt. -/
def writeOnce (exitCode : UInt32) (bytes : ByteArray) : IO UInt32 := do
  try
    let stdout ← IO.getStdout
    stdout.write bytes
    stdout.flush
    return exitCode
  catch error => fatal ("output_io_error: " ++ error.toString)
end ANL.Words.Wire.IOBoundary
