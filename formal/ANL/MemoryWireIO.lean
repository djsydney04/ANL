import ANL.MemoryWire

namespace ANL.Memory.Wire.IOBoundary
open Lean

def readLoop (handle : IO.FS.Handle) (limit : Nat) : Nat → ByteArray → IO ByteArray
  | 0, bytes => pure bytes
  | fuel + 1, bytes => do
    let remaining := limit + 1 - bytes.size
    if remaining == 0 then return bytes
    let chunk ← handle.read (USize.ofNat (min 65536 remaining))
    if chunk.isEmpty then return bytes
    readLoop handle limit fuel (bytes ++ chunk)

/-- At most limit+1 bytes are read, before allocating a String. I/O exceptions propagate. -/
def readFile (path : System.FilePath) (limit : Nat) : IO (Decode String) := do
  IO.FS.withFile path .read fun handle => do
    let bytes ← readLoop handle limit (limit + 1) ByteArray.empty
    if bytes.size > limit then return .error (Wire.limit "raw byte limit")
    match String.fromUTF8? bytes with
    | none => return .error (invalid "input is not valid UTF-8")
    | some text => return .ok text

def truncateChars : List Char → Nat → List Char
  | [], _ => []
  | c :: cs, remaining =>
    if c.utf8Size ≤ remaining then c :: truncateChars cs (remaining - c.utf8Size) else []

def reason (text : String) : String := String.ofList (truncateChars text.toList 1024)

def profileJson (p : Profile) : Json := Json.mkObj [
  ("abi", toJson p.abi), ("char_bits", toJson p.charBits),
  ("i64_bytes", toJson p.i64Bytes), ("i64_align", toJson p.i64Align),
  ("size_bits", toJson p.sizeBits), ("ptrdiff_bits", toJson p.ptrdiffBits)]

inductive Status where
  | accepted | rejected | resourceLimit | error
  deriving Repr

def Status.name : Status → String
  | .accepted => "accepted" | .rejected => "rejected"
  | .resourceLimit => "resource_limit" | .error => "error"
def Status.exitCode : Status → UInt32
  | .accepted => 0 | .rejected => 1 | .resourceLimit => 3 | .error => 4

def report (status : Status) (profile : Option Profile) (message : String) : Json :=
  Json.mkObj [("schema", toJson "anl-memory-pair-check-v1"),
    ("status", toJson status.name), ("semantic_revision", toJson "anl-owned-buffers-v1"),
    ("allocation_profile", match status, profile with
      | .accepted, some p => profileJson p | _, _ => .null),
    ("reason", toJson (match status with | .accepted => "" | _ => reason message))]

def emit (status : Status) (profile : Option Profile := none) (message : String := "") : IO UInt32 := do
  IO.println (report status profile message).compress
  return status.exitCode

def rejected (e : DecodeError) : IO UInt32 :=
  emit (match e.kind with | .invalid => .rejected | .resourceLimit => .resourceLimit) none e.message

def runPair (args : List String) : IO UInt32 := do
  match args with
  | [corePath, mirPath] =>
    try
      match ← readFile corePath coreByteLimit with
      | .error e => rejected e
      | .ok ct =>
        match ← readFile mirPath mirByteLimit with
        | .error e => rejected e
        | .ok mt =>
          match checkDocuments ct mt with
          | .error e => rejected e
          | .ok (c, _) => emit .accepted (some c.profile)
    catch e => emit .error none e.toString
  | _ => emit .error none "usage: anl_memory_pair_checker CORE MIR"

end ANL.Memory.Wire.IOBoundary
