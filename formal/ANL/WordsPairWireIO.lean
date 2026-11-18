import ANL.WordsPairWireSafety
import ANL.WordsWireIOCommon

namespace ANL.Words.Wire.IOBoundary
open Lean

inductive Status where
  | accepted | rejected | resourceLimit | error
  deriving Repr

def Status.name : Status → String
  | .accepted => "accepted" | .rejected => "rejected"
  | .resourceLimit => "resource_limit" | .error => "error"
def Status.exitCode : Status → UInt32
  | .accepted => 0 | .rejected => 1 | .resourceLimit => 3 | .error => 4

def report (status : Status) (profile : Option Profile) (message : String) : Json :=
  Json.mkObj [("schema", toJson "anl-words-pair-check-v1"),
    ("status", toJson status.name), ("semantic_revision", toJson "anl-words-v1"),
    ("allocation_profile", match status, profile with
      | .accepted, some p => profileJson p | _, _ => .null),
    ("reason", toJson (match status with | .accepted => "" | _ => reason message))]

def emit (status : Status) (profile : Option Profile := none) (message : String := "") : IO UInt32 := do
  writeOnce status.exitCode ((report status profile message).compress ++ "\n").toUTF8

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
  | _ => emit .error none "usage: anl_words_pair_checker CORE MIR"


end ANL.Words.Wire.IOBoundary
