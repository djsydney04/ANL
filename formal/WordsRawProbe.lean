import ANL.WordsWireIOCommon
open Lean ANL.Words ANL.Words.Wire

def emit (valid : Bool) (message : String) (exitCode : UInt32) : IO UInt32 :=
  IOBoundary.writeOnce exitCode ((Json.mkObj [("raw_valid", toJson valid),
    ("reason", toJson (IOBoundary.reason message))]).compress ++ "\n").toUTF8

/-- Private evidence companion. It does not use the pair report protocol. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [kind, path] =>
    if kind != "core" && kind != "mir" then return 4
    try
      match ← IOBoundary.readFile path (if kind == "core" then coreByteLimit else mirByteLimit) with
      | .error e =>
        emit false e.message (if e.kind == .resourceLimit then 3 else 1)
      | .ok text =>
        let result : Decode Unit := if kind == "core" then ((checkCoreDocument text).map (fun _ => ()))
          else ((checkMirDocument text).map (fun _ => ()))
        match result with
        | .ok _ =>
          emit true "" 0
        | .error e =>
          emit false e.message (if e.kind == .resourceLimit then 3 else 1)
    catch e =>
      emit false e.toString 4
  | _ => return 4
