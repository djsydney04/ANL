import ANL.MemoryWireIO
open Lean ANL.Memory ANL.Memory.Wire

/-- Private evidence companion. It does not use the pair report protocol. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [kind, path] =>
    if kind != "core" && kind != "mir" then return 4
    try
      match ← IOBoundary.readFile path (if kind == "core" then coreByteLimit else mirByteLimit) with
      | .error e =>
        IO.println (Json.mkObj [("raw_valid", toJson false), ("reason", toJson (IOBoundary.reason e.message))]).compress
        return if e.kind == .resourceLimit then 3 else 1
      | .ok text =>
        let result : Decode Unit := if kind == "core" then ((checkCoreDocument text).map (fun _ => ()))
          else ((checkMirDocument text).map (fun _ => ()))
        match result with
        | .ok _ =>
          IO.println (Json.mkObj [("raw_valid", toJson true), ("reason", toJson "")]).compress
          return 0
        | .error e =>
          IO.println (Json.mkObj [("raw_valid", toJson false), ("reason", toJson (IOBoundary.reason e.message))]).compress
          return if e.kind == .resourceLimit then 3 else 1
    catch e =>
      IO.println (Json.mkObj [("raw_valid", toJson false), ("reason", toJson (IOBoundary.reason e.toString))]).compress
      return 4
  | _ => return 4
