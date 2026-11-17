import APL.Wire
import APL.LocalStateWire

open APL

def executeText (text : String) (fuel : Nat) : Except Program.Error Val :=
  let decoded : Except String (Sum Wire.Input LocalStateWire.Input) := do
    if text.utf8ByteSize > 1048576 then throw "input file size limit"
    Wire.lexicalCheck text.toList
    let document ← Lean.Json.parse text
    let schema ← (← Wire.field document "schema").getStr?
    if schema == "apl-core-v1" || schema == "apl-expr-v1" then
      return .inr (← LocalStateWire.document document)
    else
      return .inl (← Wire.document document)
  match decoded with
  | .ok (.inl input) => Wire.execute input fuel
  | .ok (.inr input) => LocalStateWire.execute input fuel
  | .error message => .error (Wire.decodeError message)

def main (args : List String) : IO UInt32 := do
  let (path, fuel) ← match args with
    | [path] => pure (path, 100000)
    | [path, "--fuel", n] => match n.toNat? with
      | some fuel =>
        if fuel > 1000000000 || n.isEmpty || !n.toList.all Wire.asciiDigit then
          IO.eprintln "fuel must be a decimal integer in 0..1000000000"
          return 4
        pure (path, fuel)
      | none => IO.eprintln "invalid fuel"; return 4
    | _ => IO.eprintln "usage: anl_formal FILE [--fuel N]"; return 4
  let metadata ← try (System.FilePath.mk path).metadata catch e => IO.eprintln e.toString; return 4
  if metadata.byteSize > 1048576 then
    IO.println (Wire.outcome (.error .resourceLimit)).compress
    return 3
  let bytes ← try IO.FS.readBinFile path catch e => IO.eprintln e.toString; return 4
  let r := match String.fromUTF8? bytes with
    | none => .error .invalid
    | some text => executeText text fuel
  IO.println (Wire.outcome r).compress
  return match r with
    | .ok _ => 0
    | .error .invalid => 1
    | .error (.trap _) => 2
    | .error .resourceLimit => 3
