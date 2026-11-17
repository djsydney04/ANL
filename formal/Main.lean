import APL.Wire

open APL

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
    | _ => IO.eprintln "usage: apl_formal FILE [--fuel N]"; return 4
  let metadata ← try (System.FilePath.mk path).metadata catch e => IO.eprintln e.toString; return 4
  if metadata.byteSize > 1048576 then
    IO.println (Wire.outcome (.error .resourceLimit)).compress
    return 3
  let bytes ← try IO.FS.readBinFile path catch e => IO.eprintln e.toString; return 4
  let r := match String.fromUTF8? bytes with
    | none => .error .invalid
    | some text => match Wire.decode text with
      | .ok input => Wire.execute input fuel
      | .error message => .error (Wire.decodeError message)
  IO.println (Wire.outcome r).compress
  return match r with
    | .ok _ => 0
    | .error .invalid => 1
    | .error (.trap _) => 2
    | .error .resourceLimit => 3
