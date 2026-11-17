import APL.FlatProductsWire

open APL

private def finish (r : Except Program.Error FlatProducts.Val) : IO UInt32 := do
  IO.println (FlatProductsWire.outcome r).compress
  return match r with
    | .ok _ => 0
    | .error .invalid => 1
    | .error (.trap _) => 2
    | .error .resourceLimit => 3

def main (args : List String) : IO UInt32 := do
  let (path, fuel, revisionOnly) ← match args with
    | [path] => pure (path, 100000, false)
    | [path, "--revision"] => pure (path, 100000, true)
    | [path, "--fuel", n] => match n.toNat? with
      | some fuel =>
        if fuel > 1000000000 || n.isEmpty || !n.toList.all Wire.asciiDigit then
          IO.eprintln "fuel must be a decimal integer in 0..1000000000"
          return 4
        pure (path, fuel, false)
      | none => IO.eprintln "invalid fuel"; return 4
    | _ => IO.eprintln "usage: apl_formal_v2 FILE [--fuel N | --revision]"; return 4
  let metadata ← try (System.FilePath.mk path).metadata catch e => IO.eprintln e.toString; return 4
  if metadata.byteSize > 1048576 then return ← finish (.error .resourceLimit)
  let bytes ← try IO.FS.readBinFile path catch e => IO.eprintln e.toString; return 4
  let decoded : Except String FlatProductsWire.Input := match String.fromUTF8? bytes with
    | none => .error "invalid UTF-8"
    | some text => FlatProductsWire.decode text
  match decoded with
  | .error message => finish (.error (Wire.decodeError message))
  | .ok input =>
    if revisionOnly then
      IO.println (FlatProductsWire.semanticRevision input)
      return 0
    finish (FlatProductsWire.execute input fuel)
