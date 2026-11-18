import ANL.BootV2WireAdmission
import ANL.BootWireIO

namespace ANL.Boot.V2.Wire.IOBoundary
open ANL.Boot.Wire.IOBoundary (readFile emit rejected)

def run (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    try
      match ← readFile path coreByteLimit with
      | .error error => rejected error
      | .ok text =>
        match Admission.checkProbeDocument text with
        | .ok _ => emit true "" 0
        | .error error => rejected error
    catch error => emit false error.toString 4
  | _ => emit false "usage: anl_boot_v2_raw_probe CORE_PATH" 4

end ANL.Boot.V2.Wire.IOBoundary
