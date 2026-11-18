import ANL.BootReferenceOutput
import ANL.BootReferenceUtf8

namespace ANL.Boot.Reference.Output

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
 theorem minimal_bound (known : Bool) (reason : MinimalReason) : (minimalBytes known reason).size ≤ outputLimit := by
  simp only [minimalBytes, ByteArray.size_push]
  cases known <;> cases reason
  all_goals
    change (String.ofList _).utf8ByteSize + 1 ≤ outputLimit
    rw [Text.ofList_bytes]
    decide +kernel

end ANL.Boot.Reference.Output
