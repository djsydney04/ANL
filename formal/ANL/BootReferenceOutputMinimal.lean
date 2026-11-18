import ANL.BootReferenceOutput

namespace ANL.Boot.Reference.Output

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
 theorem minimal_bound (known : Bool) (reason : MinimalReason) : (minimalBytes known reason).size ≤ outputLimit := by
  cases known <;> cases reason <;> decide


end ANL.Boot.Reference.Output
