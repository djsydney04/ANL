import ANL.BootV2Carrier
import ANL.BootNoReturn

namespace ANL.Boot.V2
open ANL.Words

/-- The ordinary-carrier tail theorem is reused, not a new hardware execution claim. -/
theorem WellFormedProgram.boot_carrier_no_value_terminal (valid : WellFormedProgram p)
    (found : p.functions[p.entries.boot.function]? = some (.defined d))
    (steps : Steps p.carrier responses ⟨.eval d.function.body, a, k, w⟩
      ⟨.ret value, finalActivation, [], finalWorld⟩) : False :=
  (valid.boot_nonreturning found).no_value_terminal steps

theorem WellFormedProgram.handler_carrier_no_value_terminal (valid : WellFormedProgram p)
    (role : f = p.entries.hardware.function ∨ f = p.entries.language.function)
    (found : p.functions[f]? = some (.defined d))
    (steps : Steps p.carrier responses ⟨.eval d.function.body, a, k, w⟩
      ⟨.ret value, finalActivation, [], finalWorld⟩) : False :=
  (valid.handler_nonreturning role found).no_value_terminal steps

end ANL.Boot.V2
