import ANL.BootV3Carrier
import ANL.BootV2RuntimeFaultLaws

namespace ANL.Boot.V3.Runtime

open ANL.Words

variable {p : Program} {old next : V2.Runtime.State} {env : V2.Runtime.Environment}
  {request : V2.Fault.Request}

private theorem root_typed {d : Defined} {function : Nat} {values : Env}
    (wf : WellFormedProgram p)
    (found : p.functions[function]? = some (.defined d))
    (environment : EnvTyped values d.function.valueContext) :
    ANL.Words.State.Typed p.carrier
      (ANL.Boot.Origin.rootState function d.function.body values) d.function.result := by
  apply typed_eval (Γ := d.function.valueContext)
  · simpa [resourceModes] using V2.carrier_typing (wf.at found).typed
  · exact environment
  · exact .nil
  · exact .nil
  · exact ANL.Memory.World.initial_valid (carrier_wellFormed wf).profile

theorem enter_typed {function : Nat} {arguments : List Val} {world : ANL.Memory.World}
    {machine : ANL.Words.State} {parameterTypes : List Ty}
    (wf : WellFormedProgram p)
    (entered : V2.Runtime.Enter p function arguments world machine)
    (role : V2.RoleValid p function parameterTypes)
    (argumentTypes : arguments.map Val.type = parameterTypes)
    (initialWorld : world = ANL.Memory.World.initial) :
    ANL.Words.State.Typed p.carrier machine unitTy ∧
      V2.Origin.Aligned p machine (ANL.Boot.Origin.rootMetadata function) ∧
      ANL.Boot.Runtime.MemoryFreeState machine := by
  refine ⟨?_, entered.aligned, ?_⟩
  · subst world
    cases entered with | defined found =>
      cases role with | intro actual view params result =>
        have same := Option.some.inj (found.symm.trans actual)
        cases same
        have typed := root_typed wf found (values := arguments.reverse) (by
          simp [EnvTyped, Function.valueContext, immutable, argumentTypes, params,
            Function.comp_def])
        simpa [ANL.Boot.Origin.rootState, result] using typed
  · cases entered
    exact ⟨initialWorld, rfl, by simp⟩

theorem start_checked (wf : WellFormedProgram p) (input : V2.Runtime.ValidatedInput p) :
    ∃ next, V2.Runtime.start p input = some next ∧
      ANL.Words.State.Typed p.carrier next.machine unitTy ∧
      V2.Origin.Aligned p next.machine next.origins ∧
      ANL.Boot.Runtime.MemoryFreeState next.machine := by
  obtain ⟨hart, hh⟩ := V2.Runtime.word_value_exists (width := .w64) input.valid.hart
  obtain ⟨dtb, hd⟩ := V2.Runtime.word_value_exists (width := .w64) input.valid.opaqueDtb
  obtain ⟨machine, entered⟩ :=
    V2.Runtime.role_enter_exists wf.roles.boot [hart, dtb] .initial
  refine ⟨V2.Runtime.startState input.raw machine p.entries.boot.function, ?_, ?_⟩
  · exact V2.Runtime.startRaw_iff.mpr (.boot hh hd entered)
  · exact enter_typed wf entered wf.roles.boot (by simp [hh.type, hd.type, wordTy]) rfl

theorem hardware_reset_typed {delivery : ANL.Boot.Runtime.Delivery}
    (wf : WellFormedProgram p)
    (initialWorld : old.machine.world = ANL.Memory.World.initial)
    (reset : V2.Runtime.HardwareReset p old delivery next) :
    ANL.Words.State.Typed p.carrier next.machine unitTy ∧
      V2.Origin.Aligned p next.machine next.origins ∧
      ANL.Boot.Runtime.MemoryFreeState next.machine := by
  cases reset with
  | handler hc hp ha entered =>
    exact enter_typed wf entered wf.roles.hardware
      (by simp [hc.type, hp.type, ha.type, wordTy]) initialWorld

theorem language_reset_typed {tag : Nat}
    (wf : WellFormedProgram p)
    (initialWorld : old.machine.world = ANL.Memory.World.initial)
    (reset : V2.Runtime.LanguageReset p old tag next) :
    ANL.Words.State.Typed p.carrier next.machine unitTy ∧
      V2.Origin.Aligned p next.machine next.origins ∧
      ANL.Boot.Runtime.MemoryFreeState next.machine := by
  cases reset with
  | handler hv entered =>
    exact enter_typed wf entered wf.roles.language (by simp [hv.type, byteTy]) initialWorld

theorem forward_reset_typed (wf : WellFormedProgram p)
    (initialWorld : old.machine.world = ANL.Memory.World.initial)
    (reset : V2.Runtime.ForwardReset p env old request next) :
    ANL.Words.State.Typed p.carrier next.machine unitTy ∧
      V2.Origin.Aligned p next.machine next.origins ∧
      ANL.Boot.Runtime.MemoryFreeState next.machine := by
  cases reset with
  | handler _ _ _ hc hp ha entered =>
    exact enter_typed wf entered wf.roles.hardware
      (by simp [hc.type, hp.type, ha.type, wordTy]) initialWorld

theorem forwarding_checked (wf : WellFormedProgram p) (input : V2.Runtime.InputValid p env)
    (initialWorld : old.machine.world = ANL.Memory.World.initial)
    (phase : old.phase = .faultPending request)
    (valid : V2.Runtime.FaultRaisedValid p env old request)
    (response : env.fault.forwarding = some .forward) :
    ∃ next, V2.Runtime.resetForward p env old request = some next ∧
      ANL.Words.State.Typed p.carrier next.machine unitTy ∧
      V2.Origin.Aligned p next.machine next.origins ∧
      ANL.Boot.Runtime.MemoryFreeState next.machine := by
  obtain ⟨cause, hc⟩ := V2.Runtime.word_value_exists (width := .w64) (n := 2) (by decide)
  obtain ⟨pc, hp⟩ :=
    V2.Runtime.word_value_exists (width := .w64) (valid.1.site_valid input).1
  obtain ⟨auxiliary, ha⟩ := V2.Runtime.word_value_exists (width := .w64) (n := 0) (by decide)
  obtain ⟨machine, entered⟩ :=
    V2.Runtime.role_enter_exists wf.roles.hardware [cause, pc, auxiliary] old.machine.world
  have reset : V2.Runtime.ForwardReset p env old request
      (V2.Runtime.forwardResetState p old request machine) :=
    .handler phase valid response hc hp ha entered
  exact ⟨_, V2.Runtime.resetForward_iff.mpr reset, forward_reset_typed wf initialWorld reset⟩

end ANL.Boot.V3.Runtime
