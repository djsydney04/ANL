import ANL.BootRuntimeSelectedSpin

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}

def installCount : List Event → Nat
  | [] => 0
  | .primitive _ _ (.installTrap ..) _ :: rest => installCount rest + 1
  | _ :: rest => installCount rest

 theorem OperationEffect.no_install_count (effect : OperationEffect env hardware cursor op args result)
    (absent : result.hardware.installedHandler = none) :
    hardware.installedHandler = none ∧
      installCount (.primitive ordinal ident op result.payload :: events) = installCount events := by
  cases effect <;> simp_all [installCount]

 theorem History.no_install_count {hardware : Hardware} (history : History p env events hardware cursor ordinal episode used)
    (absent : hardware.installedHandler = none) : installCount events = 0 := by
  induction history with
  | initial => rfl
  | primitive _ _ effect ih =>
    obtain ⟨old, same⟩ := effect.effect.no_install_count (events := _) absent
    rw [same]
    exact ih old
  | language _ _ ih | hardware _ _ _ _ _ ih => exact ih absent

 theorem ineligible_cut (outcome : BootOutcome p env s (.ineligibleDelivery next)) :
    ∃ key d, DeliveryAt env s key d ∧ ¬ Eligible p s := by
  cases outcome with | ready _ execution =>
   cases execution <;> rename_i cut
   all_goals cases cut with | ineligible present denied => exact ⟨_, _, present, denied⟩

 theorem ineligible_before_install (wf : WellFormedProgram p) (safe : SafetyInvariant p env s)
    (outcome : tickRaw p env s = .ineligibleDelivery next) :
    next = s ∧ s.episode = .boot ∧ s.hardware.installedHandler = none ∧
      ∃ key d, DeliveryAt env s key d := by
  have independent := tickRaw_iff.mp outcome
  have retained := outcome_ineligible_retains independent
  obtain ⟨key, d, present, denied⟩ := ineligible_cut independent
  have boot : s.episode = .boot := by
    by_cases boot : s.episode = .boot
    · exact boot
    obtain ⟨values, position, bound, point⟩ := safe.handler boot
    have advanced := point.tick wf boot bound (env := env)
    rw [outcome] at advanced
    cases advanced
  have absent : s.hardware.installedHandler = none := by
    rcases safe.localSafety.runtime.installed with empty | installed
    · exact empty
    · exact False.elim (denied ⟨boot, installed⟩)
  exact ⟨retained, boot, absent, key, d, present⟩

 theorem ineligible_has_no_install_event (wf : WellFormedProgram p) (safe : SafetyInvariant p env s)
    (outcome : tickRaw p env s = .ineligibleDelivery next) : installCount s.revEvents = 0 :=
  safe.history.no_install_count (ineligible_before_install wf safe outcome).2.2.1

 theorem SafetyInvariant.current_defined (safe : SafetyInvariant p env s) :
    ∃ definition, p.functions[s.machine.current.function]? = some (.defined definition) :=
  safe.localSafety.runtime.aligned.current_defined

 theorem SafetyInvariant.no_primitive_body (safe : SafetyInvariant p env s) :
    p.functions[s.machine.current.function]? ≠ some (.primitive row) := by
  obtain ⟨definition, found⟩ := safe.current_defined
  simp [found]

 theorem SafetyInvariant.no_synthetic_body (safe : SafetyInvariant p env s) :
    s.machine.current.function < p.functions.length := by
  obtain ⟨definition, found⟩ := safe.current_defined
  exact (List.getElem?_eq_some_iff.mp found).1

 theorem SafetyInvariant.empty_memory (safe : SafetyInvariant p env s) :
    s.machine.world = .initial ∧ s.machine.current.resources = [] ∧
      ∀ frame ∈ s.machine.kont, FrameClean frame := safe.localSafety.runtime.memory

 theorem checked_entry_not_invalid (wf : WellFormedProgram p) (input : InputValid p env) (started : Start p env first)
    (steps : BootStepsN p env n first last) :
    last.machine.control ≠ .invalid ∧ tickRaw p env last ≠ .invalidState bad := by
  have safe := checked_entry_safety wf input started steps
  exact ⟨safe.localSafety.not_invalid, local_not_invalidState wf input safe.localSafety⟩

 theorem handler_prefix_retains (wf : WellFormedProgram p) (notBoot : s.episode ≠ .boot)
    (orbit : HandlerOrbit p s) (steps : BootStepsN p env n s last) :
    last.episode = s.episode ∧ last.revEvents = s.revEvents ∧ last.hardware = s.hardware ∧
    last.readCursor = s.readCursor ∧ last.nextOrdinal = s.nextOrdinal ∧
    last.deliveryUsed = s.deliveryUsed ∧ last.interrupted = s.interrupted := by
  induction steps with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ step _ ih =>
    have one := handler_retains wf notBoot orbit step
    have rest := ih (fun eq => notBoot (one.1.symm.trans eq)) (handler_preserved wf notBoot orbit step)
    rcases one with ⟨a, b, c, d, e, f, g, _⟩
    rcases rest with ⟨a', b', c', d', e', f', g'⟩
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d, e'.trans e, f'.trans f, g'.trans g⟩

end ANL.Boot.Runtime
