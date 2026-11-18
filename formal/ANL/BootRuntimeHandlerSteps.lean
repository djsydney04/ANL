import ANL.BootRuntimeHandlerOrbit

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}
set_option linter.unusedSimpArgs false

 theorem nine_positions (bound : position < 9) :
    position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 ∨ position = 4 ∨
    position = 5 ∨ position = 6 ∨ position = 7 ∨ position = 8 := by omega

 theorem HandlerAt.firstPark_iff (wf : WellFormedProgram p) (notBoot : s.episode ≠ .boot)
    (bound : position < 9) (point : HandlerAt p s values position) : FirstPark p s ↔ position = 1 ∨ position = 2 := by
  have selected := selected_handler wf notBoot
  rcases point with ⟨machine, origins, phase, seen⟩
  rcases nine_positions bound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [FirstPark, ParkAt, ParkControl, machine, origins, seen, handlerPoint, handler, park,
    trueTerm, emptyTerm, notBoot, selected, Origin.Location.root, Origin.Location.child] at *
  all_goals simp_all

 theorem HandlerAt.capture_none (bound : position < 9) (point : HandlerAt p s values position) : capture p s = none := by
  rcases nine_positions bound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [capture, point.1, handlerPoint]

 theorem HandlerAt.tick (wf : WellFormedProgram p) (notBoot : s.episode ≠ .boot)
    (bound : position < 9) (point : HandlerAt p s values position) :
    tickRaw p env s = .advance (handlerAdvance p s values position) := by
  have first := point.firstPark_iff wf notBoot bound
  have noCapture := point.capture_none bound
  have selected := selected_handler wf notBoot
  rcases point with ⟨machine, origins, phase, seen⟩
  rcases nine_positions bound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tickRaw, command, execute, phase, machine, origins, seen, first, noCapture,
    handlerAdvance, handlerSuccessor, handlerPoint, handler, park, trueTerm, emptyTerm,
    Origin.step, Origin.checkAdmitted, Origin.Admitted, Words.step, Origin.advance,
    Origin.action, Origin.applyAction, ordinaryState, withPhase, observedPark,
    ParkWaiting, ParkConsumed, ParkAt, ParkControl, notBoot, selected,
    Origin.Location.root, Origin.Location.child] at *
  all_goals simp_all

 theorem handler_step_exact (wf : WellFormedProgram p) (notBoot : s.episode ≠ .boot)
    (orbit : HandlerOrbit p s) (step : BootStep p env s next) :
    ∃ values position, position < 9 ∧ next = handlerAdvance p s values position := by
  obtain ⟨values, position, bound, point⟩ := orbit notBoot
  have actual := tickRaw_step_iff.mpr step
  have expected := point.tick wf notBoot bound (env := env)
  exact ⟨values, position, bound, TickResult.advance.inj (actual.symm.trans expected)⟩

 theorem handler_retains (wf : WellFormedProgram p) (notBoot : s.episode ≠ .boot)
    (orbit : HandlerOrbit p s) (step : BootStep p env s next) :
    next.episode = s.episode ∧ next.revEvents = s.revEvents ∧ next.hardware = s.hardware ∧
    next.readCursor = s.readCursor ∧ next.nextOrdinal = s.nextOrdinal ∧
    next.deliveryUsed = s.deliveryUsed ∧ next.interrupted = s.interrupted ∧
    next.bootParkSeen = s.bootParkSeen ∧ next.stackRole = s.stackRole := by
  obtain ⟨values, position, _, rfl⟩ := handler_step_exact wf notBoot orbit step
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

 theorem handler_preserved (wf : WellFormedProgram p) (notBoot : s.episode ≠ .boot)
    (orbit : HandlerOrbit p s) (step : BootStep p env s next) : HandlerOrbit p next := by
  obtain ⟨values, position, bound, rfl⟩ := handler_step_exact wf notBoot orbit step
  exact handlerAdvance_orbit bound

 theorem HandlerAt.not_trap (bound : position < 9) (point : HandlerAt p s values position) : s.machine.control ≠ .trap kind := by
  rcases nine_positions bound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [point.1, handlerPoint]

 theorem HandlerAt.not_invoke (bound : position < 9) (point : HandlerAt p s values position) : s.machine.control ≠ .invoke ident loan args := by
  rcases nine_positions bound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [point.1, handlerPoint]

 theorem BootStep.handler_orbit (wf : WellFormedProgram p) (old : LocalSafety p env s)
    (orbit : HandlerOrbit p s) (step : BootStep p env s next) : HandlerOrbit p next := by
  by_cases boot : s.episode = .boot
  · cases step with | advance ready execution =>
     cases execution with
     | language reset => exact reset.handler_orbit wf old.runtime.memory.1
     | before cut | after cut | parkBoot _ cut =>
       cases cut with
       | absent => intro notBoot; exact False.elim (notBoot boot)
       | deliver _ _ reset => exact reset.handler_orbit wf old.runtime.memory.1
     | enterPark | captured | ordinary | commit | finish | parkHandler | parkResume =>
       intro notBoot
       exact False.elim (notBoot boot)
  · exact handler_preserved wf boot orbit step

end ANL.Boot.Runtime
