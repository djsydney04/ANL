import ANL.BootRuntimeRunCompleteness

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : Program} {s : State}

 theorem HandlerControl.eq (valid : HandlerControl ctl) : ctl = .eval handler := by
  cases ctl <;> try exact False.elim valid
  exact congrArg Control.eval valid

 theorem FreshHandler.shape (fresh : FreshHandler p s) :
    s.machine.control = .eval handler ∧ s.machine.kont = [] ∧ s.machine.current.resources = [] ∧
    s.origins = Origin.rootMetadata (s.episode.function p) := by
  rcases fresh with ⟨_, _, _, ctl, _, _, _, shape⟩
  refine ⟨ctl.eq, ?_⟩
  split at shape
  next snapshot kont resources frames _ =>
    refine ⟨kont, resources, ?_⟩
    change s.origins = ⟨Origin.Location.root (s.episode.function p), []⟩
    rw [← shape, ← frames]
  next impossible => exact False.elim shape

 theorem FreshHandler.point (fresh : FreshHandler p s) (world : s.machine.world = .initial) :
    HandlerAt p s s.machine.current.env 0 := by
  obtain ⟨ctl, kont, resources, origins⟩ := fresh.shape
  refine ⟨?_, origins, fresh.2.2.1, fresh.2.2.2.2.2.2.1⟩
  change s.machine = ⟨.eval handler, ⟨s.episode.function p, s.machine.current.env, []⟩, [], .initial⟩
  rw [← ctl, ← fresh.2.2.2.2.1, ← resources, ← kont, ← world]

 theorem HardwareReset.observation (wf : WellFormedProgram p) (reset : HardwareReset p s d next) :
    Observation p next (.handlerEntry .hardwareHandler) := by
  cases reset with | handler _ _ _ entered =>
   cases entered with | defined found =>
    apply Observation.handler
    simp [FreshHandler, HandlerDefinition, hardwareResetState, Episode.function,
      HandlerControl, found, wf.roles.hardwareBody _ found, Origin.rootMetadata]

 theorem LanguageReset.observation (wf : WellFormedProgram p) (reset : LanguageReset p s tag next) :
    Observation p next (.handlerEntry .languageHandler) := by
  cases reset with | handler _ entered =>
   cases entered with | defined found =>
    apply Observation.handler
    simp [FreshHandler, HandlerDefinition, languageResetState, Episode.function,
      HandlerControl, found, wf.roles.languageBody _ found, Origin.rootMetadata]

 theorem FreshHandler.advances (wf : WellFormedProgram p) (fresh : FreshHandler p s)
    (world : s.machine.world = .initial) :
    BootStep p env s (handlerAdvance p s s.machine.current.env 0) :=
  tickRaw_step_iff.mp ((fresh.point world).tick wf fresh.1 (by decide))

 theorem Observation.advances (wf : WellFormedProgram p) (safe : SafetyInvariant p env s)
    (observed : Observation p s kind) : ∃ next, BootStep p env s next := by
  cases observed with
  | handler fresh => exact ⟨_, fresh.advances wf safe.localSafety.runtime.memory.1⟩
  | park phase consumed => exact ⟨_, (observed_park_resumes phase consumed).1⟩

 theorem resume_observed_positive (wf : WellFormedProgram p) (safe : SafetyInvariant p env s)
    (observed : Observation p s kind) : ∃ next,
    BootStep p env s next ∧ resumeRaw p env (budget + 1) s = (runRaw p env budget next).bump := by
  obtain ⟨next, step⟩ := observed.advances wf safe
  exact ⟨next, step, (ResumeTo.advance step runRaw_sound).compute⟩

 theorem resume_observed_used_positive (wf : WellFormedProgram p) (safe : SafetyInvariant p env s)
    (observed : Observation p s kind) : 0 < (resumeRaw p env (budget + 1) s).used := by
  obtain ⟨_, _, eq⟩ := resume_observed_positive (budget := budget) wf safe observed
  rw [eq]
  exact Nat.zero_lt_succ _

 theorem resume_observed_stop (wf : WellFormedProgram p) (safe : SafetyInvariant p env s)
    (observed : Observation p s kind) :
    StopAt p env (resumeRaw p env (budget + 1) s).state (resumeRaw p env (budget + 1) s).reason := by
  obtain ⟨_, _, eq⟩ := resume_observed_positive (budget := budget) wf safe observed
  rw [eq]
  exact runRaw_stop

 theorem SelectedSpin.no_observation (spin : SelectedSpin p s) : ∀ kind, ¬ Observation p s kind := by
  intro kind observed
  obtain ⟨phase, seen⟩ := spin.phase
  cases observed with
  | handler fresh => have impossible := fresh.2.2.2.2.2.2.1; rw [seen] at impossible; contradiction
  | park observed _ => rw [phase] at observed; contradiction

 theorem SelectedSpin.progress (spin : SelectedSpin p s) : ∃ next, BootStep p env s next := by
  obtain ⟨location, _, a, k, w, frames, position, bound, point⟩ := spin
  exact ⟨_, tickRaw_step_iff.mp (point.tick bound)⟩

 theorem SelectedSpin.finite (spin : SelectedSpin p s) (n : Nat) :
    ∃ last, ObservationFreeStepsN p env n s last ∧ SelectedSpin p last := by
  induction n generalizing s with
  | zero => exact ⟨s, .zero, spin⟩
  | succ n ih =>
    obtain ⟨next, step⟩ := spin.progress
    obtain ⟨last, rest, lastSpin⟩ := ih (spin.step step)
    exact ⟨last, .succ spin.no_observation step rest, lastSpin⟩

 theorem SelectedSpin.run_exhausted (spin : SelectedSpin p s) :
    (runRaw p env budget s).reason = .exhausted ∧ (runRaw p env budget s).used = budget := by
  obtain ⟨last, segment, lastSpin⟩ := spin.finite (env := env) budget
  have eq := (segment.prepend (RunTo.exhausted lastSpin.no_observation)).compute
  simpa [RunResult.addUsed] using congrArg (fun r : RunResult => (r.reason, r.used)) eq

 theorem resume_park_exhausted (phase : s.phase = .parkObserved location) (valid : ParkConsumed p s location) :
    (resumeRaw p env (budget + 1) s).reason = .exhausted ∧
    (resumeRaw p env (budget + 1) s).used = budget + 1 := by
  obtain ⟨step, spinning⟩ := observed_park_resumes (env := env) phase valid
  have eq := (ResumeTo.advance step (runRaw_sound (budget := budget))).compute
  rw [eq]
  obtain ⟨reason, count⟩ := spinning.run_exhausted (env := env) (budget := budget)
  exact ⟨reason, congrArg (· + 1) count⟩

 theorem resume_park_retains (phase : s.phase = .parkObserved location) (valid : ParkConsumed p s location) :
    (resumeRaw p env (budget + 1) s).state.revEvents = s.revEvents ∧
    (resumeRaw p env (budget + 1) s).state.readCursor = s.readCursor ∧
    (resumeRaw p env (budget + 1) s).state.deliveryUsed = s.deliveryUsed := by
  obtain ⟨step, spinning⟩ := observed_park_resumes (env := env) phase valid
  have eq := (ResumeTo.advance step (runRaw_sound (budget := budget))).compute
  rw [eq]
  have retained := selected_spin_retains spinning (runRaw_prefix (env := env) (budget := budget))
  exact ⟨retained.2.1, retained.2.2.2.1, retained.2.2.2.2.2.1⟩

end ANL.Boot.Runtime
