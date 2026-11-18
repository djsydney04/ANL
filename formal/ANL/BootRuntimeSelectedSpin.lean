import ANL.BootRuntimeEventPrefixes

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}
set_option linter.unusedSimpArgs false

/-- The literal-true empty loop keeps the exact lower continuation and origin stack. -/
def spinPoint (a : Activation) (k : List Frame) (w : Memory.World) (location : Origin.Location)
    (frames : List Origin.Location) (position : Nat) : Words.State × Origin.Metadata :=
  match position with
  | 0 => (⟨.eval park, a, k, w⟩, ⟨location, frames⟩)
  | 1 => (⟨.eval trueTerm, a, .condition trueTerm emptyTerm :: k, w⟩,
      ⟨location.child .whileCondition, location :: frames⟩)
  | 2 => (⟨.ret (.scalar (.legacy (.bool true))), a, .condition trueTerm emptyTerm :: k, w⟩,
      ⟨location.child .whileCondition, location :: frames⟩)
  | 3 => (⟨.eval emptyTerm, a, .body trueTerm emptyTerm :: k, w⟩,
      ⟨location.child .whileBody, location :: frames⟩)
  | 4 => (⟨.ret unitValue, a, .body trueTerm emptyTerm :: k, w⟩,
      ⟨location.child .whileBody, location :: frames⟩)
  | _ => (⟨.eval park, a, k, w⟩, ⟨location, frames⟩)

def SpinAt (s : State) (a : Activation) (k : List Frame) (w : Memory.World) (location : Origin.Location)
    (frames : List Origin.Location) (position : Nat) : Prop :=
  s.machine = (spinPoint a k w location frames position).1 ∧
  s.origins = (spinPoint a k w location frames position).2 ∧ s.phase = .ordinary ∧ s.episodeParkSeen = true

def Spinning (s : State) (location : Origin.Location) : Prop :=
  ∃ a k w frames position, position < 5 ∧ SpinAt s a k w location frames position

def SelectedSpin (p : Program) (s : State) : Prop :=
  ∃ location, SelectedPark p s.episode location ∧ Spinning s location

def spinSuccessor (position : Nat) : Nat := if position = 4 then 1 else position + 1

def spinAdvance (s : State) (a : Activation) (k : List Frame) (w : Memory.World) (location : Origin.Location)
    (frames : List Origin.Location) (position : Nat) : State :=
  let point := spinPoint a k w location frames (spinSuccessor position)
  { s with machine := point.1, origins := point.2 }

 theorem spinSuccessor_bound (bound : position < 5) : spinSuccessor position < 5 := by
  unfold spinSuccessor
  split <;> omega

 theorem SpinAt.tick (bound : position < 5) (point : SpinAt s a k w location frames position) :
    tickRaw p env s = .advance (spinAdvance s a k w location frames position) := by
  rcases point with ⟨machine, origins, phase, seen⟩
  have positions : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 ∨ position = 4 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl
  all_goals simp [tickRaw, command, execute, phase, machine, origins, seen,
    spinAdvance, spinSuccessor, spinPoint, park, trueTerm, emptyTerm, FirstPark,
    capture, Origin.step, Origin.checkAdmitted, Origin.Admitted, Words.step, Origin.advance,
    Origin.action, Origin.applyAction, ordinaryState] at *

 theorem spinning_step_exact (spin : Spinning s location) (step : BootStep p env s next) :
    ∃ a k w frames position, position < 5 ∧ SpinAt s a k w location frames position ∧
      next = spinAdvance s a k w location frames position := by
  obtain ⟨a, k, w, frames, position, bound, point⟩ := spin
  exact ⟨a, k, w, frames, position, bound, point,
    TickResult.advance.inj ((tickRaw_step_iff.mpr step).symm.trans (point.tick bound))⟩

 theorem spinning_preserved (spin : Spinning s location) (step : BootStep p env s next) : Spinning next location := by
  obtain ⟨a, k, w, frames, position, bound, point, rfl⟩ := spinning_step_exact spin step
  exact ⟨a, k, w, frames, _, spinSuccessor_bound bound, rfl, rfl, point.2.2.1, point.2.2.2⟩

 theorem spinning_retains (spin : Spinning s location) (step : BootStep p env s next) :
    next.episode = s.episode ∧ next.revEvents = s.revEvents ∧ next.hardware = s.hardware ∧
    next.readCursor = s.readCursor ∧ next.nextOrdinal = s.nextOrdinal ∧
    next.deliveryUsed = s.deliveryUsed ∧ next.bootParkSeen = s.bootParkSeen ∧
    next.episodeParkSeen = s.episodeParkSeen ∧ next.interrupted = s.interrupted := by
  obtain ⟨a, k, w, frames, position, _, _, rfl⟩ := spinning_step_exact spin step
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

 theorem SelectedSpin.step (spin : SelectedSpin p s) (step : BootStep p env s next) : SelectedSpin p next := by
  obtain ⟨location, selected, spinning⟩ := spin
  exact ⟨location, (spinning_retains spinning step).1 ▸ selected, spinning_preserved spinning step⟩

 theorem park_resume_selected_spin (valid : ParkConsumed p s location) : SelectedSpin p (withPhase s .ordinary) := by
  rcases valid with ⟨⟨origin, function, selected, ctl⟩, seen, _⟩
  have controlEq := ParkControl.eq ctl
  refine ⟨location, selected, s.machine.current, s.machine.kont, s.machine.world, s.origins.frames, 0, by decide, ?_⟩
  refine ⟨?_, ?_, rfl, seen⟩
  · change s.machine = ⟨.eval park, s.machine.current, s.machine.kont, s.machine.world⟩
    rw [← controlEq]
  · change s.origins = ⟨location, s.origins.frames⟩
    rw [origin]

 theorem observed_park_resumes (phase : s.phase = .parkObserved location) (valid : ParkConsumed p s location) :
    BootStep p env s (withPhase s .ordinary) ∧ SelectedSpin p (withPhase s .ordinary) :=
  ⟨.advance (.parkResume phase valid) .parkResume, park_resume_selected_spin valid⟩

 theorem SelectedSpin.phase (spin : SelectedSpin p s) : s.phase = .ordinary ∧ s.episodeParkSeen = true := by
  obtain ⟨location, _, a, k, w, frames, position, _, point⟩ := spin
  exact point.2.2

 theorem SelectedSpin.steps (spin : SelectedSpin p s) (steps : BootStepsN p env n s last) : SelectedSpin p last := by
  induction steps with
  | zero => exact spin
  | succ step _ ih => exact ih (spin.step step)

 theorem selected_spin_retains (spin : SelectedSpin p s) (steps : BootStepsN p env n s last) :
    last.episode = s.episode ∧ last.revEvents = s.revEvents ∧ last.hardware = s.hardware ∧
    last.readCursor = s.readCursor ∧ last.nextOrdinal = s.nextOrdinal ∧
    last.deliveryUsed = s.deliveryUsed ∧ last.bootParkSeen = s.bootParkSeen ∧
    last.episodeParkSeen = s.episodeParkSeen ∧ last.interrupted = s.interrupted := by
  induction steps with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ step _ ih =>
    have one := spinning_retains spin.choose_spec.2 step
    have rest := ih (spin.step step)
    rcases one with ⟨a, b, c, d, e, f, g, h, i⟩
    rcases rest with ⟨a', b', c', d', e', f', g', h', i'⟩
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d, e'.trans e, f'.trans f, g'.trans g, h'.trans h, i'.trans i⟩

 theorem selected_park_not_observed_again (spin : SelectedSpin p s) (steps : BootStepsN p env n s last) :
    ∀ location, last.phase ≠ .parkObserved location := by
  intro location
  rw [(spin.steps steps).phase.1]
  intro impossible
  cases impossible

end ANL.Boot.Runtime
