import ANL.BootRuntimeProgress

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}

/-- The nine exact control/phase shapes of the fixed handler, including its sole park observation. -/
def handlerPoint (function : Nat) (values : Env) (position : Nat) :
    Words.State × Origin.Metadata × Phase × Bool :=
  let root := Origin.Location.root function
  let loop := root.child .letValue
  let activation : Activation := ⟨function, values, []⟩
  let kont := [Frame.bind false emptyTerm]
  match position with
  | 0 => (⟨.eval handler, activation, [], .initial⟩, ⟨root, []⟩, .ordinary, false)
  | 1 => (⟨.eval park, activation, kont, .initial⟩, ⟨loop, [root]⟩, .ordinary, false)
  | 2 => (⟨.eval park, activation, kont, .initial⟩, ⟨loop, [root]⟩, .parkCheck loop, false)
  | 3 => (⟨.eval park, activation, kont, .initial⟩, ⟨loop, [root]⟩, .parkObserved loop, true)
  | 4 => (⟨.eval park, activation, kont, .initial⟩, ⟨loop, [root]⟩, .ordinary, true)
  | 5 => (⟨.eval trueTerm, activation, .condition trueTerm emptyTerm :: kont, .initial⟩,
      ⟨loop.child .whileCondition, [loop, root]⟩, .ordinary, true)
  | 6 => (⟨.ret (.scalar (.legacy (.bool true))), activation, .condition trueTerm emptyTerm :: kont, .initial⟩,
      ⟨loop.child .whileCondition, [loop, root]⟩, .ordinary, true)
  | 7 => (⟨.eval emptyTerm, activation, .body trueTerm emptyTerm :: kont, .initial⟩,
      ⟨loop.child .whileBody, [loop, root]⟩, .ordinary, true)
  | 8 => (⟨.ret unitValue, activation, .body trueTerm emptyTerm :: kont, .initial⟩,
      ⟨loop.child .whileBody, [loop, root]⟩, .ordinary, true)
  | _ => (⟨.eval handler, activation, [], .initial⟩, ⟨root, []⟩, .ordinary, false)

def HandlerAt (p : Program) (s : State) (values : Env) (position : Nat) : Prop :=
  let point := handlerPoint (s.episode.function p) values position
  s.machine = point.1 ∧ s.origins = point.2.1 ∧ s.phase = point.2.2.1 ∧ s.episodeParkSeen = point.2.2.2

/-- Shape invariant only. It does not encode execution or future absence of events. -/
def HandlerOrbit (p : Program) (s : State) : Prop :=
  s.episode ≠ .boot → ∃ values position, position < 9 ∧ HandlerAt p s values position

def handlerSuccessor (position : Nat) : Nat := if position = 8 then 5 else position + 1

/-- A proof fixture for the next shape; actual BootStep agreement is proved separately. -/
def handlerAdvance (p : Program) (s : State) (values : Env) (position : Nat) : State :=
  let point := handlerPoint (s.episode.function p) values (handlerSuccessor position)
  { s with machine := point.1, origins := point.2.1, phase := point.2.2.1, episodeParkSeen := point.2.2.2 }

 theorem handlerSuccessor_bound (bound : position < 9) : handlerSuccessor position < 9 := by
  unfold handlerSuccessor
  split <;> omega

 theorem handlerAdvance_at : HandlerAt p (handlerAdvance p s values position) values (handlerSuccessor position) :=
  ⟨rfl, rfl, rfl, rfl⟩

 theorem handlerAdvance_orbit (bound : position < 9) : HandlerOrbit p (handlerAdvance p s values position) :=
  fun _ => ⟨values, _, handlerSuccessor_bound bound, handlerAdvance_at⟩

 theorem selected_handler (wf : WellFormedProgram p) (notBoot : episode ≠ .boot) :
    SelectedPark p episode ((Origin.Location.root (episode.function p)).child .letValue) := by
  cases episode with
  | boot => contradiction
  | hardwareHandler =>
    cases wf.roles.hardware with | intro found _ _ _ =>
     apply SelectedPark.role (p := p) (episode := .hardwareHandler) (path := [.value]) found
     rw [wf.roles.hardwareBody _ found]
     exact .letValue .park
  | languageHandler =>
    cases wf.roles.language with | intro found _ _ _ =>
     apply SelectedPark.role (p := p) (episode := .languageHandler) (path := [.value]) found
     rw [wf.roles.languageBody _ found]
     exact .letValue .park

 theorem Start.handler_orbit (started : Start p env s) : HandlerOrbit p s := by
  cases started
  intro impossible
  exact False.elim (impossible rfl)

 theorem HardwareReset.handler_orbit (wf : WellFormedProgram p) (world : s.machine.world = .initial)
    (reset : HardwareReset p s d next) : HandlerOrbit p next := by
  cases reset with | @handler cause pc auxiliary machine _ _ _ entered =>
   cases entered with | defined found =>
    intro _
    refine ⟨[auxiliary, pc, cause], 0, by decide, ?_⟩
    simp only [HandlerAt, handlerPoint, hardwareResetState, Episode.function, Origin.rootMetadata]
    rw [wf.roles.hardwareBody _ found, world]
    exact ⟨rfl, True.intro, True.intro, True.intro⟩

 theorem LanguageReset.handler_orbit (wf : WellFormedProgram p) (world : s.machine.world = .initial)
    (reset : LanguageReset p s tag next) : HandlerOrbit p next := by
  cases reset with | @handler value machine _ entered =>
   cases entered with | defined found =>
    intro _
    refine ⟨[value], 0, by decide, ?_⟩
    simp only [HandlerAt, handlerPoint, languageResetState, Episode.function, Origin.rootMetadata]
    rw [wf.roles.languageBody _ found, world]
    exact ⟨rfl, True.intro, True.intro, True.intro⟩

end ANL.Boot.Runtime
