import ANL.BootRuntimeTickProofs

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem tick_language (phase : s.phase = .ordinary) (controlEq : s.machine.control = .trap trap)
    (tagged : LanguageTag trap tag) (reset : LanguageReset p s tag next) :
    tickRaw p env s = .advance next :=
  tickRaw_step_iff.mpr (.advance (.language phase controlEq tagged) (.language reset))

 theorem tick_capture (phase : s.phase = .ordinary) (notPark : ¬ FirstPark p s) (captured : Captured p s q) :
    tickRaw p env s = .advance (withPhase s (.primitiveBefore q)) :=
  tickRaw_step_iff.mpr (.advance (.capture phase notPark captured) .captured)

 theorem tick_before (phase : s.phase = .primitiveBefore q) (valid : BeforeValid p s q) :
    tickRaw p env s = atCut p env s (.beforePrimitive q.ordinal q.declaration) (withPhase s (.primitiveCommit q)) := by
  simp [tickRaw, (Ready.before phase valid).compute, execute]

 theorem tick_after (phase : s.phase = .primitiveAfter q v) (valid : AfterValid p s q v) :
    tickRaw p env s = atCut p env s (.afterPrimitive q.ordinal q.declaration) (withPhase s (.primitiveReturn q v)) := by
  simp [tickRaw, (Ready.after phase valid).compute, execute]

 theorem tick_commit (phase : s.phase = .primitiveCommit q) (valid : BeforeValid p s q)
    (effect : Effect p env s.hardware s.readCursor q.operation q.arguments result) :
    tickRaw p env s = .advance (commitState s q result) :=
  tickRaw_step_iff.mpr (.advance (.commit phase valid) (.commit effect))

 theorem tick_read_blocked (phase : s.phase = .primitiveCommit q) (valid : BeforeValid p s q)
    (block : ReadBlocked p env s.hardware s.readCursor q.operation q.arguments) :
    tickRaw p env s = .blockedRead s :=
  tickRaw_iff.mpr (.ready (.commit phase valid) (.blocked block))

 theorem tick_finish (phase : s.phase = .primitiveReturn q v) (valid : AfterValid p s q v) :
    tickRaw p env s = .advance (returnState s v) :=
  tickRaw_step_iff.mpr (.advance (.finish phase valid) .finish)

 theorem tick_first_park (phase : s.phase = .ordinary) (first : FirstPark p s) :
    tickRaw p env s = .advance (withPhase s (.parkCheck s.origins.control)) :=
  tickRaw_step_iff.mpr (.advance (.park phase first) .enterPark)

 theorem tick_park_handler (phase : s.phase = .parkCheck location) (valid : ParkWaiting p s location)
    (handler : s.episode ≠ .boot) : tickRaw p env s = .advance (observedPark s location) :=
  tickRaw_step_iff.mpr (.advance (.parkCheck phase valid) (.parkHandler handler))

 theorem tick_park_resume (phase : s.phase = .parkObserved location) (valid : ParkConsumed p s location) :
    tickRaw p env s = .advance (withPhase s .ordinary) :=
  tickRaw_step_iff.mpr (.advance (.parkResume phase valid) .parkResume)

 theorem pre_delivery (phase : s.phase = .primitiveBefore q) (valid : BeforeValid p s q)
    (present : DeliveryAt env s (.beforePrimitive q.ordinal q.declaration) d)
    (eligible : Eligible p s) (reset : HardwareReset p s d next) :
    tickRaw p env s = .advance next ∧ next.readCursor = s.readCursor ∧
    next.nextOrdinal = s.nextOrdinal ∧ next.revEvents = .hardware d.landmark d.scause d.sepc d.stval :: s.revEvents := by
  refine ⟨tickRaw_step_iff.mpr (.advance (.before phase valid) (.before (.deliver present eligible reset))), ?_⟩
  exact ⟨reset.retains.2.1, reset.retains.2.2.1, reset.retains.2.2.2.2.2.1⟩

 theorem post_delivery (phase : s.phase = .primitiveAfter q v) (valid : AfterValid p s q v)
    (present : DeliveryAt env s (.afterPrimitive q.ordinal q.declaration) d)
    (eligible : Eligible p s) (reset : HardwareReset p s d next) :
    tickRaw p env s = .advance next ∧ next.readCursor = s.readCursor ∧
    next.nextOrdinal = s.nextOrdinal ∧ next.hardware = s.hardware ∧
    next.interrupted = some s.snapshot ∧ s.snapshot.phase = .primitiveAfter q v ∧
    next.revEvents = .hardware d.landmark d.scause d.sepc d.stval :: s.revEvents := by
  refine ⟨tickRaw_step_iff.mpr (.advance (.after phase valid) (.after (.deliver present eligible reset))), ?_⟩
  exact ⟨reset.retains.2.1, reset.retains.2.2.1, reset.retains.1,
    reset.retains.2.2.2.2.1, phase, reset.retains.2.2.2.2.2.1⟩

 theorem pre_ineligible (phase : s.phase = .primitiveBefore q) (valid : BeforeValid p s q)
    (present : DeliveryAt env s (.beforePrimitive q.ordinal q.declaration) d) (ineligible : ¬ Eligible p s) :
    tickRaw p env s = .ineligibleDelivery s :=
  tickRaw_iff.mpr (.ready (.before phase valid) (.before (.ineligible present ineligible)))

 theorem before_absent (phase : s.phase = .primitiveBefore q) (valid : BeforeValid p s q)
    (absent : ∀ d, ¬ DeliveryAt env s (.beforePrimitive q.ordinal q.declaration) d) :
    tickRaw p env s = .advance (withPhase s (.primitiveCommit q)) :=
  tickRaw_step_iff.mpr (.advance (.before phase valid) (.before (.absent absent)))

 theorem after_absent (phase : s.phase = .primitiveAfter q v) (valid : AfterValid p s q v)
    (absent : ∀ d, ¬ DeliveryAt env s (.afterPrimitive q.ordinal q.declaration) d) :
    tickRaw p env s = .advance (withPhase s (.primitiveReturn q v)) :=
  tickRaw_step_iff.mpr (.advance (.after phase valid) (.after (.absent absent)))

 theorem park_delivery (phase : s.phase = .parkCheck location) (valid : ParkWaiting p s location)
    (boot : s.episode = .boot) (present : DeliveryAt env s (.bootPark location) d)
    (eligible : Eligible p s) (reset : HardwareReset p s d next) : tickRaw p env s = .advance next :=
  tickRaw_step_iff.mpr (.advance (.parkCheck phase valid) (.parkBoot boot (.deliver present eligible reset)))

 theorem BootOutcome.blocked (outcome : BootOutcome p env s (.blockedRead stopped)) :
    stopped = s ∧ ∃ q, s.phase = .primitiveCommit q ∧ BeforeValid p s q ∧
      ReadBlocked p env s.hardware s.readCursor q.operation q.arguments := by
  cases outcome with
  | ready ready execution =>
    cases execution with
    | blocked block => cases ready with | commit phase valid => exact ⟨rfl, _, phase, valid, block⟩
    | before cut | after cut | parkBoot _ cut => cases cut

 theorem blocked_iff : tickRaw p env s = .blockedRead stopped ↔
    stopped = s ∧ ∃ q, s.phase = .primitiveCommit q ∧ BeforeValid p s q ∧
      ReadBlocked p env s.hardware s.readCursor q.operation q.arguments := by
  constructor
  · intro output; exact (tickRaw_iff.mp output).blocked
  · rintro ⟨rfl, q, phase, valid, block⟩; exact tick_read_blocked phase valid block

 theorem returnState_retains :
    (returnState s v).machine.control = .ret v ∧ (returnState s v).machine.current = s.machine.current ∧
    (returnState s v).machine.kont = s.machine.kont ∧ (returnState s v).machine.world = s.machine.world ∧
    (returnState s v).origins = s.origins ∧ (returnState s v).revEvents = s.revEvents ∧
    (returnState s v).readCursor = s.readCursor := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

 theorem administrative_retains :
    (withPhase s phase).machine = s.machine ∧ (withPhase s phase).origins = s.origins ∧
    (withPhase s phase).hardware = s.hardware ∧ (withPhase s phase).revEvents = s.revEvents ∧
    (withPhase s phase).readCursor = s.readCursor ∧ (withPhase s phase).nextOrdinal = s.nextOrdinal ∧
    (withPhase s phase).deliveryUsed = s.deliveryUsed := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.Runtime
