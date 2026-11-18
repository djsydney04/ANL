import ANL.BootV2RuntimeTickProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (WordAt)
variable {p : ANL.Boot.V2.Program} {env : Environment} {s : State}
set_option linter.unusedSimpArgs false

theorem Raised.retains (raised : Raised p env s q next) :
    next.phase = .faultPending q ∧ next.nextOrdinal = s.nextOrdinal + 1 ∧
    next.revEvents = .fault (.raised q) :: s.revEvents ∧
    next.machine = s.machine ∧ next.origins = s.origins ∧ next.hardware = s.hardware ∧
    next.readCursor = s.readCursor ∧ next.deliveryUsed = s.deliveryUsed ∧
    next.forwardingUsed = s.forwardingUsed ∧ next.interrupted = s.interrupted ∧
    next.episode = s.episode ∧ next.stackRole = s.stackRole ∧
    next.bootParkSeen = s.bootParkSeen ∧ next.episodeParkSeen = s.episodeParkSeen := by
  cases raised
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Raised.pending_valid (raised : Raised p env s q next) : FaultRaisedValid p env next q := by
  cases raised with
  | raise phase valid =>
    rcases valid with ⟨⟨frontier, positive, ordinal, unused⟩, hardware, installed⟩
    refine ⟨?_, positive, ?_, unused, hardware, installed, ?_⟩
    · change FaultAt p env s q
      exact frontier
    · change q.ordinal + 1 = s.nextOrdinal + 1
      exact congrArg (fun n => n + 1) ordinal
    · exact LatestRaised.iff.mpr ⟨s.revEvents, rfl⟩

theorem Raised.no_legacy_after (raised : Raised p env s q next) :
    next.phase ≠ .legacy (.primitiveAfter pending value) ∧
      next.phase ≠ .legacy (.primitiveReturn pending value) := by
  rw [raised.retains.1]
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem pending_not_raised (phase : s.phase = .faultPending q) : ¬ Raised p env s request next := by
  intro raised
  cases raised with
  | raise commit _ => rw [phase] at commit; cases commit

theorem ForwardReset.frontier (reset : ForwardReset p env s q next) :
    s.phase = .faultPending q ∧ FaultRaisedValid p env s q ∧ env.fault.forwarding = some .forward := by
  cases reset with | handler phase valid response _ _ _ _ => exact ⟨phase, valid, response⟩

theorem ForwardReset.retains (reset : ForwardReset p env s q next) :
    next.phase = .legacy .ordinary ∧ next.episode = .hardwareHandler ∧ next.stackRole = .terminal ∧
    next.origins = ANL.Boot.Origin.rootMetadata p.entries.hardware.function ∧
    next.machine.world = s.machine.world ∧ next.readCursor = s.readCursor ∧
    next.nextOrdinal = s.nextOrdinal ∧ next.deliveryUsed = s.deliveryUsed ∧
    next.forwardingUsed = true ∧ next.bootParkSeen = s.bootParkSeen ∧ next.episodeParkSeen = false ∧
    next.revEvents = .fault (.forwarded q) :: s.revEvents ∧ next.interrupted = some s.snapshot ∧
    next.hardware.sstatus = Fault.forwardedStatus s.hardware.sstatus ∧
    next.hardware.sie = s.hardware.sie ∧ next.hardware.installedHandler = s.hardware.installedHandler := by
  cases reset with
  | handler _ _ _ _ _ _ entered =>
    exact ⟨rfl, rfl, rfl, rfl, entered.world, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ForwardReset.saved_pending (reset : ForwardReset p env s q next) :
    next.interrupted = some s.snapshot ∧ s.snapshot.phase = .faultPending q := by
  cases reset with
  | handler phase _ _ _ _ _ _ => exact ⟨rfl, phase⟩

theorem ForwardReset.arguments (reset : ForwardReset p env s q next) :
    ∃ cause pc auxiliary, WordAt .w64 2 cause ∧ WordAt .w64 q.pc pc ∧ WordAt .w64 0 auxiliary ∧
      next.machine.current.env = [auxiliary, pc, cause] ∧
      next.machine.current.function = p.entries.hardware.function ∧
      next.machine.kont = [] ∧ next.machine.current.resources = [] := by
  cases reset with
  | handler _ _ _ hc hp ha entered =>
    cases entered
    exact ⟨_, _, _, hc, hp, ha, rfl, rfl, rfl, rfl⟩

theorem ForwardReset.defined (reset : ForwardReset p env s q next) :
    ∃ d, p.functions[p.entries.hardware.function]? = some (.defined d) := by
  cases reset with
  | handler _ _ _ _ _ _ entered =>
    cases entered with | defined found => exact ⟨_, found⟩

theorem ForwardReset.hardware_valid (reset : ForwardReset p env s q next) : next.hardware.Valid := by
  cases reset with
  | handler _ valid _ _ _ _ _ =>
    exact ⟨Fault.forwardedStatus_bound _, valid.2.2.2.2.1.2⟩

theorem ForwardReset.status_bits (reset : ForwardReset p env s q next) :
    next.hardware.sstatus < Fault.modulus ∧ next.hardware.sstatus.testBit 1 = false ∧
      next.hardware.sstatus.testBit 8 = true ∧ next.hardware.sstatus.testBit 5 = s.hardware.sstatus.testBit 1 := by
  cases reset
  exact ⟨Fault.forwardedStatus_bound _, Fault.forwardedStatus_sie _, Fault.forwardedStatus_spp _,
    Fault.forwardedStatus_spie _⟩

theorem ForwardReset.typed (wf : WellFormedProgram p) (_input : InputValid p env)
    (world : s.machine.world = .initial) (reset : ForwardReset p env s q next) :
    Words.State.Typed p.carrier next.machine unitTy ∧ Origin.Aligned p next.machine next.origins := by
  cases reset with
  | handler _ _ _ hc hp ha entered =>
    rw [world] at entered
    exact ⟨entered.typed wf wf.roles.hardware (by simp [hc.type, hp.type, ha.type, wordTy]), entered.aligned⟩

theorem resetForward_exists (wf : WellFormedProgram p) (input : InputValid p env)
    (phase : s.phase = .faultPending q) (valid : FaultRaisedValid p env s q)
    (response : env.fault.forwarding = some .forward) : ∃ next, ForwardReset p env s q next := by
  obtain ⟨cause, hc⟩ := word_value_exists (width := .w64) (n := 2) (by decide)
  obtain ⟨pc, hp⟩ := word_value_exists (width := .w64) (valid.1.site_valid input).1
  obtain ⟨auxiliary, ha⟩ := word_value_exists (width := .w64) (n := 0) (by decide)
  obtain ⟨machine, entered⟩ := role_enter_exists wf.roles.hardware [cause, pc, auxiliary] s.machine.world
  exact ⟨_, .handler phase valid response hc hp ha entered⟩

theorem forwarding_checked (wf : WellFormedProgram p) (input : InputValid p env)
    (world : s.machine.world = .initial) (phase : s.phase = .faultPending q)
    (valid : FaultRaisedValid p env s q) (response : env.fault.forwarding = some .forward) :
    ∃ next, resetForward p env s q = some next ∧ Words.State.Typed p.carrier next.machine unitTy ∧
      Origin.Aligned p next.machine next.origins := by
  obtain ⟨next, reset⟩ := resetForward_exists wf input phase valid response
  exact ⟨next, resetForward_iff.mpr reset, reset.typed wf input world⟩

theorem fault_before_D_ineligible (phase : s.phase = .faultBefore q) (valid : FaultBeforeValid p env s q)
    (delivery : DeliveryAt env s (.beforePrimitive q.ordinal q.declaration) d) (ineligible : ¬ Eligible p s) :
    tickRaw p env s = .ineligibleDelivery s :=
  (BootOutcome.ready (.faultBefore phase valid) (.faultBefore (.ineligible delivery ineligible))).compute

theorem fault_before_D_delivers (phase : s.phase = .faultBefore q) (valid : FaultBeforeValid p env s q)
    (delivery : DeliveryAt env s (.beforePrimitive q.ordinal q.declaration) d)
    (eligible : Eligible p s) (reset : HardwareReset p s d next) : tickRaw p env s = .advance next :=
  (BootOutcome.ready (.faultBefore phase valid) (.faultBefore (.deliver delivery eligible reset))).compute

theorem fault_before_without_D (phase : s.phase = .faultBefore q) (valid : FaultBeforeValid p env s q)
    (absent : ∀ d, ¬ DeliveryAt env s (.beforePrimitive q.ordinal q.declaration) d) :
    tickRaw p env s = .advance (withPhase s (.faultCommit q)) :=
  (BootOutcome.ready (.faultBefore phase valid) (.faultBefore (.absent absent))).compute

theorem fault_commit_raises (phase : s.phase = .faultCommit q) (valid : FaultCommitValid p env s q) :
    tickRaw p env s = .advance (raiseFaultState s q) :=
  (BootOutcome.ready (.faultCommit phase valid) (.raised (.raise phase valid))).compute

theorem fault_pending_blocks (blocked : ForwardBlocked p env s q) : tickRaw p env s = .blockedForwarding s :=
  (BootOutcome.ready (.faultPending blocked.1 blocked.2.1) (.forwardBlocked blocked)).compute

theorem fault_pending_block_stable (blocked : ForwardBlocked p env s q) :
    tickRaw p env (tickRaw p env s).state = .blockedForwarding s := by
  rw [fault_pending_blocks blocked]
  exact fault_pending_blocks blocked

theorem fault_pending_invalid (phase : s.phase = .faultPending q) (invalid : ¬ FaultRaisedValid p env s q) :
    tickRaw p env s = .invalidState s := by simp [tickRaw, command, phase, invalid]

theorem fault_pending_forwards (reset : ForwardReset p env s q next) : tickRaw p env s = .advance next :=
  (BootOutcome.ready (.faultPending reset.frontier.1 reset.frontier.2.1) (.forwarded reset)).compute

theorem after_illegal_input_invalid (illegal : p.operationAt ident = some (.illegalInstruction authority))
    (present : env.legacy.delivery = some d) (landmark : d.landmark = .afterPrimitive ordinal ident) :
    ¬ InputValid p env := by
  intro input
  have scope := (input.delivery d present).scope
  rw [landmark] at scope
  exact illegal_after_not_scoped illegal scope

end ANL.Boot.V2.Runtime
