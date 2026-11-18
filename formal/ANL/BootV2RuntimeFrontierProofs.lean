import ANL.BootV2RuntimeFrontiers
import ANL.BootV2Authority
import ANL.BootRuntimeOccurrenceTyping

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Pending Episode Landmark Delivery ParkControl)
variable {p : ANL.Boot.V2.Program} {s : State} {ident : Nat}
set_option linter.unusedSimpArgs false

theorem captureLegacy_iff : captureLegacy p s = some q ↔ CapturedLegacy p s q := by
  constructor
  · intro found
    unfold captureLegacy at found
    split at found
    next ident values controlEq =>
      split at found
      next row declaration =>
        split at found
        next operation operationEq =>
          dsimp only at found
          split at found
          next valid =>
            simp only [Option.some.injEq] at found
            subst q
            exact .invoke controlEq declaration operationEq valid
          next => cases found
        next => cases found
      next => cases found
    next => cases found
  · intro captured
    cases captured with
    | invoke controlEq declaration operation valid =>
      simp [captureLegacy, controlEq, declaration, operation, valid]

theorem CapturedLegacy.valid (h : CapturedLegacy p s q) : LegacyPendingAt p s q := by cases h; assumption
theorem CapturedLegacy.ordinal (h : CapturedLegacy p s q) : q.ordinal = s.nextOrdinal := by cases h; rfl
theorem CapturedLegacy.origin (h : CapturedLegacy p s q) : q.origin = s.origins.control := by cases h; rfl
theorem CapturedLegacy.frontier (h : CapturedLegacy p s q) : Origin.PrimitiveFrontier p s.machine := by
  cases h with | invoke controlEq declaration _ _ => exact ⟨_, _, _, controlEq, declaration⟩
theorem CapturedLegacy.unique (a : CapturedLegacy p s q) (b : CapturedLegacy p s r) : q = r :=
  Option.some.inj ((captureLegacy_iff.mpr a).symm.trans (captureLegacy_iff.mpr b))

theorem LegacyPendingAt.invocation (valid : LegacyPendingAt p s q) :
    ∃ values row, s.machine.control = .invoke q.declaration none values ∧
      p.functions[q.declaration]? = some (.primitive row) ∧
      row.operation = .legacy q.operation ∧ values.reverse = q.arguments := by
  rcases valid with ⟨_, _, _, _, _, facts⟩
  split at facts
  next ident values row ty target terms controlEq found located =>
    rcases facts with ⟨rfl, _, operation, _, _, arguments⟩
    exact ⟨values, row, controlEq, found, operation, arguments⟩
  next => contradiction

theorem LegacyPendingAt.located (valid : LegacyPendingAt p s q) :
    ∃ ty args, Origin.Located p q.origin (.call ty q.declaration args) := by
  rcases valid with ⟨_, _, _, _, _, facts⟩
  split at facts
  next ident values row ty target terms controlEq found located =>
    rcases facts with ⟨_, rfl, _, _, _, _⟩
    exact ⟨ty, terms, Origin.lookup_iff.mp located⟩
  next => contradiction

theorem LegacyPendingAt.operation (valid : LegacyPendingAt p s q) :
    p.operationAt q.declaration = some (.legacy q.operation) := by
  obtain ⟨values, row, _, found, operation, _⟩ := valid.invocation
  simp [Program.operationAt, found, operation]

theorem LegacyPendingAt.not_illegal (valid : LegacyPendingAt p s q) :
    p.operationAt q.declaration ≠ some (.illegalInstruction authority) := by
  simp [valid.operation]

theorem checkFaultAt_iff : checkFaultAt p env s q = true ↔ FaultAt p env s q := by simp [checkFaultAt]
theorem checkFaultBefore_iff : checkFaultBefore p env s q = true ↔ FaultBeforeValid p env s q := by
  simp [checkFaultBefore]
theorem checkFaultCommit_iff : checkFaultCommit p env s q = true ↔ FaultCommitValid p env s q := by
  simp [checkFaultCommit]
theorem checkFaultRaised_iff : checkFaultRaised p env s q = true ↔ FaultRaisedValid p env s q := by
  simp [checkFaultRaised]

theorem FaultAt.invocation (valid : FaultAt p env s q) :
    s.machine.control = .invoke q.declaration none [] ∧
    p.operationAt q.declaration = some (.illegalInstruction 0) ∧
    Origin.Located p q.origin (.call unitTy q.declaration []) := by
  rcases valid with ⟨_, _, _, _, _, facts⟩
  split at facts
  next ident authority ty target controlEq operation found =>
    rcases facts with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨controlEq, operation, Origin.lookup_iff.mp found⟩
  next => contradiction

theorem FaultAt.site_valid (input : InputValid p env) (valid : FaultAt p env s q) :
    Fault.SiteValid p q.pc := input.fault.site q.pc valid.2.2.2.2.1

theorem FaultAt.pending_at_request (valid : FaultAt p env s q) (positive : 0 < q.ordinal)
    (installed : s.hardware.installedHandler = some p.entries.hardware.function) :
    Fault.PendingValid p env.fault s.hardware q.ordinal (s.pendingView q) := by
  rcases q with ⟨ordinal, declaration, ⟨function, path⟩, pc⟩
  obtain ⟨controlEq, operation, located⟩ := valid.invocation
  rcases valid with ⟨episode, current, source, origin, site, _⟩
  have sourceFunction : function = p.entries.boot.function := source
  refine ⟨episode, rfl, positive, site, operation, installed, current, source, origin, controlEq, ?_⟩
  cases located with
  | intro found occurrence => exact ⟨_, by simpa only [sourceFunction] using found, occurrence⟩

theorem FaultCommitValid.pending (valid : FaultCommitValid p env s q) :
    Fault.PendingValid p env.fault s.hardware s.nextOrdinal (s.pendingView q) := by
  have pending := valid.1.1.pending_at_request valid.1.2.1 valid.2.2
  simpa [valid.1.2.2.1] using pending

theorem FaultRaisedValid.pending (valid : FaultRaisedValid p env s q) :
    Fault.PendingValid p env.fault s.hardware q.ordinal (s.pendingView q) :=
  valid.1.pending_at_request valid.2.1 valid.2.2.2.2.2.1

theorem FaultRaisedValid.counter_not_precommit (valid : FaultRaisedValid p env s q) :
    q.ordinal ≠ s.nextOrdinal := by
  have afterRaise := valid.2.2.1
  omega

theorem FaultBeforeValid.hardware_independent :
    FaultBeforeValid p env { s with hardware := hardware } q ↔ FaultBeforeValid p env s q := Iff.rfl

theorem FaultAt.counter_independent :
    FaultAt p env { s with nextOrdinal := ordinal } q ↔ FaultAt p env s q := Iff.rfl

theorem FaultAt.phase_independent :
    FaultAt p env { s with phase := phase } q ↔ FaultAt p env s q := Iff.rfl

theorem LatestRaised.iff : LatestRaised s q ↔ ∃ rest, s.revEvents = .fault (.raised q) :: rest := by
  cases events : s.revEvents with
  | nil => simp [LatestRaised, events]
  | cons event rest =>
    cases event with
    | legacy event => simp [LatestRaised, events]
    | fault event =>
      cases event <;> simp [LatestRaised, events, eq_comm]

theorem captureFault_iff : captureFault p env s = some q ↔ CapturedFault p env s q := by
  constructor
  · intro found
    unfold captureFault at found
    split at found
    next ident values controlEq =>
      split at found
      next authority operation =>
        split at found
        next pc site =>
          dsimp only at found
          split at found
          next valid =>
            simp only [Option.some.injEq] at found
            subst q
            exact .invoke controlEq operation site valid
          next => cases found
        next => cases found
      next => cases found
    next => cases found
  · intro captured
    cases captured with
    | invoke controlEq operation site valid => simp [captureFault, controlEq, operation, site, valid]

theorem CapturedFault.valid (h : CapturedFault p env s q) : FaultBeforeValid p env s q := by cases h; assumption
theorem CapturedFault.ordinal (h : CapturedFault p env s q) : q.ordinal = s.nextOrdinal := by cases h; rfl
theorem CapturedFault.origin (h : CapturedFault p env s q) : q.origin = s.origins.control := by cases h; rfl
theorem CapturedFault.frontier (h : CapturedFault p env s q) : Origin.PrimitiveFrontier p s.machine := by
  obtain ⟨controlEq, operation, _⟩ := h.valid.1.invocation
  unfold Program.operationAt at operation
  cases found : p.functions[q.declaration]? with
  | none => simp [found] at operation
  | some row =>
    cases row with
    | defined d => simp [found] at operation
    | primitive row => exact ⟨q.declaration, [], row, controlEq, found⟩
theorem CapturedFault.unique (a : CapturedFault p env s q) (b : CapturedFault p env s r) : q = r :=
  Option.some.inj ((captureFault_iff.mpr a).symm.trans (captureFault_iff.mpr b))

theorem captures_disjoint (legacy : CapturedLegacy p s pending) (fault : CapturedFault p env s request) : False := by
  obtain ⟨values, row, legacyControl, _, _, _⟩ := legacy.valid.invocation
  obtain ⟨faultControl, faultOperation, _⟩ := fault.valid.1.invocation
  have same : pending.declaration = request.declaration := by
    have equalControls := legacyControl.symm.trans faultControl
    simpa using congrArg (fun control : Control => match control with
      | .invoke target _ _ => target
      | _ => 0) equalControls
  have oldOperation := legacy.valid.operation
  rw [same, faultOperation] at oldOperation
  cases oldOperation

theorem located_typed (wf : WellFormedProgram p) (located : Origin.Located p origin term) :
    ∃ context ty, HasType p.signatures context [] term ty := by
  cases located with | intro found occurrence =>
    exact ANL.Boot.Runtime.occurrence_typed occurrence (wf.at found).typed

theorem declaration_signature (found : p.functions[ident]? = some row) :
    p.signatures[ident]? = some row.signature := by
  simp [Program.signatures, List.getElem?_map, found]

theorem primitive_carrier_signature (found : p.functions[ident]? = some (.primitive row)) :
    p.carrier.signatures[ident]? = some ⟨none, row.params, row.result⟩ :=
  carrier_lookup (declaration_signature found)

theorem located_call_result (wf : WellFormedProgram p)
    (located : Origin.Located p origin (.call ty ident args))
    (found : p.functions[ident]? = some (.primitive row)) : ty = row.operation.result := by
  obtain ⟨context, result, typed⟩ := located_typed wf located
  cases typed with
  | call signature _ _ =>
    have same := Option.some.inj (signature.symm.trans (declaration_signature found))
    cases same
    exact (wf.at found).result

theorem typed_invoke_arguments (typed : Words.State.Typed p.carrier ⟨.invoke ident none values, a, k, w⟩ t)
    (found : p.functions[ident]? = some (.primitive row)) : values.reverse.map Val.type = row.params := by
  cases typed with | intro env control frames layout world =>
   cases control with | invoke signature _ params _ =>
    have same := Option.some.inj (signature.symm.trans (primitive_carrier_signature found))
    cases same
    simpa [List.map_reverse] using params.symm

theorem typed_invoke_arguments_at (typed : Words.State.Typed p.carrier machine t)
    (controlEq : machine.control = .invoke ident none values)
    (found : p.functions[ident]? = some (.primitive row)) : values.reverse.map Val.type = row.params := by
  cases machine with | mk ctl a k w =>
   simp only at controlEq
   subst ctl
   exact typed_invoke_arguments typed found

theorem invoke_source_at (aligned : Origin.Aligned p s.machine s.origins)
    (controlEq : s.machine.control = .invoke ident none values) :
    ∃ ty terms, Origin.Located p s.origins.control (.call ty ident terms) ∧ values.length = terms.length := by
  have control := aligned.control
  rw [controlEq] at control
  cases control with | invoke located arity => exact ⟨_, _, located, arity⟩

theorem located_illegal_only_boot (wf : WellFormedProgram p)
    (located : Origin.Located p origin (.call ty ident args))
    (found : p.functions[ident]? = some (.primitive row))
    (operation : row.operation = .illegalInstruction 0) : origin.function = p.entries.boot.function := by
  cases located with | intro caller occurrence =>
    exact wf.illegal_call_only_boot caller (occurrence.calls (by simp [ANL.Boot.calls])) found operation

theorem captureLegacy_complete (wf : WellFormedProgram p) (typed : Words.State.Typed p.carrier s.machine t)
    (aligned : Origin.Aligned p s.machine s.origins)
    (controlEq : s.machine.control = .invoke ident none values)
    (found : p.functions[ident]? = some (.primitive row)) (operation : row.operation = .legacy op)
    (ordinal : 0 < s.nextOrdinal) : ∃ q, CapturedLegacy p s q := by
  obtain ⟨ty, terms, located, arity⟩ := invoke_source_at aligned controlEq
  have policy : PrimitiveValid p row := wf.at found
  have allowed := policy.operation
  rw [operation] at allowed
  have legacyAllowed : op.Valid p.entries.hardware.function := by cases allowed with | legacy h => exact h
  have params : values.reverse.map Val.type = op.params := by
    simpa [operation, Operation.params] using (typed_invoke_arguments_at typed controlEq found).trans policy.params
  have result : ty = op.result := by simpa [operation, Operation.result] using located_call_result wf located found
  refine ⟨_, .invoke controlEq found operation ?_⟩
  refine ⟨rfl, aligned.function, ordinal, legacyAllowed, params, ?_⟩
  simp only [controlEq, found, Origin.lookup_iff.mpr located]
  exact ⟨True.intro, True.intro, operation, result, by simpa using arity.symm, True.intro⟩

/-- Raw episode and F facts are premises, not consequences of source typing. -/
theorem captureFault_complete (wf : WellFormedProgram p) (input : InputValid p env)
    (typed : Words.State.Typed p.carrier s.machine t) (aligned : Origin.Aligned p s.machine s.origins)
    (controlEq : s.machine.control = .invoke ident none values)
    (found : p.functions[ident]? = some (.primitive row)) (operation : row.operation = .illegalInstruction 0)
    (episode : s.episode = .boot) (unused : s.forwardingUsed = false)
    (ordinal : 0 < s.nextOrdinal) : ∃ q, CapturedFault p env s q := by
  obtain ⟨ty, terms, located, arity⟩ := invoke_source_at aligned controlEq
  have policy : PrimitiveValid p row := wf.at found
  have signature := policy.illegal_signature operation
  have emptyReverse : values.reverse = [] :=
    List.map_eq_nil_iff.mp ((typed_invoke_arguments_at typed controlEq found).trans signature.1)
  have empty : values = [] := by simpa using congrArg List.reverse emptyReverse
  subst values
  have termsEmpty : terms = [] := List.length_eq_zero_iff.mp (by simpa using arity.symm)
  subst terms
  have result : ty = unitTy := by simpa [operation, Operation.result] using located_call_result wf located found
  subst ty
  have source := located_illegal_only_boot wf located found operation
  have current : s.machine.current.function = p.entries.boot.function := aligned.function.symm.trans source
  have member : row ∈ p.primitives := by
    apply List.mem_filterMap.mpr
    exact ⟨.primitive row, List.mem_of_getElem? found, rfl⟩
  have presence := input.fault.presence.mpr ⟨row, member, operation⟩
  cases site : env.fault.illegalSitePc with
  | none => simp [site] at presence
  | some pc =>
    have operationAt : p.operationAt ident = some (.illegalInstruction 0) := by
      simp [Program.operationAt, found, operation]
    refine ⟨_, .invoke controlEq operationAt site ?_⟩
    refine ⟨?_, ordinal, rfl, unused⟩
    refine ⟨episode, current, source, rfl, site, ?_⟩
    simp [controlEq, operationAt, Origin.lookup_iff.mpr located]

theorem primitive_capture_complete (wf : WellFormedProgram p) (input : InputValid p env)
    (typed : Words.State.Typed p.carrier s.machine t) (aligned : Origin.Aligned p s.machine s.origins)
    (frontier : Origin.PrimitiveFrontier p s.machine) (episode : s.episode = .boot)
    (unused : s.forwardingUsed = false) (ordinal : 0 < s.nextOrdinal) :
    (∃ q, CapturedLegacy p s q) ∨ ∃ q, CapturedFault p env s q := by
  obtain ⟨ident, values, row, controlEq, found⟩ := frontier
  cases operation : row.operation with
  | legacy op => exact .inl (captureLegacy_complete wf typed aligned controlEq found operation ordinal)
  | illegalInstruction authority =>
    have allowed := (wf.at found).operation
    rw [operation] at allowed
    cases allowed
    exact .inr (captureFault_complete wf input typed aligned controlEq found operation episode unused ordinal)

/-- Only legacy rows have this return bridge; the actual caller frames are retained. -/
theorem invoke_legacy_return_typed (wf : WellFormedProgram p)
    (typed : Words.State.Typed p.carrier ⟨.invoke ident none values, a, k, w⟩ t)
    (found : p.functions[ident]? = some (.primitive row)) (operation : row.operation = .legacy op)
    (result : value.type = op.result) : Words.State.Typed p.carrier ⟨.ret value, a, k, w⟩ t := by
  have result' : value.type = row.result := by
    rw [(wf.at found).result, operation]
    exact result
  cases typed with | intro env control frames layout world =>
   cases control with | invoke signature _ _ _ =>
    have same := Option.some.inj (signature.symm.trans (primitive_carrier_signature found))
    cases same
    exact Words.typed_ret env (result' ▸ frames) layout world

theorem returnLegacy_typed (wf : WellFormedProgram p) (typed : Words.State.Typed p.carrier s.machine t)
    (pending : LegacyPendingAt p s q) (result : value.type = q.operation.result) :
    Words.State.Typed p.carrier (returnLegacyState s value).machine t := by
  obtain ⟨values, row, controlEq, found, operation, _⟩ := pending.invocation
  cases s with | mk machine origins phase hardware episode stack cursor ordinal events used forwarding seen parked snapshot =>
   cases machine with | mk ctl a k w =>
    simp only at controlEq
    subst ctl
    exact invoke_legacy_return_typed wf typed found operation result

theorem returnLegacy_aligned (aligned : Origin.Aligned p s.machine s.origins)
    (pending : LegacyPendingAt p s q) :
    Origin.Aligned p (returnLegacyState s value).machine (returnLegacyState s value).origins := by
  obtain ⟨ty, args, located⟩ := pending.located
  rw [pending.1] at located
  exact ⟨aligned.function, .ret located, aligned.frames⟩

theorem SelectedPark.unique (a : SelectedPark p episode x) (b : SelectedPark p episode y) : x = y :=
  Option.some.inj ((selectedLocation_iff.mpr a).symm.trans (selectedLocation_iff.mpr b))
theorem SelectedPark.located (a : SelectedPark p episode location) : Origin.Located p location park := by
  cases a with | role found tail => exact Origin.designatedTail_located found tail.search
theorem ParkAt.exact (a : ParkAt p s location) :
    s.machine.control = .eval park ∧ Origin.Located p location park ∧
      location = s.origins.control ∧ location.function = s.machine.current.function :=
  ⟨a.2.2.2.eq, a.2.2.1.located, a.1, a.2.1⟩

theorem deliveryAt_iff : deliveryAt env s key = some d ↔ DeliveryAt env s key d := by
  constructor
  · intro found
    unfold deliveryAt at found
    split at found
    next => cases found
    next unused =>
      have unused' : s.deliveryUsed = false := by cases h : s.deliveryUsed <;> simp_all
      split at found
      next value supplied =>
        split at found
        next matching =>
          simp only [Option.some.injEq] at found
          subst d
          exact .matchKey unused' supplied matching
        next => cases found
      next => cases found
  · intro meaning
    cases meaning with | matchKey unused supplied matching => simp [deliveryAt, unused, supplied, matching]

theorem DeliveryAt.unique (a : DeliveryAt env s key x) (b : DeliveryAt env s key y) : x = y :=
  Option.some.inj ((deliveryAt_iff.mpr a).symm.trans (deliveryAt_iff.mpr b))
theorem DeliveryAt.unused (a : DeliveryAt env s key d) : s.deliveryUsed = false := by cases a; assumption
theorem DeliveryAt.landmark_eq (a : DeliveryAt env s key d) : d.landmark = key := by cases a; assumption
theorem DeliveryAt.valid (input : InputValid p env) (a : DeliveryAt env s key d) : DeliveryValid p d := by
  cases a with | matchKey _ supplied _ => exact input.delivery d supplied

theorem deliveryAt_none_iff : deliveryAt env s key = none ↔ ∀ d, ¬ DeliveryAt env s key d := by
  constructor
  · intro absent d present
    rw [deliveryAt_iff.mpr present] at absent
    cases absent
  · intro absent
    cases found : deliveryAt env s key with
    | none => rfl
    | some d => exact False.elim (absent d (deliveryAt_iff.mp found))

theorem observedPark_retains :
    (observedPark s location).machine = s.machine ∧
    (observedPark s location).origins = s.origins ∧
    (observedPark s location).hardware = s.hardware ∧
    (observedPark s location).readCursor = s.readCursor ∧
    (observedPark s location).revEvents = s.revEvents ∧
    (observedPark s location).episodeParkSeen = true ∧
    (observedPark s location).forwardingUsed = s.forwardingUsed := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.V2.Runtime
