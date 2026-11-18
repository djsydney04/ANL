import ANL.WordsReferenceBounds
import ANL.WordsReferenceOutput
import ANL.MemoryReferenceSafety

namespace ANL.Words.Reference
open ANL.Memory

 theorem response_in_range (plan : ResponsePlan) (value : Response) (h : plan.entries[i]? = some value) : plan.responses i = value :=
  ANL.Memory.Reference.response_in_range plan value h

 theorem response_default (plan : ResponsePlan) (h : plan.entries[i]? = none) : plan.responses i = plan.defaultResponse :=
  ANL.Memory.Reference.response_default plan h

 theorem decodeResponses_bound (h : decodeResponses entries = .ok values) : values.size ≤ maxResponses :=
  ANL.Memory.Reference.decodeResponses_bound h

 theorem planDocument_bound (h : planDocument doc = .ok plan) : plan.entries.size ≤ maxResponses :=
  ANL.Memory.Reference.planDocument_bound h

 theorem readPlan_bound (h : readPlan text = .ok plan) : plan.entries.size ≤ maxResponses :=
  ANL.Memory.Reference.readPlan_bound h

 theorem checkCore_accepted (h : checkCore text = .ok checked) :
    Wire.checkCoreDocument text = .ok checked.program := by
  unfold checkCore at h
  split at h
  · cases h
  next program hp => cases h; exact hp

 theorem checkCore_wellFormed (h : checkCore text = .ok checked) : WellFormedProgram checked.program :=
  (Wire.checkCoreDocument_iff.mp (checkCore_accepted h)).2

 theorem execute_iff : execute checked plan fuel budget = .ok result ↔
    budget ≤ maxTransitions ∧ fuel ≤ Tool.maxFuel ∧
    Tool.run checked.program plan.responses budget (Tool.initial checked.program fuel) = result := by
  by_cases hb : budget ≤ maxTransitions <;> by_cases hf : fuel ≤ Tool.maxFuel <;>
    simp [execute, Tool.start?, hb, hf]

 theorem execute_safe (h : execute checked plan fuel budget = .ok result) :
    State.Typed checked.program result.configuration.machine (.scalar (.legacy .i64)) := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  rw [← hr]
  exact Tool.run_entry_safe checked.wellFormed

 theorem execute_accounted (h : execute checked plan fuel budget = .ok result) :
    Tool.Accounted result.configuration.machine result.configuration.meter := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  rw [← hr]
  exact Tool.run_entry_accounted checked.wellFormed

 theorem execute_depth (h : execute checked plan fuel budget = .ok result) :
    Tool.DepthReachable checked.program plan.responses result.configuration.machine
      result.configuration.meter.depth result.configuration.meter.parents := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  rw [← hr]
  exact Tool.run_entry_depth checked.wellFormed

 theorem execute_prefix (h : execute checked plan fuel budget = .ok result) :
    ∃ n, n ≤ budget ∧ StepsN checked.program plan.responses n (initial checked.program)
      result.configuration.machine := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  rw [← hr]
  exact run_steps_bound (c := Tool.initial checked.program fuel)

 theorem execute_event_bound (h : execute checked plan fuel budget = .ok result) :
    result.configuration.machine.world.revTrace.length ≤ budget := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  rw [← hr]
  exact run_entry_event_bound

 theorem execute_no_invalid (h : execute checked plan fuel budget = .ok result) :
    result.configuration.machine.control ≠ .invalid := (execute_safe h).not_invalid

 theorem execute_completed (h : execute checked plan fuel budget = .ok (.completed last)) :
    Terminal last.machine := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  exact (Tool.run_completed_safe checked.wellFormed (entry_typed checked.wellFormed) hr).2

 theorem execute_exhausted (h : execute checked plan fuel budget = .ok (.exhausted last)) :
    StepsN checked.program plan.responses budget (initial checked.program) last.machine ∧
    isStopped last.machine = false := Tool.run_exhausted (execute_iff.mp h).2.2

 theorem execute_resource (h : execute checked plan fuel budget = .ok (.resourceLimit reason last)) :
    Steps checked.program plan.responses (initial checked.program) last.machine ∧
    isStopped last.machine = false := Tool.run_resource (execute_iff.mp h).2.2

 theorem checked_classification (h : execute checked plan fuel budget = .ok result) :
    ∃ completion, classify result = some completion := by
  cases result with
  | resourceLimit reason last => exact ⟨.resourceLimit reason, rfl⟩
  | exhausted last => exact ⟨.transitionLimit, rfl⟩
  | completed last =>
    have typed := execute_safe h
    have terminal := execute_completed h
    rcases last with ⟨⟨control, current, kont, world⟩, meter⟩
    cases terminal with
    | value =>
      have ty := (normal_cleanup typed).1
      rename_i value
      cases value with
      | scalar v =>
          cases v with
          | legacy v => cases v <;> simp_all [Val.type, ScalarVal.type, APL.Val.type, classify]
          | word v => simp [Val.type, ScalarVal.type] at ty
      | tuple fields => simp [Val.type] at ty
    | trap => exact ⟨_, rfl⟩

 theorem execute_normal_cleanup
    (h : execute checked plan fuel budget = .ok (.completed ⟨⟨.ret value, a, [], w⟩, m⟩)) :
    m.slots = 0 ∧ m.liveCells = 0 ∧ a.env = [] ∧ a.resources = [] ∧ w.owners = [] :=
  Tool.entry_normal_reservations checked.wellFormed (execute_iff.mp h).2.2

 theorem execute_event_origin (h : execute checked plan fuel budget = .ok result)
    (member : event ∈ result.configuration.machine.world.trace) :
    ∃ fn, checked.program.functions[event.site.function]? = some fn ∧
      fn.id = event.site.function ∧ event.site.heap < fn.body.heapSites.length := by
  obtain ⟨_, _, hr⟩ := execute_iff.mp h
  rw [← hr] at member
  exact Tool.entry_event_origin checked.wellFormed member

 theorem checked_report_present (h : execute checked plan fuel budget = .ok result) :
    ∃ trace, (resultReport checked.program fuel budget result).trace = some trace := by
  obtain ⟨completion, hc⟩ := checked_classification h
  simp [resultReport, hc]

 theorem resultReport_status (h : (resultReport p fuel budget result).trace = some trace) :
    (resultReport p fuel budget result).status = trace.completion.status := by
  unfold resultReport at h ⊢
  split at h
  · cases h
  next completion hc =>
    simp only [Option.some.injEq] at h
    cases h
    rfl

 theorem encoder_event_limit (h : report.trace = some trace)
    (over : maxEvents < trace.revEvents.length) : encode report = .error .events := by
  have blocked : eventsFit maxEvents trace.revEvents = false := by
    apply Bool.eq_false_iff.mpr
    intro fits
    have bound := eventsFit_iff.mp fits
    omega
  simp [encode, encodeBuffer, h, blocked, bind, Except.bind]
  rfl

 theorem append_preflight_failure (over : maxOutputBytes - 1 < buffer.bytes.size + chunk.size) :
    Buffer.append buffer chunk = .error .bytes :=
  ANL.Memory.Reference.append_preflight_failure over

 theorem append_exact (h : Buffer.append buffer chunk = .ok result) :
    result.bytes = buffer.bytes ++ chunk :=
  ANL.Memory.Reference.append_exact h

 theorem execute_zero (hf : fuel ≤ Tool.maxFuel) :
    execute checked plan fuel 0 = .ok (.exhausted (Tool.initial checked.program fuel)) := by
  simp [execute, Tool.start?, hf, Tool.run, Tool.initial, initial, isStopped, maxTransitions]

/-- A model trace result, not evidence that a native trace was observed. -/
def HeapFree (program : Program) : Prop :=
  ∀ (index : Nat) (fn : ANL.Words.Function), program.functions[index]? = some fn → fn.body.heapSites = []

theorem execute_heapFree_trace (h : execute checked plan fuel budget = .ok result)
    (pureProgram : HeapFree checked.program) : result.configuration.machine.world.trace = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro event member
  obtain ⟨fn, found, _, bound⟩ := execute_event_origin h member
  rw [pureProgram event.site.function fn found] at bound
  exact Nat.not_lt_zero _ bound

theorem trapName_injective : Function.Injective trapName := by
  intro left right equal
  cases left <;> cases right <;> simp_all [trapName]

theorem trapName_range (trap : Trap) : trapName trap ∈
    ["arithmetic_overflow", "division_by_zero", "invalid_shift", "invalid_length", "index_out_of_bounds"] := by
  cases trap <;> simp [trapName]

end ANL.Words.Reference
