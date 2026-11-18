import ANL.BootReferenceProjectionProofs
import ANL.BootReferenceProjectionContext

namespace ANL.Boot.Reference.Projection
open ANL.Boot.Runtime ANL.Boot.Runtime.Session

 theorem final_frontier (meaning : SessionTo p env actions state previous index total rows result) :
    FrontierAt p result.previous result.state result.frontier := by
  induction meaning with
  | done view | rejected _ view | stopped _ _ _ _ view => cases view; assumption
  | advanced _ _ _ _ _ ih => exact ih

/-- Exhaustion intentionally imposes no absent-observation premise: resume0 can remain observed. -/
def ReasonObservations (p : Program) (env : Environment) (state : State) (reason : StopReason) : Prop :=
  (∀ kind, reason = .observed kind → Observation p state kind ∧ ¬ PendingDelivery env state) ∧
  (∀ kind, reason = .unobserved kind → Observation p state kind ∧ PendingDelivery env state)

 theorem stop_observations (meaning : StopAt p env state reason) : ReasonObservations p env state reason := by
  cases meaning <;> constructor <;> intro kind equal <;> cases equal <;> exact ⟨by assumption, by assumption⟩

 theorem action_observations (meaning : ActionTo p env action state result) :
    ReasonObservations p env result.state result.reason := by
  cases meaning with
  | run meaning | continued meaning => exact stop_observations meaning.stop
  | resumed meaning =>
    cases meaning with
    | advance _ rest => exact stop_observations rest.stop
    | exhausted | blocked | ineligible | invalid =>
      constructor <;> intro kind impossible <;> cases impossible

 theorem session_observations (meaning : SessionTo p env actions state previous index total rows result)
    (prior : ReasonObservations p env state (previous.getD .exhausted)) :
    ReasonObservations p env result.state result.previous := by
  induction meaning with
  | done view | rejected _ view => cases view; exact prior
  | stopped _ action _ _ view => cases view; exact action_observations action
  | advanced _ action _ _ _ ih => exact ih (action_observations action)

 theorem entry_observations (meaning : SessionTo p env actions first none 0 0 [] result) :
    ReasonObservations p env result.state result.previous := by
  apply session_observations meaning
  constructor <;> intro kind impossible <;> cases impossible

 theorem result_observed (meaning : SessionTo p env actions first none 0 0 [] result)
    (status : ResultStatus result .observed) :
    ∃ kind, Observation p result.state kind ∧ ¬ PendingDelivery env result.state := by
  cases status with
  | done _ reason =>
    have equal := reason.compute
    cases previous : result.previous <;> simp [previous, reasonStatus] at equal
    exact ⟨_, (entry_observations meaning).1 _ previous⟩

 theorem result_unobserved (meaning : SessionTo p env actions first none 0 0 [] result)
    (status : ResultStatus result .unobserved) :
    ∃ kind, Observation p result.state kind ∧ PendingDelivery env result.state := by
  cases status with
  | done _ reason =>
    have equal := reason.compute
    cases previous : result.previous <;> simp [previous, reasonStatus] at equal
    exact ⟨_, (entry_observations meaning).2 _ previous⟩

 theorem summary_counts (meaning : SessionTo p env request.actions first none 0 0 [] result)
    (view : SummaryOf request result summary) :
    summary.executed + summary.unexecuted = summary.requested ∧
    summary.totalUsed = usedRows summary.rows ∧ summary.totalUsed ≤ budgets request.actions ∧
    (∀ index, summary.failureAction = some index →
      index = summary.executed ∧ index < summary.requested) := by
  obtain ⟨added, rowsEq, totalEq, usedBound, _, countBound⟩ := meaning.summary
  simp only [List.nil_append, Nat.zero_add] at rowsEq totalEq
  have executed : result.rows.length ≤ request.actions.length := rowsEq ▸ countBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [view.executed, view.unexecuted, view.requested]; omega
  · rw [view.used, view.rows]; exact meaning.total
  · rw [view.used, totalEq]; exact usedBound
  · intro index failed
    rw [view.failure] at failed
    cases ending : result.ending <;> simp only [ending, Option.some.injEq, reduceCtorEq] at failed
    next other =>
      subst index
      have rejection := meaning.rejection_index ending
      simp only [List.length_nil, Nat.sub_zero, Nat.zero_add] at rejection
      rw [view.executed, view.requested]
      exact ⟨rejection.1, rejection.1 ▸ rejection.2⟩

 theorem unused_prefix (history : StateHistory p env state) (view : UnusedOf env state unused) :
    (readPayloads state.revEvents).reverse ++ unused.readsRemaining = env.reads ∧
    unused.readsConsumed = (readPayloads state.revEvents).length ∧
    unused.readsConsumed + unused.readsRemaining.length = unused.readsTotal := by
  refine ⟨?_, ?_, ?_⟩
  · rw [view.remaining]; exact history.reads.unused
  · rw [view.consumed]; exact history.read_count.symm
  · rw [view.consumed, view.remaining, view.total, List.length_drop]
    have bound := history.reads.bound
    omega

 theorem final_next (meaning : SessionTo p env actions first none 0 0 [] result)
    (view : FinalOf result final) :
    ∀ kind, final.nextAction = some kind ↔ Applicable p (some result.previous) result.state kind := by
  intro kind
  rw [view.next]
  exact (final_frontier meaning).next kind

 theorem row_observation (meaning : SessionTo p env actions first none 0 0 [] result)
    (present : row ∈ result.rows) :
    ∃ n middle m, BootStepsN p env n first middle ∧ BootStepsN p env m middle result.state ∧
      row.totalUsed = n ∧ row.eventEnd = middle.events.length ∧
      result.state.events.take row.eventEnd = middle.events ∧
      ObservationView p middle row.frontier.observation ∧
      (∀ kind, row.frontier.next = some kind ↔ Applicable p (some row.reason) middle kind) := by
  obtain ⟨n, middle, m, before, after, total, events, prefixEq, _, _, frontier⟩ := meaning.entry_row_events present
  exact ⟨n, middle, m, before, after, total, events, prefixEq, frontier.observation, frontier.next⟩

 theorem trace_offsets (meaning : SessionTo p env actions first none 0 0 [] result)
    (view : TraceOf result.state trace) (present : row ∈ result.rows) :
    ∃ n middle m, BootStepsN p env n first middle ∧ BootStepsN p env m middle result.state ∧
      row.totalUsed = n ∧ row.eventEnd = middle.events.length ∧
      trace.events.take row.eventEnd = middle.events ∧ row.readCursor = middle.readCursor ∧
      row.delivery = deliveryView env middle := by
  obtain ⟨n, middle, m, before, after, total, events, prefixEq, cursor, delivery, _⟩ := meaning.entry_row_events present
  exact ⟨n, middle, m, before, after, total, events, by rw [view]; exact prefixEq, cursor, delivery⟩

 theorem checked_session_prefix (checked : checkDocuments coreText requestText = .ok input)
    (ran : sessionRaw input.program input.request.environment input.request.actions = .ran result) :
    ∃ first, Start input.program input.request.environment first ∧
      BootStepsN input.program input.request.environment result.totalUsed first result.state ∧
      SafetyInvariant input.program input.request.environment result.state ∧
      result.totalUsed ≤ transitionLimit ∧ result.state.events.length ≤ result.totalUsed ∧
      result.state.nextOrdinal ≤ transitionLimit + 1 ∧ SavedPhase input.program result.state := by
  have wf := (checked_program checked).1
  have valid := checked_request checked
  obtain ⟨first, start, steps, safe, _, _, used, events, eventBound⟩ := sessionRaw_checked wf valid.input ran
  have total := valid.limits.totalBudget
  have ordinalPositive := safe.localSafety.runtime.ordinal
  have ordinalBound : result.state.nextOrdinal ≤ transitionLimit + 1 := by
    unfold State.eventCount at eventBound
    split at eventBound <;> omega
  exact ⟨first, start, steps, safe, Nat.le_trans used total, by omega, ordinalBound,
    checked_prefix_savedPhase wf valid.input start steps⟩

 theorem checked_report_prefix (checked : checkDocuments coreText requestText = .ok input)
    (ran : sessionRaw input.program input.request.environment input.request.actions = .ran result)
    (projected : FullProjection input.program input.request result report) :
    ∃ first summary final trace,
      Start input.program input.request.environment first ∧
      report.summary = some summary ∧ report.final = some final ∧ report.trace = some trace ∧
      BootStepsN input.program input.request.environment summary.totalUsed first result.state ∧
      summary.totalUsed ≤ transitionLimit ∧ trace.events = result.state.events ∧
      trace.events.length ≤ summary.totalUsed ∧ final.nextOrdinal ≤ transitionLimit + 1 ∧
      final.readCursor = summary.unused.readsConsumed := by
  obtain ⟨first, start, steps, _, used, events, ordinal, _⟩ := checked_session_prefix checked ran
  obtain ⟨summary, hs, sm⟩ := projected.meaning.summary
  obtain ⟨final, hf, fm⟩ := projected.meaning.final
  obtain ⟨trace, ht, tm⟩ := projected.meaning.trace
  exact ⟨first, summary, final, trace, start, hs, hf, ht, sm.used.symm ▸ steps,
    sm.used.symm ▸ used, tm, by rw [tm, sm.used]; exact events,
    fm.ordinal.symm ▸ ordinal, fm.cursor.trans sm.unused.consumed.symm⟩

 theorem checked_export_exists (checked : checkDocuments coreText requestText = .ok input) :
    projectForExport input.program input.request result = some (projectReport input.program input.request result) :=
  projectForExport_iff.mpr ⟨checked_documents_context checked, rfl⟩

 theorem exported_full_iff :
    projectForExport p request result = some report ∧ report.trace.isSome = true ↔
      ContextEncodable p ∧ FullProjection p request result report := by
  simp only [projectForExport_iff]
  constructor
  · rintro ⟨⟨context, projected⟩, trace⟩; exact ⟨context, projectReport_full_iff.mp ⟨projected, trace⟩⟩
  · rintro ⟨context, full⟩
    have pair := projectReport_full_iff.mpr full
    exact ⟨⟨context, pair.1⟩, pair.2⟩

 theorem projection_preserves_d (view : UnusedOf env state unused) : unused.delivery = env.delivery := view.delivery

end ANL.Boot.Reference.Projection
