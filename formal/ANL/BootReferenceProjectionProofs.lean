import ANL.BootReferenceProjectionValues
import ANL.BootRuntimeSavedPhase

namespace ANL.Boot.Reference.Projection
open ANL.Words ANL.Boot.Runtime ANL.Boot.Runtime.Session

 theorem SnapshotOf.compute (meaning : SnapshotOf raw view) : snapshotView raw = some view := by
  rcases view with ⟨episode, stack, origin, phase⟩
  rcases meaning with ⟨rfl, rfl, rfl, phase⟩
  simp [snapshotView, phase.compute]

 theorem snapshotView_iff : snapshotView raw = some view ↔ SnapshotOf raw view := by
  constructor
  · intro found
    simp only [snapshotView, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨phase, found, rfl⟩ := found
    exact ⟨rfl, rfl, rfl, phaseView_iff.mp found⟩
  · exact SnapshotOf.compute

 theorem OptionalSnapshotOf.compute (meaning : OptionalSnapshotOf raw view) : optionalSnapshotView raw = some view := by
  cases meaning with
  | absent => rfl
  | present snapshot => simp [optionalSnapshotView, snapshot.compute]

 theorem optionalSnapshotView_iff : optionalSnapshotView raw = some view ↔ OptionalSnapshotOf raw view := by
  constructor
  · intro found
    cases raw with
    | none => cases found; exact .absent
    | some snapshot =>
      change (snapshotView snapshot).map some = some view at found
      obtain ⟨projected, hs, eq⟩ := Option.map_eq_some_iff.mp found
      cases eq
      exact .present (snapshotView_iff.mp hs)
  · exact OptionalSnapshotOf.compute

 theorem FinalOf.compute (meaning : FinalOf result view) : finalView result = some view := by
  rcases view with ⟨episode, stack, origin, phase, hardware, cursor, ordinal, used, boot, seen, interrupted, next⟩
  rcases meaning with ⟨rfl, rfl, rfl, phase, rfl, rfl, rfl, rfl, rfl, rfl, interrupted, rfl⟩
  simp [finalView, phase.compute, interrupted.compute]

 theorem finalView_iff : finalView result = some view ↔ FinalOf result view := by
  constructor
  · intro found
    simp only [finalView, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨phase, phaseFound, interrupted, interruptedFound, rfl⟩ := found
    exact ⟨rfl, rfl, rfl, phaseView_iff.mp phaseFound, rfl, rfl, rfl, rfl, rfl, rfl,
      optionalSnapshotView_iff.mp interruptedFound, rfl⟩
  · exact FinalOf.compute

 theorem unusedView_meaning : UnusedOf env state (unusedView env state) := ⟨rfl, rfl, rfl, rfl, rfl⟩

 theorem UnusedOf.unique {state : Runtime.State} (meaning : UnusedOf env state view) : view = unusedView env state := by
  rcases view with ⟨total, consumed, remaining, delivery, status⟩
  rcases meaning with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

 theorem summaryView_meaning : SummaryOf request result (summaryView request result) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, unusedView_meaning⟩

 theorem SummaryOf.unique (meaning : SummaryOf request result view) : view = summaryView request result := by
  rcases view with ⟨failure, requested, executed, unexecuted, used, rows, unused⟩
  rcases meaning with ⟨rfl, rfl, rfl, rfl, rfl, rfl, meaning⟩
  cases meaning.unique
  rfl

 theorem identityView_meaning : IdentityOf p (identityView p) := ⟨rfl, rfl, rfl⟩

 theorem IdentityOf.unique (meaning : IdentityOf p view) : view = identityView p := by
  rcases view with ⟨revision, ordinary, profile⟩
  rcases meaning with ⟨rfl, rfl, rfl⟩
  rfl

 theorem ReasonStatus.compute (meaning : ReasonStatus reason status) : reasonStatus reason = status := by cases meaning <;> rfl

 theorem reasonStatus_iff : reasonStatus reason = status ↔ ReasonStatus reason status := by
  constructor
  · intro equal; cases reason <;> cases equal <;> constructor
  · exact ReasonStatus.compute

 theorem ResultStatus.compute (meaning : ResultStatus result status) : resultStatus result = status := by
  cases meaning with
  | done ending reason => simp [resultStatus, ending, reason.compute]
  | rejected ending | blocked ending | ineligible ending | invalid ending => simp [resultStatus, ending]

 theorem resultStatus_meaning : ResultStatus result (resultStatus result) := by
  unfold resultStatus
  split
  next ending => exact .done ending (reasonStatus_iff.mp rfl)
  next ending => exact .rejected ending
  next ending => exact .blocked ending
  next ending => exact .ineligible ending
  next ending => exact .invalid ending

 theorem TraceOf.unique (meaning : TraceOf state view) : view = ⟨state.revEvents⟩ := by
  rcases view with ⟨events⟩
  have equal : events = state.revEvents := List.reverse_inj.mp meaning
  cases equal
  rfl

 theorem fullReport_meaning (meaning : FinalOf result final) : ReportOf p request result (fullReport p request result final) :=
  ⟨identityView_meaning, resultStatus_meaning, rfl,
    ⟨_, rfl, summaryView_meaning⟩, ⟨_, rfl, meaning⟩, ⟨_, rfl, rfl⟩⟩

 theorem ReportOf.unique (meaning : ReportOf p request result report) :
    ∃ final, FinalOf result final ∧ report = fullReport p request result final := by
  rcases meaning with ⟨identity, status, reason, summary, final, trace⟩
  obtain ⟨sv, hs, sm⟩ := summary
  obtain ⟨fv, hf, fm⟩ := final
  obtain ⟨tv, ht, tm⟩ := trace
  have si := identity.unique
  have ss := status.compute
  have se := sm.unique
  have st := tm.unique
  refine ⟨fv, fm, ?_⟩
  cases report
  simp only at *
  subst_vars
  rfl

 theorem FullProjection.compute (meaning : FullProjection p request result report) : projectReport p request result = report := by
  obtain ⟨final, fm, rfl⟩ := meaning.meaning.unique
  have summary := meaning.summaryBound _ rfl
  have finalBound := meaning.finalBound _ rfl
  simp [projectReport, summary, fm.compute, finalBound]

 theorem projectReport_full_iff :
    projectReport p request result = report ∧ report.trace.isSome = true ↔ FullProjection p request result report := by
  constructor
  · rintro ⟨rfl, trace⟩
    unfold projectReport at trace ⊢
    by_cases summary : SummaryEncodable p (summaryView request result)
    · simp only [summary, ↓reduceIte] at trace ⊢
      cases finalFound : finalView result with
      | none => simp [finalFound, projectionFailure] at trace
      | some final =>
        simp only [finalFound] at trace ⊢
        by_cases bound : FinalEncodable p final
        · simp only [bound, ↓reduceIte] at trace ⊢
          refine ⟨fullReport_meaning (finalView_iff.mp finalFound), ?_, ?_⟩
          · intro v equal; cases equal; exact summary
          · intro v equal; cases equal; exact bound
        · simp [bound, projectionFailure] at trace
    · simp [summary, projectionFailure] at trace
  · intro meaning
    refine ⟨meaning.compute, ?_⟩
    obtain ⟨trace, equal, _⟩ := meaning.meaning.trace
    simp [equal]

 theorem projection_recovery_sound (empty : (projectReport p request result).trace = none) :
    ProjectionRecovery p request result (projectReport p request result) := by
  unfold projectReport at empty ⊢
  by_cases summary : SummaryEncodable p (summaryView request result)
  · simp only [summary, ↓reduceIte] at empty ⊢
    cases found : finalView result with
    | none =>
      simp only [found] at empty ⊢
      exact .final summaryView_meaning summary (fun final meaning _ => by have same := meaning.compute; rw [found] at same; contradiction)
    | some final =>
      simp only [found] at empty ⊢
      by_cases bound : FinalEncodable p final
      · simp [bound, fullReport] at empty
      · simp only [bound, ↓reduceIte]
        apply ProjectionRecovery.final summaryView_meaning summary
        intro other meaning bound
        have equal := Option.some.inj (found.symm.trans meaning.compute)
        cases equal
        exact ‹¬ FinalEncodable p final› bound
  · simp only [summary, ↓reduceIte]
    exact .summary summaryView_meaning summary

 theorem ProjectionRecovery.compute (meaning : ProjectionRecovery p request result report) : projectReport p request result = report := by
  cases meaning with
  | summary source bad =>
    cases source.unique
    simp [projectReport, bad]
  | final source summary bad =>
    cases source.unique
    unfold projectReport
    simp only [summary, ↓reduceIte]
    cases found : finalView result with
    | none => rfl
    | some final => simp [bad final (finalView_iff.mp found)]

 theorem projectionFailure_fields :
    (projectionFailure p summary).status = .error ∧
    (projectionFailure p summary).reason = "projection_shape_error" ∧
    (projectionFailure p summary).summary = summary ∧
    (projectionFailure p summary).final = none ∧ (projectionFailure p summary).trace = none := ⟨rfl, rfl, rfl, rfl, rfl⟩

 theorem checked_final_representable (wf : WellFormedProgram p) (input : InputValid p env)
    (started : Start p env first) (steps : BootStepsN p env n first result.state) :
    ∃ final, FinalOf result final := by
  have safe := checked_entry_safety wf input started steps
  have saved := checked_prefix_savedPhase wf input started steps
  obtain ⟨phase, phaseMeaning⟩ := phase_representable safe.localSafety.runtime.phase
  have interrupted : ∃ view, OptionalSnapshotOf result.state.interrupted view := by
    cases found : result.state.interrupted with
    | none => exact ⟨none, .absent⟩
    | some snapshot =>
      obtain ⟨before, equal, invariant⟩ := saved snapshot found
      obtain ⟨phase, meaning⟩ := phase_representable invariant
      exact ⟨some ⟨snapshot.episode, snapshot.stackRole, snapshot.origins.control, phase⟩,
        .present ⟨rfl, rfl, rfl, by simpa [equal, State.snapshot] using meaning⟩⟩
  obtain ⟨interrupted, interruptedMeaning⟩ := interrupted
  exact ⟨⟨result.state.episode, result.state.stackRole, result.state.origins.control, phase,
    result.state.hardware, result.state.readCursor, result.state.nextOrdinal, result.state.deliveryUsed,
    result.state.bootParkSeen, result.state.episodeParkSeen, interrupted, result.frontier.next⟩,
    rfl, rfl, rfl, phaseMeaning, rfl, rfl, rfl, rfl, rfl, rfl, interruptedMeaning, rfl⟩

end ANL.Boot.Reference.Projection
