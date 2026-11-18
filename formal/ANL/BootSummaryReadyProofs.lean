import ANL.BootSummaryEnvelope

namespace ANL.Boot.Reference.Summary
open ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem projected_retained_bounds :
    (∀ view, (projectReport p request result).summary = some view → SummaryEncodable p view) ∧
    (∀ view, (projectReport p request result).final = some view → FinalEncodable p view) ∧
    ((projectReport p request result).summary = none → (projectReport p request result).final = none) := by
  by_cases summary : SummaryEncodable p (summaryView request result)
  · unfold projectReport
    simp only [summary, ↓reduceIte]
    cases found : finalView result with
    | none => simp [projectionFailure, summary]
    | some view =>
      by_cases finalBound : FinalEncodable p view
      · simp [finalBound, fullReport, summary]
      · simp [finalBound, projectionFailure, summary]
  · simp [projectReport, summary, projectionFailure]

 theorem recovery_ready (projected : projectForExport p request result = some report)
    (error : Output.ExportError) : RecoveryReady p (Output.exportFailure report error) := by
  obtain ⟨context, same⟩ := projectForExport_iff.mp projected
  have guards := projected_retained_bounds (p := p) (request := request) (result := result)
  rw [same] at guards
  refine ⟨context, ?_, rfl, rfl, ⟨error, rfl⟩, guards.1, guards.2.1, guards.2.2⟩
  change report.identity = identityView p
  rw [← same, projectReport_identity]

 theorem RecoveryReady.identity_bound (ready : RecoveryReady p report) : IdentityEncodable report.identity := by
  rw [ready.identity]
  exact ready.context.identity

 theorem RecoveryReady.reason_bytes (ready : RecoveryReady p report) : report.reason.toUTF8.size ≤ 1024 := by
  obtain ⟨error, equal⟩ := ready.reason
  rw [equal]
  cases error <;> decide

 theorem knownIdentity_ready : PrestartReady (Output.knownIdentity knowledge) := by
  intro identity found
  exact Output.knownIdentity_valid found

 theorem prestart_reason_bytes (failure : Output.PrestartFailure) : failure.reason.toUTF8.size ≤ 1024 := by
  exact Text.reason_bytes _

 theorem summary_rows_bound (bounded : SummaryEncodable p view) : view.rows.length ≤ 32 := by
  have h1 := bounded.2.1
  have h2 := bounded.2.2.1
  have h3 := bounded.2.2.2.1
  change view.requested ≤ 32 at h1
  omega

 theorem summary_counts_bound (bounded : SummaryEncodable p view) :
    view.requested ≤ 32 ∧ view.executed ≤ 32 ∧ view.unexecuted ≤ 32 ∧ view.totalUsed ≤ 65536 := by
  have h1 := bounded.2.1
  have h2 := bounded.2.2.2.1
  have h3 := bounded.2.2.2.2.1
  change view.requested ≤ 32 at h1
  change view.totalUsed ≤ 65536 at h3
  omega

 theorem summary_failure_bound (bounded : SummaryEncodable p view)
    (present : view.failureAction = some index) : index < 32 := by
  have failure := bounded.2.2.2.2.2.1 index (by simpa using present)
  have requested := bounded.2.1
  change view.requested ≤ 32 at requested
  omega

 theorem unused_reads_bound (bounded : UnusedEncodable view) : view.readsRemaining.length ≤ 65536 := by
  have total := bounded.1
  have length := bounded.2.2.1
  change view.readsTotal ≤ 65536 at total
  omega

end ANL.Boot.Reference.Summary
