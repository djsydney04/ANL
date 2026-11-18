import ANL.BootSummaryOutput

namespace ANL.Boot.Reference.Output.Total
open ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem first_success (success : Output.encodeBuffer p report = .ok buffer) :
    encodeProjected p report = ⟨report.status, buffer.finish⟩ := by
  simp [encodeProjected, success]

 theorem first_success_unchanged (success : Output.encodeBuffer p report = .ok buffer) :
    encodeProjected p report = Output.encodeProjected p report := by
  simp [encodeProjected, Output.encodeProjected, success]

/-- Guarded recovery cannot lose summaries to the old defensive summary-limit envelope. -/
 theorem projected_first_failure (projected : projectForExport p request result = some report)
    (failed : Output.encodeBuffer p report = .error firstError) :
    ∃ buffer, Summary.recovery p (Output.exportFailure report firstError)
        ANL.Memory.Reference.Buffer.empty = .ok buffer ∧
      Summary.Wire (Summary.recoveryTarget p (Output.exportFailure report firstError)) buffer.bytes ∧
      buffer.finish.size ≤ 630041 ∧ encodeProjected p report = ⟨.error, buffer.finish⟩ := by
  obtain ⟨buffer, executed, meaning, _, size⟩ := Summary.projected_recovery_success projected firstError
  exact ⟨buffer, executed, meaning, size, by simp [encodeProjected, failed, executed]⟩

 theorem encodeResult_recovery (projected : projectForExport p request result = some report)
    (failed : Output.encodeBuffer p report = .error firstError) :
    ∃ buffer : Buffer, Summary.Wire (Summary.recoveryTarget p (Output.exportFailure report firstError)) buffer.bytes ∧
      buffer.finish.size ≤ 630041 ∧ encodeResult p request result = ⟨.error, buffer.finish⟩ := by
  obtain ⟨buffer, _, meaning, size, encoded⟩ := projected_first_failure projected failed
  exact ⟨buffer, meaning, size, by simp [encodeResult, projected, encoded]⟩

 theorem encodePrestart_success (failure : PrestartFailure) :
    ∃ buffer, Summary.prestart (Output.knownIdentity knowledge) failure
        ANL.Memory.Reference.Buffer.empty = .ok buffer ∧
      Summary.Wire (Output.prestartJson (Output.knownIdentity knowledge) failure) buffer.bytes ∧
      buffer.finish.size ≤ 12289 ∧ encodePrestart knowledge failure = ⟨failure.status, buffer.finish⟩ := by
  obtain ⟨buffer, executed, meaning, _, size⟩ :=
    Summary.prestart_success Summary.knownIdentity_ready failure
  exact ⟨buffer, executed, meaning, size, by simp [encodePrestart, executed]⟩

 theorem encodePrestart_status (failure : PrestartFailure) :
    (encodePrestart knowledge failure).status = failure.status := by
  obtain ⟨_, _, _, _, encoded⟩ := encodePrestart_success (knowledge := knowledge) failure
  rw [encoded]

 theorem encodePrestart_small (failure : PrestartFailure) :
    (encodePrestart knowledge failure).bytes.size ≤ 12289 := by
  obtain ⟨_, _, _, size, encoded⟩ := encodePrestart_success (knowledge := knowledge) failure
  simpa [encoded] using size

 theorem encodeProjected_bound : (encodeProjected p report).bytes.size ≤ outputLimit := by
  unfold encodeProjected
  split
  · exact buffer_finish_bound _
  · split
    · exact buffer_finish_bound _
    · exact minimal_bound _ _

 theorem encodeResult_bound : (encodeResult p request result).bytes.size ≤ outputLimit := by
  unfold encodeResult
  split
  · exact minimal_bound _ _
  · exact encodeProjected_bound

 theorem encodePrestart_bound (failure : PrestartFailure) :
    (encodePrestart knowledge failure).bytes.size ≤ outputLimit := by
  have small := encodePrestart_small (knowledge := knowledge) failure
  change (encodePrestart knowledge failure).bytes.size ≤ 8388608
  omega

 theorem encodeProjected_lf : ∃ before : ByteArray,
    (encodeProjected p report).bytes = before.push 10 ∧ before.size < outputLimit := by
  unfold encodeProjected
  split
  · exact buffer_finish_lf _
  · split
    · exact buffer_finish_lf _
    · exact minimal_lf

 theorem encodeResult_lf : ∃ before : ByteArray,
    (encodeResult p request result).bytes = before.push 10 ∧ before.size < outputLimit := by
  unfold encodeResult
  split
  · exact minimal_lf
  · exact encodeProjected_lf

 theorem encodePrestart_lf (failure : PrestartFailure) : ∃ before : ByteArray,
    (encodePrestart knowledge failure).bytes = before.push 10 ∧ before.size < outputLimit := by
  obtain ⟨buffer, _, _, _, encoded⟩ := encodePrestart_success (knowledge := knowledge) failure
  rw [encoded]
  exact buffer_finish_lf buffer

 theorem invalid_context_minimal (bad : ¬ ContextEncodable p) :
    encodeResult p request result = Output.minimal false .projectionShape := by
  simp [encodeResult, projectForExport_reject bad]

 theorem encodeProjected_nonerror (good : (encodeProjected p report).status ≠ .error) :
    ∃ buffer, Output.encodeBuffer p report = .ok buffer ∧
      (encodeProjected p report).status = report.status ∧ (encodeProjected p report).bytes = buffer.finish := by
  cases encoded : Output.encodeBuffer p report with
  | ok buffer => exact ⟨buffer, rfl, by simp [encodeProjected, encoded], by simp [encodeProjected, encoded]⟩
  | error error =>
    have bad : (encodeProjected p report).status = .error := by
      simp only [encodeProjected, encoded]
      cases fallback : Summary.recovery p (Output.exportFailure report error) ANL.Memory.Reference.Buffer.empty <;> rfl
    exact False.elim (good bad)

 theorem encodeResult_nonerror (good : (encodeResult p request result).status ≠ .error) :
    ∃ report buffer, projectForExport p request result = some report ∧
      ContextEncodable p ∧ FullProjection p request result report ∧
      Output.encodeBuffer p report = .ok buffer ∧ (encodeResult p request result).status = report.status ∧
      (encodeResult p request result).bytes = buffer.finish := by
  cases projected : projectForExport p request result with
  | none => simp [encodeResult, projected, minimal] at good
  | some report =>
    have chosen : encodeResult p request result = encodeProjected p report := by simp [encodeResult, projected]
    obtain ⟨buffer, encoded, status, bytes⟩ := encodeProjected_nonerror (chosen ▸ good)
    obtain ⟨context, source⟩ := projectForExport_iff.mp projected
    have full : FullProjection p request result report := by
      apply projectReport_full_iff.mp
      refine ⟨source, ?_⟩
      cases trace : report.trace with
      | some value => rfl
      | none =>
        have error := projection_error_without_trace (source ▸ trace)
        have reportError : report.status = .error := source ▸ error
        exact False.elim (good (chosen ▸ status.trans reportError))
    exact ⟨report, buffer, rfl, context, full, encoded, chosen ▸ status, chosen ▸ bytes⟩

end ANL.Boot.Reference.Output.Total
