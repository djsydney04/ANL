import ANL.BootSummaryEnvelopeSpecs

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

/-- Real execution succeeds at every sufficient prefix, with the same independently meaningful fragment. -/
 theorem Spec.prefix {value : Json} {before : Output.Buffer} (good : Spec write value bound)
    (room : before.bytes.size + bound ≤ ANL.Memory.Reference.maxOutputBytes - 1) :
    ∃ chunk after, Wire value chunk ∧ chunk.size ≤ bound ∧
      write before = .ok after ∧ after.bytes = before.bytes ++ chunk := by
  obtain ⟨chunk, meaning, size, append⟩ := good
  obtain ⟨after, executed, bytes⟩ := append before (by omega)
  exact ⟨chunk, after, meaning, size, executed, bytes⟩

 theorem Spec.at_empty {value : Json} (good : Spec write value bound)
    (room : bound ≤ ANL.Memory.Reference.maxOutputBytes - 1) :
    ∃ buffer, write ANL.Memory.Reference.Buffer.empty = .ok buffer ∧
      Wire value buffer.bytes ∧ buffer.bytes.size ≤ bound ∧ buffer.finish.size ≤ bound + 1 := by
  obtain ⟨chunk, buffer, meaning, size, executed, bytes⟩ := good.prefix (before := ANL.Memory.Reference.Buffer.empty) (by simpa [ANL.Memory.Reference.Buffer.empty] using room)
  have same : buffer.bytes = chunk := by simpa [ANL.Memory.Reference.Buffer.empty] using bytes
  refine ⟨buffer, executed, same ▸ meaning, same ▸ size, ?_⟩
  simp only [ANL.Memory.Reference.Buffer.finish, ByteArray.size_push, same]
  omega

 theorem recovery_success (ready : RecoveryReady p report) :
    ∃ buffer, recovery p report ANL.Memory.Reference.Buffer.empty = .ok buffer ∧
      Wire (recoveryTarget p report) buffer.bytes ∧
      buffer.bytes.size ≤ 630040 ∧ buffer.finish.size ≤ 630041 :=
  (recovery_spec ready).at_empty (by decide)

 theorem recovery_no_error (ready : RecoveryReady p report) :
    recovery p report ANL.Memory.Reference.Buffer.empty ≠ .error error := by
  obtain ⟨buffer, executed, _⟩ := recovery_success ready
  rw [executed]
  intro impossible
  cases impossible

 theorem projected_recovery_success (projected : projectForExport p request result = some report)
    (error : Output.ExportError) :
    ∃ buffer, recovery p (Output.exportFailure report error) ANL.Memory.Reference.Buffer.empty = .ok buffer ∧
      Wire (recoveryTarget p (Output.exportFailure report error)) buffer.bytes ∧
      buffer.bytes.size ≤ 630040 ∧ buffer.finish.size ≤ 630041 :=
  recovery_success (recovery_ready projected error)

 theorem recovery_below_summary_limit (ready : RecoveryReady p report)
    (executed : recovery p report ANL.Memory.Reference.Buffer.empty = .ok buffer) :
    buffer.finish.size ≤ 634147 ∧ buffer.finish.size < 1048576 := by
  obtain ⟨actual, success, _, _, size⟩ := recovery_success ready
  have equal : actual = buffer := Except.ok.inj (success.symm.trans executed)
  subst actual
  omega

 theorem prestart_success (ready : PrestartReady identity) (failure : Output.PrestartFailure) :
    ∃ buffer, prestart identity failure ANL.Memory.Reference.Buffer.empty = .ok buffer ∧
      Wire (Output.prestartJson identity failure) buffer.bytes ∧
      buffer.bytes.size ≤ 12288 ∧ buffer.finish.size ≤ 12289 :=
  (prestart_spec ready failure).at_empty (by decide)

 theorem prestart_no_error (ready : PrestartReady identity) (failure : Output.PrestartFailure) :
    prestart identity failure ANL.Memory.Reference.Buffer.empty ≠ .error error := by
  obtain ⟨buffer, executed, _⟩ := prestart_success ready failure
  rw [executed]
  intro impossible
  cases impossible

end ANL.Boot.Reference.Summary
