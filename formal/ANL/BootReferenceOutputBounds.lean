import ANL.BootReferenceOutputMinimal

namespace ANL.Boot.Reference.Output
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem countFits_iff {bound : Nat} : countFits bound values = true ↔ values.length ≤ bound := by
  induction bound generalizing values with
  | zero => cases values <;> simp [countFits]
  | succ n ih => cases values <;> simp [countFits, ih, Nat.succ_le_succ_iff]

 theorem buffer_finish_bound (buffer : Buffer) : buffer.finish.size ≤ outputLimit :=
  ANL.Memory.Reference.buffer_finish_bound buffer


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

 theorem encodePrestart_bound (failure : PrestartFailure) : (encodePrestart knowledge failure).bytes.size ≤ outputLimit := by
  unfold encodePrestart
  dsimp only
  split
  · exact buffer_finish_bound _
  · exact minimal_bound _ _

 theorem buffer_finish_lf (buffer : Buffer) : ∃ before : ByteArray, buffer.finish = before.push 10 ∧ before.size < outputLimit := by
  refine ⟨buffer.bytes, rfl, ?_⟩
  have bound := buffer.bounded
  change buffer.bytes.size ≤ 8388608 - 1 at bound
  change buffer.bytes.size < 8388608
  omega

 theorem minimal_lf : ∃ before : ByteArray, minimalBytes known reason = before.push 10 ∧ before.size < outputLimit := by
  refine ⟨(minimalText known reason).toUTF8, rfl, ?_⟩
  have bound := minimal_bound known reason
  simp only [minimalBytes, ByteArray.size_push] at bound
  omega

 theorem encodeProjected_lf : ∃ before : ByteArray, (encodeProjected p report).bytes = before.push 10 ∧ before.size < outputLimit := by
  unfold encodeProjected
  split
  · exact buffer_finish_lf _
  · split
    · exact buffer_finish_lf _
    · exact minimal_lf

 theorem encodeResult_lf : ∃ before : ByteArray, (encodeResult p request result).bytes = before.push 10 ∧ before.size < outputLimit := by
  unfold encodeResult
  split
  · exact minimal_lf
  · exact encodeProjected_lf

 theorem encodePrestart_lf (failure : PrestartFailure) : ∃ before : ByteArray, (encodePrestart knowledge failure).bytes = before.push 10 ∧ before.size < outputLimit := by
  unfold encodePrestart
  dsimp only
  split
  · exact buffer_finish_lf _
  · exact minimal_lf

 theorem exportFailure_retained :
    (exportFailure report error).identity = report.identity ∧
    (exportFailure report error).summary = report.summary ∧
    (exportFailure report error).final = report.final ∧
    (exportFailure report error).trace = none ∧ (exportFailure report error).status = .error := ⟨rfl, rfl, rfl, rfl, rfl⟩

 theorem invalid_context_minimal (bad : ¬ ContextEncodable p) :
    encodeResult p request result = minimal false .projectionShape := by
  simp [encodeResult, projectForExport_reject bad]

 theorem knownIdentity_valid (found : knownIdentity knowledge = some identity) : IdentityEncodable identity := by
  cases knowledge with
  | none => cases found
  | some p =>
    by_cases context : ContextEncodable p
    · simp only [knownIdentity, context, ↓reduceIte, Option.some.injEq] at found
      subst identity
      exact ⟨rfl, rfl, rfl⟩
    · simp [knownIdentity, context] at found

 theorem prestart_status (failure : PrestartFailure) :
    failure.status = .rejected ∨ failure.status = .resourceLimit ∨ failure.status = .error := by
  cases failure with
  | core error | request error => cases kind : error.kind <;> simp [PrestartFailure.status, kind]
  | invocation | inputIO | internal => exact .inr (.inr rfl)

 theorem appendEvents_bad (bad : ¬ EventEncodable p event) :
    appendEvents p (event :: rest) first buffer = .error .shape := by
  simp [appendEvents, bad, throw, throwThe, bind, Except.bind]
  rfl

 theorem event_count_precedes_encoding (present : report.trace = some trace)
    (over : transitionLimit < trace.revEvents.length) : encodeBuffer p report = .error .events := by
  have bad : countFits transitionLimit trace.revEvents = false :=
    Bool.eq_false_iff.mpr (fun h => Nat.not_le.mpr over (countFits_iff.mp h))
  simp [encodeBuffer, present, bad, throw, throwThe, bind, Except.bind]
  rfl

 theorem encodeProjected_nonerror (good : (encodeProjected p report).status ≠ .error) :
    ∃ buffer, encodeBuffer p report = .ok buffer ∧ (encodeProjected p report).status = report.status ∧
      (encodeProjected p report).bytes = buffer.finish := by
  cases encoded : encodeBuffer p report with
  | ok buffer => exact ⟨buffer, rfl, by simp [encodeProjected, encoded], by simp [encodeProjected, encoded]⟩
  | error error =>
    have bad : (encodeProjected p report).status = .error := by
      simp only [encodeProjected, encoded]
      cases fallback : encodeBuffer p (exportFailure report error) <;> rfl
    exact False.elim (good bad)

 theorem projection_error_without_trace (absent : (projectReport p request result).trace = none) :
    (projectReport p request result).status = .error := by
  generalize projected : projectReport p request result = report at absent ⊢
  have recovery := projection_recovery_sound (projected ▸ absent)
  rw [projected] at recovery
  cases recovery <;> rfl

 theorem encodeResult_nonerror (good : (encodeResult p request result).status ≠ .error) :
    ∃ report buffer, projectForExport p request result = some report ∧
      ContextEncodable p ∧ FullProjection p request result report ∧
      encodeBuffer p report = .ok buffer ∧ (encodeResult p request result).status = report.status ∧
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

end ANL.Boot.Reference.Output
