import ANL.BootSummaryHeaderSpecs

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem rows_spec (bounded : ∀ view, summary = some view → SummaryEncodable p view) :
    Spec (array (row p) (summary.map SummaryView.rows |>.getD []))
      (toJson ((summary.map SummaryView.rows |>.getD []).map (Output.rowJson p))) 303138 := by
  cases summary with
  | none =>
      exact (Spec.array (perItem := 9472) (row p) (Output.rowJson p) [] (by simp)).mono (by decide)
  | some view =>
      have good := bounded view rfl
      have size := summary_rows_bound good
      exact (Spec.array (perItem := 9472) (row p) (Output.rowJson p) view.rows
        (fun item member => row_spec (good.2.2.2.2.2.2.1 item member))).mono (by omega)

 def retainedUnusedTarget (summary : Option SummaryView) : Json :=
  match summary with | none => .null | some view => unusedTarget view.unused

 theorem retained_unused_spec (bounded : ∀ view, summary = some view → SummaryEncodable p view) :
    Spec (optional unused (summary.map SummaryView.unused))
      (retainedUnusedTarget summary) 272640 := by
  cases summary with
  | none => exact Spec.null.mono (by decide)
  | some view => exact unused_spec (bounded view rfl).2.2.2.2.2.2.2

 theorem recovery_spec (ready : RecoveryReady p report) :
    Spec (recovery p report) (recoveryTarget p report) 630040 := by
  have identityReady : PrestartReady (some report.identity) := by
    intro item found
    cases found
    exact ready.identity_bound
  have finalSpec : Spec (optional final report.final)
      (Output.optionalJson Output.finalJson report.final) 41984 :=
    optional_spec _ _ (fun item found => final_spec ready.context (ready.final item found)) (by decide)
  have tail := FieldSpec.short_cons (key := "actions") (by unfold SafeASCII; decide) (by decide)
    (rows_spec ready.summary)
    (FieldSpec.short_cons (key := "final") (by unfold SafeASCII; decide) (by decide) finalSpec
      (FieldSpec.short_cons (key := "trace") (by unfold SafeASCII; decide) (by decide) Spec.null
        (FieldSpec.short_cons (key := "unused_input") (by unfold SafeASCII; decide) (by decide)
          (retained_unused_spec ready.summary) FieldSpec.nil rfl) rfl) rfl) rfl
  have fields := header_suffix_spec (status := report.status) identityReady ready.reason_bytes
    (header_counters ready.summary) tail rfl
  unfold recovery recoveryTarget
  exact (Spec.object fields (by
    change (["schema", "status", "reason", "semantic_revision", "ordinary_semantic_revision",
      "target_profile", "limits", "failure_action", "actions_requested", "actions_executed",
      "actions_unexecuted", "total_used", "actions", "final", "trace", "unused_input"] : List String).Nodup
    decide)).mono (by decide)

 theorem prestart_spec (ready : PrestartReady identity) (failure : Output.PrestartFailure) :
    Spec (prestart identity failure) (Output.prestartJson identity failure) 12288 := by
  have actions : Spec (array (fun _ : Unit => null) []) (toJson ([] : List Json)) 2 :=
    Spec.array (perItem := 4) (fun _ : Unit => null) (fun _ => Json.null) [] (by simp)
  have tail := FieldSpec.short_cons (key := "actions") (by unfold SafeASCII; decide) (by decide) actions
    (FieldSpec.short_cons (key := "final") (by unfold SafeASCII; decide) (by decide) Spec.null
      (FieldSpec.short_cons (key := "trace") (by unfold SafeASCII; decide) (by decide) Spec.null
        (FieldSpec.short_cons (key := "unused_input") (by unfold SafeASCII; decide) (by decide)
          Spec.null FieldSpec.nil rfl) rfl) rfl) rfl
  have fields := header_suffix_spec (status := failure.status) ready (prestart_reason_bytes failure) absent_counters tail rfl
  unfold prestart Output.prestartJson
  exact (Spec.object fields (by
    change (["schema", "status", "reason", "semantic_revision", "ordinary_semantic_revision",
      "target_profile", "limits", "failure_action", "actions_requested", "actions_executed",
      "actions_unexecuted", "total_used", "actions", "final", "trace", "unused_input"] : List String).Nodup
    decide)).mono (by decide)

end ANL.Boot.Reference.Summary
