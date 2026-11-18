import ANL.BootSummaryRowSpecs

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem limits_spec : Spec limits Output.limitsJson 2048 := by
  unfold limits Output.limitsJson
  exact (Spec.object (FieldSpec.cons (key := "id") (by unfold SafeASCII; decide) (Spec.ascii (value := "anl-boot-reference-limits-v1") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "core_bytes") (by unfold SafeASCII; decide) (Spec.natural (n := 1048576) (by decide)) (FieldSpec.cons (key := "core_json_depth") (by unfold SafeASCII; decide) (Spec.natural (n := 1024) (by decide)) (FieldSpec.cons (key := "core_logical_depth") (by unfold SafeASCII; decide) (Spec.natural (n := 128) (by decide)) (FieldSpec.cons (key := "request_bytes") (by unfold SafeASCII; decide) (Spec.natural (n := 1048576) (by decide)) (FieldSpec.cons (key := "request_json_depth") (by unfold SafeASCII; decide) (Spec.natural (n := 16) (by decide)) (FieldSpec.cons (key := "declarations") (by unfold SafeASCII; decide) (Spec.natural (n := declarationLimit) (by decide)) (FieldSpec.cons (key := "term_nodes") (by unfold SafeASCII; decide) (Spec.natural (n := nodeLimit) (by decide)) (FieldSpec.cons (key := "parameters") (by unfold SafeASCII; decide) (Spec.natural (n := arityLimit) (by decide)) (FieldSpec.cons (key := "call_arguments") (by unfold SafeASCII; decide) (Spec.natural (n := arityLimit) (by decide)) (FieldSpec.cons (key := "reads") (by unfold SafeASCII; decide) (Spec.natural (n := readLimit) (by decide)) (FieldSpec.cons (key := "delivery_origin_edges") (by unfold SafeASCII; decide) (Spec.natural (n := originLimit) (by decide)) (FieldSpec.cons (key := "output_origin_edges") (by unfold SafeASCII; decide) (Spec.natural (n := originLimit) (by decide)) (FieldSpec.cons (key := "actions") (by unfold SafeASCII; decide) (Spec.natural (n := actionLimit) (by decide)) (FieldSpec.cons (key := "action_transitions") (by unfold SafeASCII; decide) (Spec.natural (n := transitionLimit) (by decide)) (FieldSpec.cons (key := "total_transitions") (by unfold SafeASCII; decide) (Spec.natural (n := transitionLimit) (by decide)) (FieldSpec.cons (key := "events") (by unfold SafeASCII; decide) (Spec.natural (n := transitionLimit) (by decide)) (FieldSpec.cons (key := "output_bytes") (by unfold SafeASCII; decide) (Spec.natural (n := Output.outputLimit) (by decide)) (FieldSpec.cons (key := "reason_utf8_bytes") (by unfold SafeASCII; decide) (Spec.natural (n := 1024) (by decide)) FieldSpec.nil rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) (by change (["id", "core_bytes", "core_json_depth", "core_logical_depth", "request_bytes", "request_json_depth", "declarations", "term_nodes", "parameters", "call_arguments", "reads", "delivery_origin_edges", "output_origin_edges", "actions", "action_transitions", "total_transitions", "events", "output_bytes", "reason_utf8_bytes"] : List String).Nodup; decide)).mono (by decide)

 theorem FieldSpec.short_cons {value : Json} (safe : SafeASCII key) (keyBound : key.toUTF8.size ≤ 64)
    (head : Spec write value valueBound) (tail : FieldSpec writes values restBound)
    (shape : writes.isEmpty = values.isEmpty) :
    FieldSpec ((key, write) :: writes) ((key, value) :: values) (68 + valueBound + restBound) := by
  exact (FieldSpec.cons safe head tail shape).mono (by omega)

 def HeaderCounters (summary : Option SummaryView) : Prop :=
  ∀ view, summary = some view → view.requested ≤ 32 ∧ view.executed ≤ 32 ∧
    view.unexecuted ≤ 32 ∧ view.totalUsed ≤ 65536 ∧
    ∀ ident, view.failureAction = some ident → ident < 32

 theorem header_counters (bounded : ∀ view, summary = some view → SummaryEncodable p view) : HeaderCounters summary := by
  intro view found
  have counts := summary_counts_bound (bounded view found)
  exact ⟨counts.1, counts.2.1, counts.2.2.1, counts.2.2.2, fun _ present => summary_failure_bound (bounded view found) present⟩

 theorem absent_counters : HeaderCounters none := by intro view found; cases found

 theorem identity_revision_spec (ready : PrestartReady identity) :
    Spec (optional (ascii ∘ Identity.semanticRevision) identity)
      (Output.optionalJson (toJson ∘ Identity.semanticRevision) identity) 64 := by
  apply optional_spec _ _ ?_ (by decide)
  intro item found
  have bound := ready item found
  change Spec (ascii item.semanticRevision) (toJson item.semanticRevision) 64
  rw [bound.1]
  exact (Spec.ascii (by unfold SafeASCII; decide)).mono (by decide)

 theorem identity_ordinary_spec (ready : PrestartReady identity) :
    Spec (optional (ascii ∘ Identity.ordinaryRevision) identity)
      (Output.optionalJson (toJson ∘ Identity.ordinaryRevision) identity) 64 := by
  apply optional_spec _ _ ?_ (by decide)
  intro item found
  have bound := ready item found
  change Spec (ascii item.ordinaryRevision) (toJson item.ordinaryRevision) 64
  rw [bound.2.1]
  exact (Spec.ascii (by unfold SafeASCII; decide)).mono (by decide)

 theorem identity_profile_spec (ready : PrestartReady identity) :
    Spec (optional (ascii ∘ Identity.targetProfile) identity)
      (Output.optionalJson (toJson ∘ Identity.targetProfile) identity) 64 := by
  apply optional_spec _ _ ?_ (by decide)
  intro item found
  have bound := ready item found
  change Spec (ascii item.targetProfile) (toJson item.targetProfile) 64
  rw [bound.2.2]
  exact (Spec.ascii (by unfold SafeASCII; decide)).mono (by decide)

 theorem header_suffix_spec (identityReady : PrestartReady identity) (reasonBound : reason.toUTF8.size ≤ 1024)
    (counts : HeaderCounters summary) (tail : FieldSpec writes values bound)
    (shape : writes.isEmpty = values.isEmpty) :
    FieldSpec (header identity status reason summary ++ writes)
      (Output.headerFields identity status reason summary ++ values) (12000 + bound) := by
  have schema : Spec (ascii "anl-boot-reference-run-v1") (toJson "anl-boot-reference-run-v1") 64 :=
    (Spec.ascii (by unfold SafeASCII; decide)).mono (by decide)
  have reasonSpec : Spec (diagnostic reason) (toJson reason) 6146 := (Spec.diagnostic reason).mono (by omega)
  have failureSpec : Spec (match summary with | none => null | some view => optional natural view.failureAction)
      (match summary with | none => Json.null | some view => Output.optionalJson toJson view.failureAction) 20 := by
    cases summary with
    | none => exact Spec.null.mono (by decide)
    | some view =>
      apply optional_spec _ _ ?_ (by decide)
      intro ident found
      apply Spec.natural
      have bound := (counts view rfl).2.2.2.2 ident found
      omega
  have requestedSpec : Spec (optional (natural ∘ SummaryView.requested) summary)
      (Output.optionalJson (toJson ∘ SummaryView.requested) summary) 20 := by
    apply optional_spec _ _ ?_ (by decide)
    intro item found
    apply Spec.natural
    have bound := (counts item found).1
    omega
  have executedSpec : Spec (optional (natural ∘ SummaryView.executed) summary)
      (Output.optionalJson (toJson ∘ SummaryView.executed) summary) 20 := by
    apply optional_spec _ _ ?_ (by decide)
    intro item found
    apply Spec.natural
    have bound := (counts item found).2.1
    omega
  have unexecutedSpec : Spec (optional (natural ∘ SummaryView.unexecuted) summary)
      (Output.optionalJson (toJson ∘ SummaryView.unexecuted) summary) 20 := by
    apply optional_spec _ _ ?_ (by decide)
    intro item found
    apply Spec.natural
    have bound := (counts item found).2.2.1
    omega
  have usedSpec : Spec (optional (natural ∘ SummaryView.totalUsed) summary)
      (Output.optionalJson (toJson ∘ SummaryView.totalUsed) summary) 20 := by
    apply optional_spec _ _ ?_ (by decide)
    intro item found
    apply Spec.natural
    have bound := (counts item found).2.2.2.1
    omega
  simp only [header, Output.headerFields, List.cons_append, List.nil_append]
  have result := (FieldSpec.short_cons (key := "schema") (by unfold SafeASCII; decide) (by decide) schema (FieldSpec.short_cons (key := "status") (by unfold SafeASCII; decide) (by decide) (status_spec status) (FieldSpec.short_cons (key := "reason") (by unfold SafeASCII; decide) (by decide) reasonSpec (FieldSpec.short_cons (key := "semantic_revision") (by unfold SafeASCII; decide) (by decide) (identity_revision_spec identityReady) (FieldSpec.short_cons (key := "ordinary_semantic_revision") (by unfold SafeASCII; decide) (by decide) (identity_ordinary_spec identityReady) (FieldSpec.short_cons (key := "target_profile") (by unfold SafeASCII; decide) (by decide) (identity_profile_spec identityReady) (FieldSpec.short_cons (key := "limits") (by unfold SafeASCII; decide) (by decide) limits_spec (FieldSpec.short_cons (key := "failure_action") (by unfold SafeASCII; decide) (by decide) failureSpec (FieldSpec.short_cons (key := "actions_requested") (by unfold SafeASCII; decide) (by decide) requestedSpec (FieldSpec.short_cons (key := "actions_executed") (by unfold SafeASCII; decide) (by decide) executedSpec (FieldSpec.short_cons (key := "actions_unexecuted") (by unfold SafeASCII; decide) (by decide) unexecutedSpec (FieldSpec.short_cons (key := "total_used") (by unfold SafeASCII; decide) (by decide) usedSpec tail shape) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl).mono (bound' := 12000 + bound) (by omega)
  cases summary <;> exact result

end ANL.Boot.Reference.Summary
