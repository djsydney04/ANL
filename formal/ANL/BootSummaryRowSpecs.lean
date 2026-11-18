import ANL.BootSummaryPhaseSpecs

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem landmark_spec (bounded : LandmarkEncodable view) :
    Spec (landmark view) (Output.landmarkJson view) 8576 := by
  cases view with
  | beforePrimitive ordinal declaration =>
    simp only [landmark, Output.landmarkJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "before_primitive") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "ordinal") (by unfold SafeASCII; decide) (Spec.natural (n := ordinal) (by exact bounded.2.1)) (FieldSpec.cons (key := "declaration") (by unfold SafeASCII; decide) (Spec.natural (n := declaration) (by exact declaration_max bounded.2.2)) FieldSpec.nil rfl) rfl) rfl) (by change (["kind", "ordinal", "declaration"] : List String).Nodup; decide)).mono (by decide)
  | afterPrimitive ordinal declaration =>
    simp only [landmark, Output.landmarkJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "after_primitive") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "ordinal") (by unfold SafeASCII; decide) (Spec.natural (n := ordinal) (by exact bounded.2.1)) (FieldSpec.cons (key := "declaration") (by unfold SafeASCII; decide) (Spec.natural (n := declaration) (by exact declaration_max bounded.2.2)) FieldSpec.nil rfl) rfl) rfl) (by change (["kind", "ordinal", "declaration"] : List String).Nodup; decide)).mono (by decide)
  | bootPark loc =>
    simp only [landmark, Output.landmarkJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "boot_park") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec bounded.1) FieldSpec.nil rfl) rfl) (by change (["kind", "origin"] : List String).Nodup; decide)).mono (by decide)

 theorem delivery_spec (bounded : DeliveryEncodable view) :
    Spec (delivery view) (Output.deliveryJson view) 8832 := by
  unfold delivery Output.deliveryJson
  exact (Spec.object (FieldSpec.cons (key := "landmark") (by unfold SafeASCII; decide) (landmark_spec bounded.1) (FieldSpec.cons (key := "scause") (by unfold SafeASCII; decide) (Spec.word (word_max bounded.2.1)) (FieldSpec.cons (key := "sepc") (by unfold SafeASCII; decide) (Spec.word (word_max bounded.2.2.1)) (FieldSpec.cons (key := "stval") (by unfold SafeASCII; decide) (Spec.word (word_max bounded.2.2.2)) FieldSpec.nil rfl) rfl) rfl) rfl) (by change (["landmark", "scause", "sepc", "stval"] : List String).Nodup; decide)).mono (by decide)

 theorem observation_spec (bounded : ObservationEncodable p view) :
    Spec (observation p view) (Output.observationJson p view) 8576 := by
  cases view with
  | handlerEntry episode =>
    simp only [observation, Output.observationJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "handler_entry") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "episode") (by unfold SafeASCII; decide) (episode_spec episode) (FieldSpec.cons (key := "function") (by unfold SafeASCII; decide) (Spec.natural (n := (episode.function p)) (by exact declaration_max bounded)) FieldSpec.nil rfl) rfl) rfl) (by change (["kind", "episode", "function"] : List String).Nodup; decide)).mono (by decide)
  | park episode loc =>
    simp only [observation, Output.observationJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "park") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "episode") (by unfold SafeASCII; decide) (episode_spec episode) (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec bounded) FieldSpec.nil rfl) rfl) rfl) (by change (["kind", "episode", "origin"] : List String).Nodup; decide)).mono (by decide)

 theorem row_spec (bounded : RowEncodable p view) : Spec (row p view) (Output.rowJson p view) 9472 := by
  rcases bounded with ⟨index, budget, used, total, event, cursor, _reason, observed, _next⟩
  have indexMax : view.index ≤ 18446744073709551615 := by change view.index < 32 at index; omega
  have budgetMax : view.action.budget ≤ 18446744073709551615 := by change view.action.budget ≤ 65536 at budget; omega
  have usedMax : view.used ≤ 18446744073709551615 := by omega
  have totalMax : view.totalUsed ≤ 18446744073709551615 := by change view.totalUsed ≤ 65536 at total; omega
  have eventMax : view.eventEnd ≤ 18446744073709551615 := by omega
  have cursorMax : view.readCursor ≤ 18446744073709551615 := by change view.readCursor ≤ 65536 at cursor; omega
  have observedSpec := optional_spec (Output.observationJson p) view.frontier.observation
    (fun item found => observation_spec (observed item (by simpa using found))) (by decide : 4 ≤ 8576)
  have nextSpec := optional_spec (toJson ∘ Output.actionName) view.frontier.next
    (fun item _ => action_spec item) (by decide : 4 ≤ 10)
  unfold row Output.rowJson
  exact (Spec.object (FieldSpec.cons (key := "index") (by unfold SafeASCII; decide) (Spec.natural (n := view.index) (by exact indexMax)) (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (action_spec view.action.kind) (FieldSpec.cons (key := "budget") (by unfold SafeASCII; decide) (Spec.natural (n := view.action.budget) (by exact budgetMax)) (FieldSpec.cons (key := "used") (by unfold SafeASCII; decide) (Spec.natural (n := view.used) (by exact usedMax)) (FieldSpec.cons (key := "total_used") (by unfold SafeASCII; decide) (Spec.natural (n := view.totalUsed) (by exact totalMax)) (FieldSpec.cons (key := "status") (by unfold SafeASCII; decide) (status_spec (reasonStatus view.reason)) (FieldSpec.cons (key := "observation") (by unfold SafeASCII; decide) observedSpec (FieldSpec.cons (key := "event_end") (by unfold SafeASCII; decide) (Spec.natural (n := view.eventEnd) (by exact eventMax)) (FieldSpec.cons (key := "read_cursor") (by unfold SafeASCII; decide) (Spec.natural (n := view.readCursor) (by exact cursorMax)) (FieldSpec.cons (key := "delivery_state") (by unfold SafeASCII; decide) (delivery_state_spec view.delivery) (FieldSpec.cons (key := "next_action") (by unfold SafeASCII; decide) nextSpec FieldSpec.nil rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) (by change (["index", "kind", "budget", "used", "total_used", "status", "observation", "event_end", "read_cursor", "delivery_state", "next_action"] : List String).Nodup; decide)).mono (by decide)

 def unusedTarget (view : UnusedView) : Json := Json.mkObj [
  ("reads_total", toJson view.readsTotal), ("reads_consumed", toJson view.readsConsumed),
  ("reads_remaining", toJson view.readsRemaining), ("delivery", Output.optionalJson Output.deliveryJson view.delivery),
  ("delivery_state", toJson (Output.deliveryName view.deliveryState))]

 theorem unused_spec (bounded : UnusedEncodable view) : Spec (unused view) (unusedTarget view) 272640 := by
  have length := unused_reads_bound bounded
  rcases bounded with ⟨total, consumed, _length, readValues, deliveryBound⟩
  have totalMax : view.readsTotal ≤ 18446744073709551615 := by change view.readsTotal ≤ 65536 at total; omega
  have consumedMax : view.readsConsumed ≤ 18446744073709551615 := by omega
  have reads : Spec (array natural view.readsRemaining) (toJson view.readsRemaining) 262146 :=
    (natural_array_spec view.readsRemaining readValues).mono (by omega)
  have deliveryValue : ∀ item, view.delivery = some item → DeliveryEncodable item := by
    intro item found
    rw [found] at deliveryBound
    exact deliveryBound.1
  have pending := optional_spec Output.deliveryJson view.delivery
    (fun item found => delivery_spec (deliveryValue item found)) (by decide : 4 ≤ 8832)
  unfold unused unusedTarget
  exact (Spec.object (FieldSpec.cons (key := "reads_total") (by unfold SafeASCII; decide) (Spec.natural (n := view.readsTotal) (by exact totalMax)) (FieldSpec.cons (key := "reads_consumed") (by unfold SafeASCII; decide) (Spec.natural (n := view.readsConsumed) (by exact consumedMax)) (FieldSpec.cons (key := "reads_remaining") (by unfold SafeASCII; decide) reads (FieldSpec.cons (key := "delivery") (by unfold SafeASCII; decide) pending (FieldSpec.cons (key := "delivery_state") (by unfold SafeASCII; decide) (delivery_state_spec view.deliveryState) FieldSpec.nil rfl) rfl) rfl) rfl) rfl) (by change (["reads_total", "reads_consumed", "reads_remaining", "delivery", "delivery_state"] : List String).Nodup; decide)).mono (by decide)

end ANL.Boot.Reference.Summary
