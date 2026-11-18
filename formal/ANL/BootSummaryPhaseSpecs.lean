import ANL.BootSummaryOriginSpecs

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

 theorem pending_spec (context : ContextEncodable p) (bounded : PendingEncodable p view) :
    Spec (pending view) (Output.pendingJson view) 9472 := by
  rcases bounded with ⟨_positive, ordinal, declaration, op, args, loc⟩
  have arguments : Spec (array value view.arguments) (toJson (view.arguments.map Output.valueJson)) 67 := by
    apply (Spec.array value Output.valueJson view.arguments
      (fun item member => value_spec (arguments_values args item member))).mono
    have length := arguments_length args
    omega
  unfold pending Output.pendingJson
  exact (Spec.object (FieldSpec.cons (key := "ordinal") (by unfold SafeASCII; decide) (Spec.natural (n := view.ordinal) (by exact transition_max ordinal)) (FieldSpec.cons (key := "declaration") (by unfold SafeASCII; decide) (Spec.natural (n := view.declaration) (by exact declaration_max declaration)) (FieldSpec.cons (key := "operation") (by unfold SafeASCII; decide) (operation_spec context op) (FieldSpec.cons (key := "arguments") (by unfold SafeASCII; decide) arguments (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec loc) FieldSpec.nil rfl) rfl) rfl) rfl) rfl) (by change (["ordinal", "declaration", "operation", "arguments", "origin"] : List String).Nodup; decide)).mono (by decide)

 theorem primitive_phase_spec (context : ContextEncodable p) (safe : SafeASCII name)
    (nameBytes : name.toUTF8.size ≤ 16) (bounded : PendingEncodable p view)
    (resultBound : ∀ item, result = some item → ValueEncodable item) :
    Spec (primitivePhase name view result) (Output.primitivePhaseJson name view result) 9984 := by
  have nameSpec : Spec (ascii name) (toJson name) 18 := (Spec.ascii safe).mono (by omega)
  have resultSpec := optional_spec Output.valueJson result (fun item found => value_spec (resultBound item found)) (by decide : 4 ≤ 64)
  unfold primitivePhase Output.primitivePhaseJson
  exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) nameSpec (FieldSpec.cons (key := "pending") (by unfold SafeASCII; decide) (pending_spec context bounded) (FieldSpec.cons (key := "result") (by unfold SafeASCII; decide) resultSpec FieldSpec.nil rfl) rfl) rfl) (by change (["kind", "pending", "result"] : List String).Nodup; decide)).mono (by decide)

 theorem phase_spec (context : ContextEncodable p) (bounded : PhaseEncodable p view) :
    Spec (phase view) (Output.phaseJson view) 9984 := by
  cases view with
  | ordinary =>
    simp only [phase, Output.phaseJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "ordinary") (by unfold SafeASCII; decide)) FieldSpec.nil rfl) (by change (["kind"] : List String).Nodup; decide)).mono (by decide)
  | before q =>
    exact primitive_phase_spec context (by unfold SafeASCII; decide) (by decide) bounded (by intro item found; cases found)
  | commit q =>
    exact primitive_phase_spec context (by unfold SafeASCII; decide) (by decide) bounded (by intro item found; cases found)
  | after q v =>
    exact primitive_phase_spec context (by unfold SafeASCII; decide) (by decide) bounded.1
      (by intro item found; cases found; exact result_value bounded.2)
  | finish q v =>
    exact primitive_phase_spec context (by unfold SafeASCII; decide) (by decide) bounded.1
      (by intro item found; cases found; exact result_value bounded.2)
  | parkCheck loc =>
    simp only [phase, Output.phaseJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "park_check") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec bounded) FieldSpec.nil rfl) rfl) (by change (["kind", "origin"] : List String).Nodup; decide)).mono (by decide)
  | parkObserved loc =>
    simp only [phase, Output.phaseJson]
    exact (Spec.object (FieldSpec.cons (key := "kind") (by unfold SafeASCII; decide) (Spec.ascii (value := "park_observed") (by unfold SafeASCII; decide)) (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec bounded) FieldSpec.nil rfl) rfl) (by change (["kind", "origin"] : List String).Nodup; decide)).mono (by decide)

 theorem snapshot_spec (context : ContextEncodable p) (bounded : SnapshotEncodable p view) :
    Spec (snapshot view) (Output.snapshotJson view) 18944 := by
  unfold snapshot Output.snapshotJson
  exact (Spec.object (FieldSpec.cons (key := "episode") (by unfold SafeASCII; decide) (episode_spec view.episode) (FieldSpec.cons (key := "stack_role") (by unfold SafeASCII; decide) (stack_spec view.stackRole) (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec bounded.1) (FieldSpec.cons (key := "phase") (by unfold SafeASCII; decide) (phase_spec context bounded.2) FieldSpec.nil rfl) rfl) rfl) rfl) (by change (["episode", "stack_role", "origin", "phase"] : List String).Nodup; decide)).mono (by decide)

 theorem hardware_spec (bounded : Hardware.Valid view)
    (handlerBound : ∀ ident ∈ view.installedHandler, ident < declarationLimit) :
    Spec (hardware view) (Output.hardwareJson view) 256 := by
  have handler := optional_spec toJson view.installedHandler
    (fun ident found => Spec.natural (declaration_max (handlerBound ident (by simpa using found)))) (by decide : 4 ≤ 20)
  unfold hardware Output.hardwareJson
  exact (Spec.object (FieldSpec.cons (key := "sstatus") (by unfold SafeASCII; decide) (Spec.word (word_max bounded.1)) (FieldSpec.cons (key := "sie") (by unfold SafeASCII; decide) (Spec.word (word_max bounded.2)) (FieldSpec.cons (key := "installed_handler") (by unfold SafeASCII; decide) handler FieldSpec.nil rfl) rfl) rfl) (by change (["sstatus", "sie", "installed_handler"] : List String).Nodup; decide)).mono (by decide)

 theorem final_spec (context : ContextEncodable p) (bounded : FinalEncodable p view) :
    Spec (final view) (Output.finalJson view) 41984 := by
  rcases bounded with ⟨loc, phaseBound, hard, installed, cursor, _positive, ordinal, saved, _next⟩
  have cursorMax : view.readCursor ≤ 18446744073709551615 := by
    change view.readCursor ≤ 65536 at cursor
    omega
  have savedSpec := optional_spec Output.snapshotJson view.interrupted
    (fun item found => snapshot_spec context (by simpa [OptionalSnapshotEncodable, found] using saved)) (by decide : 4 ≤ 18944)
  have nextSpec := optional_spec (toJson ∘ Output.actionName) view.nextAction
    (fun item _ => action_spec item) (by decide : 4 ≤ 10)
  unfold final Output.finalJson
  exact (Spec.object (FieldSpec.cons (key := "episode") (by unfold SafeASCII; decide) (episode_spec view.episode) (FieldSpec.cons (key := "stack_role") (by unfold SafeASCII; decide) (stack_spec view.stackRole) (FieldSpec.cons (key := "origin") (by unfold SafeASCII; decide) (origin_spec loc) (FieldSpec.cons (key := "phase") (by unfold SafeASCII; decide) (phase_spec context phaseBound) (FieldSpec.cons (key := "hardware") (by unfold SafeASCII; decide) (hardware_spec hard installed) (FieldSpec.cons (key := "read_cursor") (by unfold SafeASCII; decide) (Spec.natural (n := view.readCursor) (by exact cursorMax)) (FieldSpec.cons (key := "next_ordinal") (by unfold SafeASCII; decide) (Spec.natural (n := view.nextOrdinal) (by exact transition_max ordinal)) (FieldSpec.cons (key := "delivery_used") (by unfold SafeASCII; decide) (Spec.boolean view.deliveryUsed) (FieldSpec.cons (key := "boot_park_seen") (by unfold SafeASCII; decide) (Spec.boolean view.bootParkSeen) (FieldSpec.cons (key := "episode_park_seen") (by unfold SafeASCII; decide) (Spec.boolean view.episodeParkSeen) (FieldSpec.cons (key := "interrupted") (by unfold SafeASCII; decide) savedSpec (FieldSpec.cons (key := "next_action") (by unfold SafeASCII; decide) nextSpec FieldSpec.nil rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) (by change (["episode", "stack_role", "origin", "phase", "hardware", "read_cursor", "next_ordinal", "delivery_used", "boot_park_seen", "episode_park_seen", "interrupted", "next_action"] : List String).Nodup; decide)).mono (by decide)

end ANL.Boot.Reference.Summary
