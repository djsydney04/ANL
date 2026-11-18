import ANL.BootSummaryComponents

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

/-- Recovery admission is independent of writers, byte bounds and future execution. -/
structure RecoveryReady (p : Program) (report : Report) : Prop where
  context : ContextEncodable p
  identity : report.identity = identityView p
  status : report.status = .error
  trace : report.trace = none
  reason : ∃ error : Output.ExportError, report.reason = error.reason
  summary : ∀ view, report.summary = some view → SummaryEncodable p view
  final : ∀ view, report.final = some view → FinalEncodable p view
  unavailable : report.summary = none → report.final = none

/-- Raw prestart identity is accepted only when canonical or absent. -/
def PrestartReady (identity : Option Identity) : Prop :=
  ∀ value, identity = some value → IdentityEncodable value

/-- A fixed-size list of field writers; it never expands rows or reads into a JSON tree. -/
def header (identity : Option Identity) (status : Status) (reason : String)
    (summary : Option SummaryView) : List (String × Writer) := [
  ("schema", ascii "anl-boot-reference-run-v1"), ("status", ascii status.name), ("reason", diagnostic reason),
  ("semantic_revision", optional (ascii ∘ Identity.semanticRevision) identity),
  ("ordinary_semantic_revision", optional (ascii ∘ Identity.ordinaryRevision) identity),
  ("target_profile", optional (ascii ∘ Identity.targetProfile) identity), ("limits", limits),
  ("failure_action", match summary with | none => null | some view => optional natural view.failureAction),
  ("actions_requested", optional (natural ∘ SummaryView.requested) summary),
  ("actions_executed", optional (natural ∘ SummaryView.executed) summary),
  ("actions_unexecuted", optional (natural ∘ SummaryView.unexecuted) summary),
  ("total_used", optional (natural ∘ SummaryView.totalUsed) summary)]

/-- Internal trace-null serializer. Trusted callers must establish RecoveryReady. -/
def recovery (p : Program) (report : Report) : Writer := object (
  header (some report.identity) report.status report.reason report.summary ++ [
    ("actions", array (row p) (report.summary.map SummaryView.rows |>.getD [])),
    ("final", optional final report.final), ("trace", null),
    ("unused_input", optional unused (report.summary.map SummaryView.unused))])

/-- Proof target only; the executable writer never constructs this whole JSON value. -/
def recoveryTarget (p : Program) (report : Report) : Json := Json.mkObj (
  Output.headerFields (some report.identity) report.status report.reason report.summary ++ [
    ("actions", toJson ((report.summary.map SummaryView.rows |>.getD []).map (Output.rowJson p))),
    ("final", Output.optionalJson Output.finalJson report.final), ("trace", .null),
    ("unused_input", match report.summary with
      | none => .null
      | some view => Json.mkObj [
          ("reads_total", toJson view.unused.readsTotal), ("reads_consumed", toJson view.unused.readsConsumed),
          ("reads_remaining", toJson view.unused.readsRemaining),
          ("delivery", Output.optionalJson Output.deliveryJson view.unused.delivery),
          ("delivery_state", toJson (Output.deliveryName view.unused.deliveryState))])])

/-- Pure prestart serializer, preserving the existing reason truncation and status mapping. -/
def prestart (identity : Option Identity) (failure : Output.PrestartFailure) : Writer := object (
  header identity failure.status failure.reason none ++ [
    ("actions", array (fun _ : Unit => null) []), ("final", null), ("trace", null), ("unused_input", null)])

end ANL.Boot.Reference.Summary
