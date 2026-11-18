import ANL.BootReferenceProjectionGuards

namespace ANL.Boot.Reference.Projection
open ANL.Words ANL.Boot.Runtime ANL.Boot.Runtime.Session

def valueView (value : Words.Val) : Option Value :=
  if value = unitValue then some .unit else (byteOperand value).map Value.byte

def argumentViews (op : Operation) (args : List Words.Val) : Option (List Value) :=
  match op, args with
  | .write8 .., [value] => (byteOperand value).map (fun n => [.byte n])
  | .write8 .., _ => none
  | _, [] => some []
  | _, _ => none

def pendingView (pending : Pending) : Option PendingView := do
  let args ← argumentViews pending.operation pending.arguments
  return ⟨pending.ordinal, pending.declaration, pending.operation, args, pending.origin⟩

def phaseView : Phase → Option PhaseView
  | .ordinary => some .ordinary
  | .primitiveBefore q => (pendingView q).map PhaseView.before
  | .primitiveCommit q => (pendingView q).map PhaseView.commit
  | .primitiveAfter q v => do return .after (← pendingView q) (← valueView v)
  | .primitiveReturn q v => do return .finish (← pendingView q) (← valueView v)
  | .parkCheck origin => some (.parkCheck origin)
  | .parkObserved origin => some (.parkObserved origin)

def snapshotView (snapshot : Interrupted) : Option SnapshotView := do
  return ⟨snapshot.episode, snapshot.stackRole, snapshot.origins.control, ← phaseView snapshot.phase⟩

def optionalSnapshotView : Option Interrupted → Option (Option SnapshotView)
  | none => some none
  | some snapshot => (snapshotView snapshot).map some

def finalView (result : Session.Result) : Option FinalView := do
  let state := result.state
  let phase ← phaseView state.phase
  let interrupted ← optionalSnapshotView state.interrupted
  return ⟨state.episode, state.stackRole, state.origins.control, phase, state.hardware,
    state.readCursor, state.nextOrdinal, state.deliveryUsed, state.bootParkSeen,
    state.episodeParkSeen, interrupted, result.frontier.next⟩

def unusedView (env : Environment) (state : Runtime.State) : UnusedView :=
  ⟨env.reads.length, state.readCursor, env.reads.drop state.readCursor, env.delivery, deliveryView env state⟩

def reasonStatus : StopReason → Status
  | .observed _ => .observed | .unobserved _ => .unobserved | .exhausted => .exhausted
  | .blockedRead => .blockedRead | .ineligibleDelivery => .ineligibleDelivery | .invalidState => .error

def resultStatus (result : Session.Result) : Status :=
  match result.ending with
  | .done => reasonStatus result.previous
  | .rejected _ => .rejected | .blocked => .blockedRead
  | .ineligible => .ineligibleDelivery | .invalid => .error

def summaryView (request : Request) (result : Session.Result) : SummaryView :=
  ⟨(match result.ending with | .rejected i => some i | _ => none),
    request.actions.length, result.rows.length, request.actions.length - result.rows.length,
    result.totalUsed, result.rows, unusedView request.environment result.state⟩

def identityView (p : Program) : Identity := ⟨p.semanticRevision, p.ordinaryRevision, p.profile.id⟩

def fullReport (p : Program) (request : Request) (result : Session.Result) (final : FinalView) : Report :=
  ⟨identityView p, resultStatus result, (resultStatus result).executionReason,
    some (summaryView request result), some final, some ⟨result.state.revEvents⟩⟩

/-- Pure error recovery retains only a previously validated compact summary. No state is changed. -/
def projectionFailure (p : Program) (summary : Option SummaryView) : Report :=
  ⟨identityView p, .error, "projection_shape_error", summary, none, none⟩

/-- No classifier, semantic transition, input validator or full event traversal occurs here. -/
def projectReport (p : Program) (request : Request) (result : Session.Result) : Report :=
  let summary := summaryView request result
  if SummaryEncodable p summary then
    match finalView result with
    | none => projectionFailure p (some summary)
    | some final =>
      if FinalEncodable p final then fullReport p request result final
      else projectionFailure p (some summary)
  else projectionFailure p none

/-- This relation characterizes successful full projection without defining it by executable output. -/
structure FullProjection (p : Program) (request : Request) (result : Session.Result) (report : Report) : Prop where
  meaning : ReportOf p request result report
  summaryBound : ∀ summary, report.summary = some summary → SummaryEncodable p summary
  finalBound : ∀ final, report.final = some final → FinalEncodable p final

inductive ProjectionRecovery (p : Program) (request : Request) (result : Session.Result) : Report → Prop where
  | summary : SummaryOf request result summary → ¬ SummaryEncodable p summary →
      ProjectionRecovery p request result (projectionFailure p none)
  | final : SummaryOf request result summary → SummaryEncodable p summary →
      (∀ final, FinalOf result final → ¬ FinalEncodable p final) →
      ProjectionRecovery p request result (projectionFailure p (some summary))

end ANL.Boot.Reference.Projection
