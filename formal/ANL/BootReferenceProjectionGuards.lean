import ANL.BootReferenceProjectionCore

namespace ANL.Boot.Reference.Projection
open ANL.Boot.Runtime ANL.Boot.Runtime.Session

def EdgeEncodable : Origin.Edge → Prop
  | .callArgument i | .tupleField i => i ≤ wireNatMax
  | _ => True
instance (edge : Origin.Edge) : Decidable (EdgeEncodable edge) := by cases edge <;> unfold EdgeEncodable <;> infer_instance

def OriginEncodable (origin : Origin.Location) : Prop :=
  origin.function < declarationLimit ∧ origin.path.length ≤ originLimit ∧
    ∀ edge ∈ origin.path, EdgeEncodable edge
instance (origin : Origin.Location) : Decidable (OriginEncodable origin) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ValueEncodable : Value → Prop
  | .unit => True
  | .byte n => n < byteModulus
instance (value : Value) : Decidable (ValueEncodable value) := by cases value <;> unfold ValueEncodable <;> infer_instance

def ByteEncodable : Value → Prop
  | .unit => False | .byte n => n < byteModulus
instance (value : Value) : Decidable (ByteEncodable value) := by cases value <;> unfold ByteEncodable <;> infer_instance

def ArgumentsEncodable (op : Operation) (values : List Value) : Prop :=
  values.length = op.params.length ∧ ∀ value ∈ values, ByteEncodable value
instance (op : Operation) (values : List Value) : Decidable (ArgumentsEncodable op values) := by
  unfold ArgumentsEncodable; infer_instance

def ResultEncodable (op : Operation) (value : Value) : Prop :=
  match op, value with
  | .read8 .., .byte n => n < byteModulus
  | .read8 .., _ => False
  | _, .unit => True
  | _, _ => False
instance (op : Operation) (value : Value) : Decidable (ResultEncodable op value) := by
  cases op <;> cases value <;> unfold ResultEncodable <;> infer_instance

def PendingEncodable (p : Program) (view : PendingView) : Prop :=
  0 < view.ordinal ∧ view.ordinal ≤ transitionLimit + 1 ∧
  view.declaration < declarationLimit ∧ view.operation.Valid p.entries.hardware.function ∧
  ArgumentsEncodable view.operation view.arguments ∧ OriginEncodable view.origin
instance (p : Program) (view : PendingView) : Decidable (PendingEncodable p view) := by
  unfold PendingEncodable; infer_instance

def PhaseEncodable (p : Program) : PhaseView → Prop
  | .ordinary => True
  | .before q | .commit q => PendingEncodable p q
  | .after q v | .finish q v => PendingEncodable p q ∧ ResultEncodable q.operation v
  | .parkCheck origin | .parkObserved origin => OriginEncodable origin
instance (p : Program) (view : PhaseView) : Decidable (PhaseEncodable p view) := by
  cases view <;> unfold PhaseEncodable <;> infer_instance

def SnapshotEncodable (p : Program) (view : SnapshotView) : Prop :=
  OriginEncodable view.origin ∧ PhaseEncodable p view.phase
instance (p : Program) (view : SnapshotView) : Decidable (SnapshotEncodable p view) := by
  unfold SnapshotEncodable; infer_instance

def OptionalSnapshotEncodable (p : Program) : Option SnapshotView → Prop
  | none => True | some view => SnapshotEncodable p view
instance (p : Program) (view : Option SnapshotView) : Decidable (OptionalSnapshotEncodable p view) := by
  cases view <;> unfold OptionalSnapshotEncodable <;> infer_instance

def NextEncodable : Option ActionKind → Prop
  | some .run => False | _ => True
instance (kind : Option ActionKind) : Decidable (NextEncodable kind) := by
  cases kind with
  | none => exact isTrue trivial
  | some k => cases k <;> unfold NextEncodable <;> infer_instance

def FinalEncodable (p : Program) (view : FinalView) : Prop :=
  OriginEncodable view.origin ∧ PhaseEncodable p view.phase ∧ view.hardware.Valid ∧
  (∀ id ∈ view.hardware.installedHandler, id < declarationLimit) ∧
  view.readCursor ≤ readLimit ∧ 0 < view.nextOrdinal ∧ view.nextOrdinal ≤ transitionLimit + 1 ∧
  OptionalSnapshotEncodable p view.interrupted ∧ NextEncodable view.nextAction
instance (p : Program) (view : FinalView) : Decidable (FinalEncodable p view) := by
  unfold FinalEncodable; infer_instance

def LandmarkEncodable : Landmark → Prop
  | .beforePrimitive k id | .afterPrimitive k id =>
      0 < k ∧ k ≤ wireNatMax ∧ id < declarationLimit
  | .bootPark origin => OriginEncodable origin ∧ ∀ edge ∈ origin.path, TailEdge edge
instance (key : Landmark) : Decidable (LandmarkEncodable key) := by
  cases key <;> unfold LandmarkEncodable <;> infer_instance

def DeliveryEncodable (d : Delivery) : Prop :=
  LandmarkEncodable d.landmark ∧ d.scause < wordModulus ∧ d.sepc < wordModulus ∧ d.stval < wordModulus
instance (d : Delivery) : Decidable (DeliveryEncodable d) := by unfold DeliveryEncodable; infer_instance

def UnusedEncodable (view : UnusedView) : Prop :=
  view.readsTotal ≤ readLimit ∧ view.readsConsumed ≤ view.readsTotal ∧
  view.readsRemaining.length = view.readsTotal - view.readsConsumed ∧
  (∀ n ∈ view.readsRemaining, n < byteModulus) ∧
  match view.delivery with
  | none => view.deliveryState = .absent
  | some d => DeliveryEncodable d ∧ (view.deliveryState = .pending ∨ view.deliveryState = .used)
instance (view : UnusedView) : Decidable (UnusedEncodable view) := by
  unfold UnusedEncodable
  cases view.delivery <;> infer_instance

def ObservationEncodable (p : Program) : ObservationKind → Prop
  | .handlerEntry episode => episode.function p < declarationLimit
  | .park _ location => OriginEncodable location
instance (p : Program) (kind : ObservationKind) : Decidable (ObservationEncodable p kind) := by
  cases kind <;> unfold ObservationEncodable <;> infer_instance

def ReasonEncodable (p : Program) : StopReason → Prop
  | .observed kind | .unobserved kind => ObservationEncodable p kind
  | _ => True
instance (p : Program) (reason : StopReason) : Decidable (ReasonEncodable p reason) := by
  cases reason <;> unfold ReasonEncodable <;> infer_instance

def RowEncodable (p : Program) (row : Row) : Prop :=
  row.index < actionLimit ∧ row.action.budget ≤ transitionLimit ∧ row.used ≤ row.action.budget ∧
  row.totalUsed ≤ transitionLimit ∧ row.eventEnd ≤ row.totalUsed ∧ row.readCursor ≤ readLimit ∧
  ReasonEncodable p row.reason ∧ (∀ observation ∈ row.frontier.observation, ObservationEncodable p observation) ∧
  NextEncodable row.frontier.next
instance (p : Program) (row : Row) : Decidable (RowEncodable p row) := by unfold RowEncodable; infer_instance

def SummaryEncodable (p : Program) (view : SummaryView) : Prop :=
  0 < view.executed ∧ view.requested ≤ actionLimit ∧ view.executed = view.rows.length ∧
  view.executed + view.unexecuted = view.requested ∧ view.totalUsed ≤ transitionLimit ∧
  (∀ index ∈ view.failureAction, index = view.executed ∧ index < view.requested) ∧
  (∀ row ∈ view.rows, RowEncodable p row) ∧ UnusedEncodable view.unused
instance (p : Program) (view : SummaryView) : Decidable (SummaryEncodable p view) := by
  unfold SummaryEncodable; infer_instance

def PayloadEncodable : Operation → Payload → Prop
  | .read8 .., .read n | .write8 .., .write n => n < byteModulus
  | .fence .., .unit | .csrClear .., .unit | .csrWrite .., .unit | .installTrap .., .unit => True
  | _, _ => False
instance (op : Operation) (payload : Payload) : Decidable (PayloadEncodable op payload) := by
  cases op <;> cases payload <;> unfold PayloadEncodable <;> infer_instance

def EventEncodable (p : Program) : Event → Prop
  | .primitive ordinal declaration op payload =>
      0 < ordinal ∧ ordinal ≤ transitionLimit ∧ declaration < declarationLimit ∧
      op.Valid p.entries.hardware.function ∧ PayloadEncodable op payload
  | .language tag => tag = 1 ∨ tag = 2 ∨ tag = 3
  | .hardware key cause pc auxiliary =>
      LandmarkEncodable key ∧ cause < wordModulus ∧ pc < wordModulus ∧ auxiliary < wordModulus
instance (p : Program) (event : Event) : Decidable (EventEncodable p event) := by
  cases event <;> unfold EventEncodable <;> infer_instance

/-- Export-only predicate. The projector retains raw events without traversing them. -/
def TraceEncodable (p : Program) (view : TraceView) : Prop :=
  view.revEvents.length ≤ transitionLimit ∧ ∀ event ∈ view.revEvents, EventEncodable p event

end ANL.Boot.Reference.Projection
