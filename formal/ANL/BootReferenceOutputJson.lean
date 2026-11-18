import ANL.BootReferenceProjectionSession
import ANL.MemoryReferenceOutput

namespace ANL.Boot.Reference.Output
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

abbrev outputLimit : Nat := 8388608

def optionalJson (f : α → Json) : Option α → Json
  | none => .null | some value => f value

def episodeName : Episode → String
  | .boot => "boot" | .hardwareHandler => "hardware_handler" | .languageHandler => "language_handler"
def stackName : StackRole → String
  | .boot => "boot" | .terminal => "terminal"
def actionName : ActionKind → String
  | .run => "run" | .continue => "continue" | .resume => "resume"
def deliveryName : DeliveryView → String
  | .absent => "absent" | .pending => "pending" | .used => "used"

def edgeJson : Origin.Edge → Json
  | .callArgument i => Json.mkObj [("edge", toJson "callArgument"), ("index", toJson i)]
  | .tupleField i => Json.mkObj [("edge", toJson "tupleField"), ("index", toJson i)]
  | edge => Json.mkObj [("edge", toJson (match edge with
      | .letValue => "letValue" | .letBody => "letBody"
      | .whileCondition => "whileCondition" | .whileBody => "whileBody"
      | .ifCondition => "ifCondition" | .ifThen => "ifThen" | .ifElse => "ifElse"
      | .unaryOperand => "unaryOperand" | .binaryLeft => "binaryLeft" | .binaryRight => "binaryRight"
      | .convertOperand => "convertOperand" | .projectOperand => "projectOperand" | .assignValue => "assignValue"
      | .callArgument _ => "callArgument" | .tupleField _ => "tupleField"))]

def originJson (origin : Origin.Location) : Json := Json.mkObj [
  ("function", toJson origin.function), ("core_path", toJson (origin.path.map edgeJson))]

def landmarkJson : Landmark → Json
  | .beforePrimitive ordinal declaration => Json.mkObj [
      ("kind", toJson "before_primitive"), ("ordinal", toJson ordinal), ("declaration", toJson declaration)]
  | .afterPrimitive ordinal declaration => Json.mkObj [
      ("kind", toJson "after_primitive"), ("ordinal", toJson ordinal), ("declaration", toJson declaration)]
  | .bootPark origin => Json.mkObj [("kind", toJson "boot_park"), ("origin", originJson origin)]

def deliveryJson (d : Delivery) : Json := Json.mkObj [
  ("landmark", landmarkJson d.landmark), ("scause", toJson (toString d.scause)),
  ("sepc", toJson (toString d.sepc)), ("stval", toJson (toString d.stval))]

def operationJson : Operation → Json
  | .read8 region offset => Json.mkObj [("tag", toJson "mmio_read8"), ("region", toJson region), ("offset", toJson offset)]
  | .write8 region offset => Json.mkObj [("tag", toJson "mmio_write8"), ("region", toJson region), ("offset", toJson offset)]
  | .fence region => Json.mkObj [("tag", toJson "io_fence"), ("region", toJson region)]
  | .csrClear authority register mask => Json.mkObj [
      ("tag", toJson "csr_clear"), ("authority", toJson authority), ("register", toJson register), ("mask", toJson (toString mask))]
  | .csrWrite authority register value => Json.mkObj [
      ("tag", toJson "csr_write"), ("authority", toJson authority), ("register", toJson register), ("value", toJson (toString value))]
  | .installTrap authority target => Json.mkObj [
      ("tag", toJson "install_trap"), ("authority", toJson authority), ("handler", toJson target)]

def valueJson : Value → Json
  | .unit => Json.mkObj [("type", toJson "unit")]
  | .byte n => Json.mkObj [("type", toJson "u8"), ("value", toJson n)]

def pendingJson (q : PendingView) : Json := Json.mkObj [
  ("ordinal", toJson q.ordinal), ("declaration", toJson q.declaration),
  ("operation", operationJson q.operation), ("arguments", toJson (q.arguments.map valueJson)), ("origin", originJson q.origin)]

def primitivePhaseJson (name : String) (q : PendingView) (result : Option Value) : Json :=
  Json.mkObj [("kind", toJson name), ("pending", pendingJson q), ("result", optionalJson valueJson result)]

def phaseJson : PhaseView → Json
  | .ordinary => Json.mkObj [("kind", toJson "ordinary")]
  | .before q => primitivePhaseJson "primitive_before" q none
  | .commit q => primitivePhaseJson "primitive_commit" q none
  | .after q v => primitivePhaseJson "primitive_after" q (some v)
  | .finish q v => primitivePhaseJson "primitive_return" q (some v)
  | .parkCheck origin => Json.mkObj [("kind", toJson "park_check"), ("origin", originJson origin)]
  | .parkObserved origin => Json.mkObj [("kind", toJson "park_observed"), ("origin", originJson origin)]

def snapshotJson (view : SnapshotView) : Json := Json.mkObj [
  ("episode", toJson (episodeName view.episode)), ("stack_role", toJson (stackName view.stackRole)),
  ("origin", originJson view.origin), ("phase", phaseJson view.phase)]

def hardwareJson (h : Hardware) : Json := Json.mkObj [
  ("sstatus", toJson (toString h.sstatus)), ("sie", toJson (toString h.sie)),
  ("installed_handler", optionalJson toJson h.installedHandler)]

def finalJson (view : FinalView) : Json := Json.mkObj [
  ("episode", toJson (episodeName view.episode)), ("stack_role", toJson (stackName view.stackRole)),
  ("origin", originJson view.origin), ("phase", phaseJson view.phase), ("hardware", hardwareJson view.hardware),
  ("read_cursor", toJson view.readCursor), ("next_ordinal", toJson view.nextOrdinal),
  ("delivery_used", toJson view.deliveryUsed), ("boot_park_seen", toJson view.bootParkSeen),
  ("episode_park_seen", toJson view.episodeParkSeen), ("interrupted", optionalJson snapshotJson view.interrupted),
  ("next_action", optionalJson (toJson ∘ actionName) view.nextAction)]

def observationJson (p : Program) : ObservationKind → Json
  | .handlerEntry episode => Json.mkObj [("kind", toJson "handler_entry"),
      ("episode", toJson (episodeName episode)), ("function", toJson (episode.function p))]
  | .park episode origin => Json.mkObj [("kind", toJson "park"),
      ("episode", toJson (episodeName episode)), ("origin", originJson origin)]

def rowJson (p : Program) (row : Row) : Json := Json.mkObj [
  ("index", toJson row.index), ("kind", toJson (actionName row.action.kind)), ("budget", toJson row.action.budget),
  ("used", toJson row.used), ("total_used", toJson row.totalUsed), ("status", toJson (reasonStatus row.reason).name),
  ("observation", optionalJson (observationJson p) row.frontier.observation), ("event_end", toJson row.eventEnd),
  ("read_cursor", toJson row.readCursor), ("delivery_state", toJson (deliveryName row.delivery)),
  ("next_action", optionalJson (toJson ∘ actionName) row.frontier.next)]

def payloadJson : Payload → Json
  | .unit => Json.mkObj [("kind", toJson "unit")]
  | .read n => Json.mkObj [("kind", toJson "read"), ("value", toJson n)]
  | .write n => Json.mkObj [("kind", toJson "write"), ("value", toJson n)]

def eventJson : Event → Json
  | .primitive ordinal declaration operation payload => Json.mkObj [
      ("kind", toJson "primitive"), ("ordinal", toJson ordinal), ("declaration", toJson declaration),
      ("operation", operationJson operation), ("payload", payloadJson payload)]
  | .language tag => Json.mkObj [("kind", toJson "language"), ("tag", toJson tag)]
  | .hardware key cause pc auxiliary => Json.mkObj [("kind", toJson "hardware"), ("landmark", landmarkJson key),
      ("scause", toJson (toString cause)), ("sepc", toJson (toString pc)), ("stval", toJson (toString auxiliary))]

def limitsJson : Json := Json.mkObj [
  ("id", toJson "anl-boot-reference-limits-v1"),
  ("core_bytes", toJson (1048576 : Nat)), ("core_json_depth", toJson (1024 : Nat)), ("core_logical_depth", toJson (128 : Nat)),
  ("request_bytes", toJson (1048576 : Nat)), ("request_json_depth", toJson (16 : Nat)),
  ("declarations", toJson declarationLimit), ("term_nodes", toJson nodeLimit), ("parameters", toJson arityLimit),
  ("call_arguments", toJson arityLimit), ("reads", toJson readLimit), ("delivery_origin_edges", toJson originLimit),
  ("output_origin_edges", toJson originLimit), ("actions", toJson actionLimit), ("action_transitions", toJson transitionLimit),
  ("total_transitions", toJson transitionLimit), ("events", toJson transitionLimit), ("output_bytes", toJson outputLimit),
  ("reason_utf8_bytes", toJson (1024 : Nat))]

/-- Header values are all bounded by the guarded projection entry; no trace/row Json tree is built. -/
def headerFields (identity : Option Identity) (status : Status) (reason : String) (summary : Option SummaryView) : List (String × Json) := [
  ("schema", toJson "anl-boot-reference-run-v1"), ("status", toJson status.name), ("reason", toJson reason),
  ("semantic_revision", optionalJson (toJson ∘ Identity.semanticRevision) identity),
  ("ordinary_semantic_revision", optionalJson (toJson ∘ Identity.ordinaryRevision) identity),
  ("target_profile", optionalJson (toJson ∘ Identity.targetProfile) identity), ("limits", limitsJson),
  ("failure_action", match summary with | none => .null | some s => optionalJson toJson s.failureAction),
  ("actions_requested", optionalJson (toJson ∘ SummaryView.requested) summary),
  ("actions_executed", optionalJson (toJson ∘ SummaryView.executed) summary),
  ("actions_unexecuted", optionalJson (toJson ∘ SummaryView.unexecuted) summary),
  ("total_used", optionalJson (toJson ∘ SummaryView.totalUsed) summary)]

end ANL.Boot.Reference.Output
