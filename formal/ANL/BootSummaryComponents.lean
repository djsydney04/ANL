import ANL.BootSummaryWire

namespace ANL.Boot.Reference.Summary
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

/-- All inputs are existing projection values; no state interpretation occurs here. -/
def edge : Origin.Edge → Writer
  | .callArgument i => object [("edge", ascii "callArgument"), ("index", natural i)]
  | .tupleField i => object [("edge", ascii "tupleField"), ("index", natural i)]
  | value => object [("edge", ascii (match value with
      | .letValue => "letValue" | .letBody => "letBody"
      | .whileCondition => "whileCondition" | .whileBody => "whileBody"
      | .ifCondition => "ifCondition" | .ifThen => "ifThen" | .ifElse => "ifElse"
      | .unaryOperand => "unaryOperand" | .binaryLeft => "binaryLeft" | .binaryRight => "binaryRight"
      | .convertOperand => "convertOperand" | .projectOperand => "projectOperand" | .assignValue => "assignValue"
      | .callArgument _ => "callArgument" | .tupleField _ => "tupleField"))]

def origin (value : Origin.Location) : Writer := object [
  ("function", natural value.function), ("core_path", array edge value.path)]

def landmark : Landmark → Writer
  | .beforePrimitive ordinal declaration => object [
      ("kind", ascii "before_primitive"), ("ordinal", natural ordinal), ("declaration", natural declaration)]
  | .afterPrimitive ordinal declaration => object [
      ("kind", ascii "after_primitive"), ("ordinal", natural ordinal), ("declaration", natural declaration)]
  | .bootPark location => object [("kind", ascii "boot_park"), ("origin", origin location)]

def delivery (value : Delivery) : Writer := object [
  ("landmark", landmark value.landmark), ("scause", word value.scause),
  ("sepc", word value.sepc), ("stval", word value.stval)]

def operation : Operation → Writer
  | .read8 region offset => object [
      ("tag", ascii "mmio_read8"), ("region", natural region), ("offset", natural offset)]
  | .write8 region offset => object [
      ("tag", ascii "mmio_write8"), ("region", natural region), ("offset", natural offset)]
  | .fence region => object [("tag", ascii "io_fence"), ("region", natural region)]
  | .csrClear authority register mask => object [
      ("tag", ascii "csr_clear"), ("authority", natural authority), ("register", ascii register), ("mask", word mask)]
  | .csrWrite authority register value => object [
      ("tag", ascii "csr_write"), ("authority", natural authority), ("register", ascii register), ("value", word value)]
  | .installTrap authority target => object [
      ("tag", ascii "install_trap"), ("authority", natural authority), ("handler", natural target)]

def value : Value → Writer
  | .unit => object [("type", ascii "unit")]
  | .byte n => object [("type", ascii "u8"), ("value", natural n)]

def pending (view : PendingView) : Writer := object [
  ("ordinal", natural view.ordinal), ("declaration", natural view.declaration),
  ("operation", operation view.operation), ("arguments", array value view.arguments), ("origin", origin view.origin)]

def primitivePhase (name : String) (view : PendingView) (result : Option Value) : Writer :=
  object [("kind", ascii name), ("pending", pending view), ("result", optional value result)]

def phase : PhaseView → Writer
  | .ordinary => object [("kind", ascii "ordinary")]
  | .before q => primitivePhase "primitive_before" q none
  | .commit q => primitivePhase "primitive_commit" q none
  | .after q v => primitivePhase "primitive_after" q (some v)
  | .finish q v => primitivePhase "primitive_return" q (some v)
  | .parkCheck location => object [("kind", ascii "park_check"), ("origin", origin location)]
  | .parkObserved location => object [("kind", ascii "park_observed"), ("origin", origin location)]

def snapshot (view : SnapshotView) : Writer := object [
  ("episode", ascii (Output.episodeName view.episode)), ("stack_role", ascii (Output.stackName view.stackRole)),
  ("origin", origin view.origin), ("phase", phase view.phase)]

def hardware (view : Hardware) : Writer := object [
  ("sstatus", word view.sstatus), ("sie", word view.sie),
  ("installed_handler", optional natural view.installedHandler)]

def final (view : FinalView) : Writer := object [
  ("episode", ascii (Output.episodeName view.episode)), ("stack_role", ascii (Output.stackName view.stackRole)),
  ("origin", origin view.origin), ("phase", phase view.phase), ("hardware", hardware view.hardware),
  ("read_cursor", natural view.readCursor), ("next_ordinal", natural view.nextOrdinal),
  ("delivery_used", boolean view.deliveryUsed), ("boot_park_seen", boolean view.bootParkSeen),
  ("episode_park_seen", boolean view.episodeParkSeen), ("interrupted", optional snapshot view.interrupted),
  ("next_action", optional (ascii ∘ Output.actionName) view.nextAction)]

def observation (p : Program) : ObservationKind → Writer
  | .handlerEntry episode => object [("kind", ascii "handler_entry"),
      ("episode", ascii (Output.episodeName episode)), ("function", natural (episode.function p))]
  | .park episode location => object [("kind", ascii "park"),
      ("episode", ascii (Output.episodeName episode)), ("origin", origin location)]

def row (p : Program) (view : Row) : Writer := object [
  ("index", natural view.index), ("kind", ascii (Output.actionName view.action.kind)), ("budget", natural view.action.budget),
  ("used", natural view.used), ("total_used", natural view.totalUsed), ("status", ascii (reasonStatus view.reason).name),
  ("observation", optional (observation p) view.frontier.observation), ("event_end", natural view.eventEnd),
  ("read_cursor", natural view.readCursor), ("delivery_state", ascii (Output.deliveryName view.delivery)),
  ("next_action", optional (ascii ∘ Output.actionName) view.frontier.next)]

def unused (view : UnusedView) : Writer := object [
  ("reads_total", natural view.readsTotal), ("reads_consumed", natural view.readsConsumed),
  ("reads_remaining", array natural view.readsRemaining), ("delivery", optional delivery view.delivery),
  ("delivery_state", ascii (Output.deliveryName view.deliveryState))]

def limits : Writer := object [
  ("id", ascii "anl-boot-reference-limits-v1"),
  ("core_bytes", natural 1048576), ("core_json_depth", natural 1024), ("core_logical_depth", natural 128),
  ("request_bytes", natural 1048576), ("request_json_depth", natural 16),
  ("declarations", natural declarationLimit), ("term_nodes", natural nodeLimit), ("parameters", natural arityLimit),
  ("call_arguments", natural arityLimit), ("reads", natural readLimit), ("delivery_origin_edges", natural originLimit),
  ("output_origin_edges", natural originLimit), ("actions", natural actionLimit), ("action_transitions", natural transitionLimit),
  ("total_transitions", natural transitionLimit), ("events", natural transitionLimit), ("output_bytes", natural Output.outputLimit),
  ("reason_utf8_bytes", natural 1024)]

end ANL.Boot.Reference.Summary
