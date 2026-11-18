import ANL.BootReferenceOutputJson

namespace ANL.Boot.Reference.Output
open Lean ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

inductive ExportError where
  | shape | events | bytes
  deriving DecidableEq, Repr

def ExportError.reason : ExportError → String
  | .shape => "projection_shape_error" | .events => "trace_event_limit" | .bytes => "output_byte_limit"

abbrev Buffer := ANL.Memory.Reference.Buffer

def bufferError : ANL.Memory.Reference.ExportError → ExportError
  | .events => .events | .bytes => .bytes

def appendText (buffer : Buffer) (text : String) : Except ExportError Buffer :=
  (buffer.text text).mapError bufferError

def appendJson (buffer : Buffer) (json : Json) : Except ExportError Buffer :=
  (buffer.json json).mapError bufferError

def appendFields : List (String × Json) → Buffer → Except ExportError Buffer
  | [], buffer => .ok buffer
  | (key, value) :: rest, buffer => do
      let buffer ← appendJson buffer (toJson key)
      let buffer ← appendText buffer ":"
      let buffer ← appendJson buffer value
      let buffer ← appendText buffer ","
      appendFields rest buffer

def appendArray (render : α → Json) : List α → Bool → Buffer → Except ExportError Buffer
  | [], _, buffer => .ok buffer
  | item :: rest, first, buffer => do
      let buffer ← if first then .ok buffer else appendText buffer ","
      let buffer ← appendJson buffer (render item)
      appendArray render rest false buffer

/-- Bounded final count guard; it never counts beyond limit+1 nodes. -/
def countFits : Nat → List α → Bool
  | _, [] => true | 0, _ :: _ => false | limit + 1, _ :: rest => countFits limit rest

/-- Validate each event immediately before its small Json fragment, preserving first-failure order. -/
def appendEvents (p : Program) : List Event → Bool → Buffer → Except ExportError Buffer
  | [], _, buffer => .ok buffer
  | event :: rest, first, buffer => do
      if !decide (EventEncodable p event) then throw .shape
      let buffer ← if first then .ok buffer else appendText buffer ","
      let buffer ← appendJson buffer (eventJson event)
      appendEvents p rest false buffer

def appendUnused (unused : Option UnusedView) (buffer : Buffer) : Except ExportError Buffer := do
  match unused with
  | none => appendText buffer "null"
  | some view =>
      let buffer ← appendText buffer "{"
      let buffer ← appendFields [("reads_total", toJson view.readsTotal), ("reads_consumed", toJson view.readsConsumed)] buffer
      let buffer ← appendText buffer "\"reads_remaining\":["
      let buffer ← appendArray toJson view.readsRemaining true buffer
      let buffer ← appendText buffer "],\"delivery\":"
      let buffer ← appendJson buffer (optionalJson deliveryJson view.delivery)
      let buffer ← appendText buffer ",\"delivery_state\":"
      let buffer ← appendJson buffer (toJson (deliveryName view.deliveryState))
      appendText buffer "}"

/-- Internal serializer. Its trusted callers supply ContextEncodable and guarded projected summaries/finals. -/
def encodeBuffer (p : Program) (report : Report) : Except ExportError Buffer := do
  if let some trace := report.trace then
    if !countFits transitionLimit trace.revEvents then throw .events
  let buffer ← appendText ANL.Memory.Reference.Buffer.empty "{"
  let buffer ← appendFields (headerFields (some report.identity) report.status report.reason report.summary) buffer
  let buffer ← appendText buffer "\"actions\":["
  let buffer ← appendArray (rowJson p) (report.summary.map SummaryView.rows |>.getD []) true buffer
  let buffer ← appendText buffer "],\"final\":"
  let buffer ← appendJson buffer (optionalJson finalJson report.final)
  let buffer ← appendText buffer ",\"trace\":"
  let buffer ← match report.trace with
    | none => appendText buffer "null"
    | some trace => do
        let buffer ← appendText buffer "{\"schema\":\"anl-boot-events-v1\",\"events\":["
        let buffer ← appendEvents p trace.revEvents.reverse true buffer
        appendText buffer "]}"
  let buffer ← appendText buffer ",\"unused_input\":"
  let buffer ← appendUnused (report.summary.map SummaryView.unused) buffer
  appendText buffer "}"

/-- Trace omission is always an explicit error; no semantic counter/summary is changed. -/
def exportFailure (report : Report) (error : ExportError) : Report :=
  {report with status := .error, reason := error.reason, trace := none}

inductive MinimalReason where
  | projectionShape | summaryLimit
  deriving DecidableEq, Repr

def MinimalReason.text : MinimalReason → String
  | .projectionShape => "projection_shape_error" | .summaryLimit => "output_summary_limit"

def canonicalIdentity : Identity := ⟨"anl-boot-rv64-virt-v1", "anl-words-v1", "rv64-virt-sbi-v1"⟩

/-- Fixed unavailable-summary envelope. The known flag may be true only after the checked context gateway. -/
def minimalJson (known : Bool) (reason : MinimalReason) : Json := Json.mkObj (
  headerFields (if known then some canonicalIdentity else none) .error reason.text none ++ [
    ("actions", toJson ([] : List Json)), ("final", .null), ("trace", .null), ("unused_input", .null)])

/-- Fixed ASCII variants, independent of the opaque Json.compress implementation. -/
def minimalText : Bool → MinimalReason → String
  | false, .projectionShape => "{\"actions\":[],\"actions_executed\":null,\"actions_requested\":null,\"actions_unexecuted\":null,\"failure_action\":null,\"final\":null,\"limits\":{\"action_transitions\":65536,\"actions\":32,\"call_arguments\":64,\"core_bytes\":1048576,\"core_json_depth\":1024,\"core_logical_depth\":128,\"declarations\":128,\"delivery_origin_edges\":128,\"events\":65536,\"id\":\"anl-boot-reference-limits-v1\",\"output_bytes\":8388608,\"output_origin_edges\":128,\"parameters\":64,\"reads\":65536,\"reason_utf8_bytes\":1024,\"request_bytes\":1048576,\"request_json_depth\":16,\"term_nodes\":8192,\"total_transitions\":65536},\"ordinary_semantic_revision\":null,\"reason\":\"projection_shape_error\",\"schema\":\"anl-boot-reference-run-v1\",\"semantic_revision\":null,\"status\":\"error\",\"target_profile\":null,\"total_used\":null,\"trace\":null,\"unused_input\":null}"
  | false, .summaryLimit => "{\"actions\":[],\"actions_executed\":null,\"actions_requested\":null,\"actions_unexecuted\":null,\"failure_action\":null,\"final\":null,\"limits\":{\"action_transitions\":65536,\"actions\":32,\"call_arguments\":64,\"core_bytes\":1048576,\"core_json_depth\":1024,\"core_logical_depth\":128,\"declarations\":128,\"delivery_origin_edges\":128,\"events\":65536,\"id\":\"anl-boot-reference-limits-v1\",\"output_bytes\":8388608,\"output_origin_edges\":128,\"parameters\":64,\"reads\":65536,\"reason_utf8_bytes\":1024,\"request_bytes\":1048576,\"request_json_depth\":16,\"term_nodes\":8192,\"total_transitions\":65536},\"ordinary_semantic_revision\":null,\"reason\":\"output_summary_limit\",\"schema\":\"anl-boot-reference-run-v1\",\"semantic_revision\":null,\"status\":\"error\",\"target_profile\":null,\"total_used\":null,\"trace\":null,\"unused_input\":null}"
  | true, .projectionShape => "{\"actions\":[],\"actions_executed\":null,\"actions_requested\":null,\"actions_unexecuted\":null,\"failure_action\":null,\"final\":null,\"limits\":{\"action_transitions\":65536,\"actions\":32,\"call_arguments\":64,\"core_bytes\":1048576,\"core_json_depth\":1024,\"core_logical_depth\":128,\"declarations\":128,\"delivery_origin_edges\":128,\"events\":65536,\"id\":\"anl-boot-reference-limits-v1\",\"output_bytes\":8388608,\"output_origin_edges\":128,\"parameters\":64,\"reads\":65536,\"reason_utf8_bytes\":1024,\"request_bytes\":1048576,\"request_json_depth\":16,\"term_nodes\":8192,\"total_transitions\":65536},\"ordinary_semantic_revision\":\"anl-words-v1\",\"reason\":\"projection_shape_error\",\"schema\":\"anl-boot-reference-run-v1\",\"semantic_revision\":\"anl-boot-rv64-virt-v1\",\"status\":\"error\",\"target_profile\":\"rv64-virt-sbi-v1\",\"total_used\":null,\"trace\":null,\"unused_input\":null}"
  | true, .summaryLimit => "{\"actions\":[],\"actions_executed\":null,\"actions_requested\":null,\"actions_unexecuted\":null,\"failure_action\":null,\"final\":null,\"limits\":{\"action_transitions\":65536,\"actions\":32,\"call_arguments\":64,\"core_bytes\":1048576,\"core_json_depth\":1024,\"core_logical_depth\":128,\"declarations\":128,\"delivery_origin_edges\":128,\"events\":65536,\"id\":\"anl-boot-reference-limits-v1\",\"output_bytes\":8388608,\"output_origin_edges\":128,\"parameters\":64,\"reads\":65536,\"reason_utf8_bytes\":1024,\"request_bytes\":1048576,\"request_json_depth\":16,\"term_nodes\":8192,\"total_transitions\":65536},\"ordinary_semantic_revision\":\"anl-words-v1\",\"reason\":\"output_summary_limit\",\"schema\":\"anl-boot-reference-run-v1\",\"semantic_revision\":\"anl-boot-rv64-virt-v1\",\"status\":\"error\",\"target_profile\":\"rv64-virt-sbi-v1\",\"total_used\":null,\"trace\":null,\"unused_input\":null}"

def minimalBytes (known : Bool) (reason : MinimalReason) : ByteArray :=
  (minimalText known reason).toUTF8.push 10

structure Encoded where
  status : Status
  bytes : ByteArray

def minimal (known : Bool) (reason : MinimalReason) : Encoded := ⟨.error, minimalBytes known reason⟩

/-- Internal: exactly one full attempt, one trace-free attempt, then a fixed bounded error. No stdout writes. -/
def encodeProjected (p : Program) (report : Report) : Encoded :=
  match encodeBuffer p report with
  | .ok buffer => ⟨report.status, buffer.finish⟩
  | .error error =>
    match encodeBuffer p (exportFailure report error) with
    | .ok buffer => ⟨.error, buffer.finish⟩
    | .error _ => minimal true .summaryLimit

/-- The only session-result export entry: raw context failure never exports raw identity strings. -/
def encodeResult (p : Program) (request : Request) (result : Session.Result) : Encoded :=
  match projectForExport p request result with
  | none => minimal false .projectionShape
  | some report => encodeProjected p report

/-- Pure pre-state error data; its actual parser/IO provenance belongs to the later gateway. -/
inductive PrestartFailure where
  | core (error : ANL.Memory.Wire.DecodeError)
  | request (error : ANL.Memory.Wire.DecodeError)
  | invocation (message : String)
  | inputIO (message : String)
  | internal (message : String)
  deriving Repr

def PrestartFailure.status : PrestartFailure → Status
  | .core error | .request error => match error.kind with
      | .invalid => .rejected | .resourceLimit => .resourceLimit
  | _ => .error

def PrestartFailure.code : PrestartFailure → String
  | .core error => match error.kind with
      | .invalid => "core_rejected" | .resourceLimit => "core_resource_limit"
  | .request error => match error.kind with
      | .invalid => "request_rejected" | .resourceLimit => "request_resource_limit"
  | .invocation _ => "invocation_error" | .inputIO _ => "input_io_error" | .internal _ => "internal_state_error"

def PrestartFailure.message : PrestartFailure → String
  | .core error | .request error => error.message
  | .invocation message | .inputIO message | .internal message => message

def PrestartFailure.reason (failure : PrestartFailure) : String :=
  ANL.Memory.Wire.IOBoundary.reason (failure.code ++
    if failure.message.isEmpty then "" else ": " ++ failure.message)

def knownIdentity : Option Program → Option Identity
  | none => none
  | some p => if ContextEncodable p then some canonicalIdentity else none

def prestartJson (identity : Option Identity) (failure : PrestartFailure) : Json := Json.mkObj (
  headerFields identity failure.status failure.reason none ++ [
    ("actions", toJson ([] : List Json)), ("final", .null), ("trace", .null), ("unused_input", .null)])

/-- No state or fabricated zero counters. The caller supplies knowledge only after its actual Core check. -/
def encodePrestart (knowledge : Option Program) (failure : PrestartFailure) : Encoded :=
  let identity := knownIdentity knowledge
  match appendJson ANL.Memory.Reference.Buffer.empty (prestartJson identity failure) with
  | .ok buffer => ⟨failure.status, buffer.finish⟩
  | .error _ => minimal identity.isSome .summaryLimit

end ANL.Boot.Reference.Output
