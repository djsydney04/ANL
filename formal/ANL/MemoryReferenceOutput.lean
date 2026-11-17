import ANL.MemoryReference
import ANL.MemoryWireIO

namespace ANL.Memory.Reference
open Lean

structure TraceView where
  semanticRevision : String
  profile : Profile
  revEvents : List Event
  completion : Completion
  deriving Repr

def TraceView.events (trace : TraceView) : List Event := trace.revEvents.reverse

structure Report where
  status : Status
  semanticRevision : String := "anl-owned-buffers-v1"
  profile : Option Profile := none
  budgets : Option (Nat × Nat) := none
  resourceReason : Option Tool.Limit := none
  reason : String := ""
  meter : Option MeterView := none
  trace : Option TraceView := none
  deriving Repr

def resultReport (p : Program) (fuel budget : Nat) (result : Tool.Result) : Report :=
  let retained := result.configuration
  match classify result with
  | none => {
      status := .error, semanticRevision := p.semanticRevision, profile := some p.profile,
      budgets := some (fuel, budget), reason := "internal_state_error", meter := some (meterView retained.meter)}
  | some completion => {
      status := completion.status, semanticRevision := p.semanticRevision, profile := some p.profile,
      budgets := some (fuel, budget),
      resourceReason := (match completion with | .resourceLimit reason => some reason | _ => none),
      reason := completion.reason, meter := some (meterView retained.meter),
      trace := some ⟨p.semanticRevision, p.profile, retained.machine.world.revTrace, completion⟩}

def siteJson (site : Site) : Json := Json.mkObj [
  ("function", toJson site.function), ("heap", toJson site.heap)]

def responseName : Response → String
  | .success => "success" | .refused => "refused"

def eventJson : Event → Json
  | .request ordinal site length response => Json.mkObj [
      ("kind", toJson "request"), ("request", toJson (toString ordinal)),
      ("site", siteJson site), ("length", toJson (toString length)),
      ("response", toJson (responseName response))]
  | .release ordinal site => Json.mkObj [
      ("kind", toJson "release"), ("request", toJson (toString ordinal)), ("site", siteJson site)]
  | .emptyOpen ordinal site => Json.mkObj [
      ("kind", toJson "empty_open"), ("empty", toJson (toString ordinal)), ("site", siteJson site)]
  | .emptyClose ordinal site => Json.mkObj [
      ("kind", toJson "empty_close"), ("empty", toJson (toString ordinal)), ("site", siteJson site)]

def completionJson : Completion → Json
  | .value value => Json.mkObj [("kind", toJson "value"), ("type", toJson "i64"),
      ("value", toJson (toString value.val))]
  | .trap kind => Json.mkObj [("kind", toJson "trap"), ("trap", toJson (trapName kind))]
  | .resourceLimit _ => Json.mkObj [("kind", toJson "resource_limit")]
  | .transitionLimit => Json.mkObj [("kind", toJson "infrastructure"),
      ("reason", toJson "administrative transition budget exhausted")]

def meterJson (m : MeterView) : Json := Json.mkObj [
  ("fuel_remaining", toJson (toString m.fuelRemaining)),
  ("active_slots", toJson (toString m.activeSlots)),
  ("live_cells", toJson (toString m.liveCells)),
  ("tuple_fields", toJson (toString m.tupleFields)),
  ("expression_depth", toJson (toString m.expressionDepth))]

def optionalJson (f : α → Json) : Option α → Json
  | none => .null | some value => f value

def headerFields (r : Report) : List (String × Json) := [
  ("schema", toJson "anl-memory-reference-run-v1"), ("status", toJson r.status.name),
  ("semantic_revision", toJson r.semanticRevision),
  ("allocation_profile", optionalJson Wire.IOBoundary.profileJson r.profile),
  ("fuel", optionalJson (fun b => toJson (toString b.1)) r.budgets),
  ("transition_budget", optionalJson (fun b => toJson (toString b.2)) r.budgets),
  ("resource_reason", optionalJson (toJson ∘ limitName) r.resourceReason),
  ("reason", toJson (Wire.IOBoundary.reason r.reason)),
  ("meter", optionalJson meterJson r.meter)]

inductive ExportError where
  | events | bytes
  deriving DecidableEq, Repr

def ExportError.reason : ExportError → String
  | .events => "trace_event_limit" | .bytes => "output_byte_limit"

/-- The proof constrains the actual buffer, not a separately maintained size claim. -/
structure Buffer where
  bytes : ByteArray
  bounded : bytes.size ≤ maxOutputBytes - 1

def Buffer.empty : Buffer := ⟨ByteArray.empty, by decide⟩

/-- Check capacity before append allocates the combined byte array. -/
def Buffer.append (buffer : Buffer) (chunk : ByteArray) : Except ExportError Buffer :=
  if h : buffer.bytes.size + chunk.size ≤ maxOutputBytes - 1 then
    .ok ⟨buffer.bytes ++ chunk, by simpa using h⟩
  else .error .bytes

def Buffer.text (buffer : Buffer) (text : String) : Except ExportError Buffer :=
  buffer.append text.toUTF8

def Buffer.json (buffer : Buffer) (value : Json) : Except ExportError Buffer :=
  buffer.text value.compress

def Buffer.finish (buffer : Buffer) : ByteArray := buffer.bytes.push 10

/-- Counts at most limit+1 nodes, once at the final export boundary. -/
def eventsFit : Nat → List Event → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: rest => eventsFit limit rest

def appendFields : List (String × Json) → Buffer → Except ExportError Buffer
  | [], buffer => .ok buffer
  | (key, value) :: rest, buffer => do
      let buffer ← buffer.json (toJson key)
      let buffer ← buffer.text ":"
      let buffer ← buffer.json value
      let buffer ← buffer.text ","
      appendFields rest buffer

def appendEvents : List Event → Bool → Buffer → Except ExportError Buffer
  | [], _, buffer => .ok buffer
  | event :: rest, first, buffer => do
      let buffer ← if first then .ok buffer else buffer.text ","
      let buffer ← buffer.json (eventJson event)
      appendEvents rest false buffer

def encodeBuffer (r : Report) : Except ExportError Buffer := do
  -- Do not reverse an oversized event list or build one whole trace Json value.
  if let some trace := r.trace then
    if !eventsFit maxEvents trace.revEvents then throw .events
  let buffer ← Buffer.empty.text "{"
  let buffer ← appendFields (headerFields r) buffer
  let buffer ← buffer.text "\"trace\":"
  match r.trace with
  | none => buffer.text "null}"
  | some trace =>
    let buffer ← buffer.text "{"
    let buffer ← appendFields [
      ("schema", toJson "anl-memory-trace-v1"),
      ("semantic_revision", toJson trace.semanticRevision),
      ("allocation_profile", Wire.IOBoundary.profileJson trace.profile)] buffer
    let buffer ← buffer.text "\"events\":["
    let buffer ← appendEvents trace.events true buffer
    let buffer ← buffer.text "],\"completion\":"
    let buffer ← buffer.json (completionJson trace.completion)
    buffer.text "}}"

def encode (r : Report) : Except ExportError ByteArray := do
  return (← encodeBuffer r).finish

/-- Infrastructure fallback keeps the snapshot, but makes no successful trace claim. -/
def exportFailure (r : Report) (error : ExportError) : Report :=
  {r with status := .error, resourceReason := none, reason := error.reason, trace := none}

 theorem buffer_finish_bound (buffer : Buffer) : buffer.finish.size ≤ maxOutputBytes := by
  have h := buffer.bounded
  simp only [Buffer.finish, ByteArray.size_push]
  unfold maxOutputBytes at *
  omega

 theorem encode_bound (h : encode r = .ok bytes) : bytes.size ≤ maxOutputBytes := by
  unfold encode at h
  cases hb : encodeBuffer r with
  | error e => simp [hb, bind, Except.bind] at h
  | ok buffer =>
    simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst bytes
    exact buffer_finish_bound buffer

 theorem eventsFit_iff : eventsFit limit events = true ↔ events.length ≤ limit := by
  induction limit generalizing events with
  | zero => cases events <;> simp [eventsFit]
  | succ n ih => cases events <;> simp [eventsFit, ih, Nat.succ_le_succ_iff]

 theorem resultReport_meter : (resultReport p fuel budget result).meter =
    some (meterView result.configuration.meter) := by
  unfold resultReport
  split <;> rfl

 theorem resultReport_trace (h : (resultReport p fuel budget result).trace = some trace) :
    trace.semanticRevision = p.semanticRevision ∧ trace.profile = p.profile ∧
    trace.events = result.configuration.machine.world.trace ∧ classify result = some trace.completion := by
  unfold resultReport at h
  split at h
  · cases h
  next completion hc =>
    simp only [Option.some.injEq] at h
    cases h
    exact ⟨rfl, rfl, rfl, hc⟩

 theorem exportFailure_retained : (exportFailure r error).meter = r.meter ∧
    (exportFailure r error).profile = r.profile ∧ (exportFailure r error).budgets = r.budgets ∧
    (exportFailure r error).trace = none := ⟨rfl, rfl, rfl, rfl⟩

end ANL.Memory.Reference
