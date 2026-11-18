import ANL.BootSummarySuccess

namespace ANL.Boot.Reference.Output.Total
open ANL.Boot.Runtime ANL.Boot.Runtime.Session Projection

/-- Keep the original full encoder and first failure. Only its trace-null retry changes. -/
def encodeProjected (p : Program) (report : Report) : Encoded :=
  match Output.encodeBuffer p report with
  | .ok buffer => ⟨report.status, buffer.finish⟩
  | .error firstError =>
    match Summary.recovery p (Output.exportFailure report firstError) ANL.Memory.Reference.Buffer.empty with
    | .ok buffer => ⟨.error, buffer.finish⟩
    | .error _ => Output.minimal true .summaryLimit

/-- Raw context failure uses the original fixed null-identity envelope. -/
def encodeResult (p : Program) (request : Request) (result : Session.Result) : Encoded :=
  match projectForExport p request result with
  | none => Output.minimal false .projectionShape
  | some report => encodeProjected p report

/-- Total bounded prestart serialization; the defensive branch is unreachable for knownIdentity. -/
def encodePrestart (knowledge : Option Program) (failure : PrestartFailure) : Encoded :=
  let identity := Output.knownIdentity knowledge
  match Summary.prestart identity failure ANL.Memory.Reference.Buffer.empty with
  | .ok buffer => ⟨failure.status, buffer.finish⟩
  | .error _ => Output.minimal identity.isSome .summaryLimit

end ANL.Boot.Reference.Output.Total
