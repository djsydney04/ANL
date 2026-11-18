import ANL.BootReferenceProjection

namespace ANL.Boot.Reference.Projection
open ANL.Boot.Runtime ANL.Boot.Runtime.Session

/-- Fixed exported identity, independent of an unchecked Program's arbitrary strings. -/
def IdentityEncodable (identity : Identity) : Prop :=
  identity.semanticRevision = "anl-boot-rv64-virt-v1" ∧
  identity.ordinaryRevision = "anl-words-v1" ∧ identity.targetProfile = "rv64-virt-sbi-v1"
instance (identity : Identity) : Decidable (IdentityEncodable identity) := by unfold IdentityEncodable; infer_instance

/-- Required before projecting an exportable report, including all raw recovery paths. -/
structure ContextEncodable (p : Program) : Prop where
  identity : IdentityEncodable (identityView p)
  boot : p.entries.boot.function < declarationLimit
  hardware : p.entries.hardware.function < declarationLimit
  language : p.entries.language.function < declarationLimit

instance (p : Program) : Decidable (ContextEncodable p) :=
  decidable_of_iff (IdentityEncodable (identityView p) ∧ p.entries.boot.function < declarationLimit ∧
    p.entries.hardware.function < declarationLimit ∧ p.entries.language.function < declarationLimit)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.identity, h.boot, h.hardware, h.language⟩⟩

/-- None authorizes only the later null-identity infrastructure envelope, never raw identity export. -/
def projectForExport (p : Program) (request : Request) (result : Session.Result) : Option Report :=
  if ContextEncodable p then some (projectReport p request result) else none

 theorem projectForExport_iff : projectForExport p request result = some report ↔
    ContextEncodable p ∧ projectReport p request result = report := by
  by_cases context : ContextEncodable p <;> simp [projectForExport, context]

 theorem projectForExport_reject (bad : ¬ ContextEncodable p) : projectForExport p request result = none := by
  simp [projectForExport, bad]

 theorem role_index_bound (role : RoleValid p ident params) (admission : ReferenceAdmissible p) :
    ident < declarationLimit := by
  cases role with | intro found _ _ _ =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    exact Nat.lt_of_lt_of_le bound admission.declarations

 theorem checked_context (wf : WellFormedProgram p) (admission : ReferenceAdmissible p) : ContextEncodable p := by
  refine ⟨?_, role_index_bound wf.roles.boot admission, role_index_bound wf.roles.hardware admission,
    role_index_bound wf.roles.language admission⟩
  exact ⟨wf.metadata.revision, wf.metadata.ordinary, congrArg TargetProfile.id wf.metadata.profile⟩

 theorem checked_documents_context (checked : checkDocuments coreText requestText = .ok input) : ContextEncodable input.program :=
  checked_context (checked_program checked).1 (checked_program checked).2

 theorem context_operation_handler (context : ContextEncodable p)
    (valid : Operation.Valid p.entries.hardware.function (.installTrap authority target)) :
    authority = 0 ∧ target < declarationLimit := by
  cases valid
  exact ⟨rfl, context.hardware⟩

 theorem context_observation_function (context : ContextEncodable p) (episode : Episode) :
    episode.function p < declarationLimit := by cases episode <;> first | exact context.boot | exact context.hardware | exact context.language

 theorem projectReport_identity : (projectReport p request result).identity = identityView p := by
  by_cases summary : SummaryEncodable p (summaryView request result)
  · unfold projectReport
    simp only [summary, ↓reduceIte]
    cases found : finalView result with
    | none => rfl
    | some final =>
      by_cases bound : FinalEncodable p final <;> simp [bound, fullReport, projectionFailure]
  · simp [projectReport, summary, projectionFailure]

 theorem exported_identity (exported : projectForExport p request result = some report) :
    IdentityEncodable report.identity := by
  obtain ⟨context, equal⟩ := projectForExport_iff.mp exported
  rw [← equal, projectReport_identity]
  exact context.identity

end ANL.Boot.Reference.Projection
