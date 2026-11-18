import ANL.BootV3Authority
import ANL.BootV2RuntimeFrontierProofs

namespace ANL.Boot.V3.Runtime
open ANL.Words
open ANL.Boot.V2.Runtime
variable {p : ANL.Boot.V3.Program} {env : V2.Runtime.Environment} {s : V2.Runtime.State}
set_option linter.unusedSimpArgs false

theorem located_typed (wf : WellFormedProgram p) (located : V2.Origin.Located p origin term) :
    ∃ context ty, HasType p.signatures context [] term ty := by
  cases located with | intro found occurrence =>
    exact ANL.Boot.Runtime.occurrence_typed occurrence (wf.at found).typed

theorem located_call_result (wf : WellFormedProgram p)
    (located : V2.Origin.Located p origin (.call ty ident args))
    (found : p.functions[ident]? = some (.primitive row)) : ty = row.operation.result := by
  obtain ⟨context, result, typed⟩ := located_typed wf located
  cases typed with
  | call signature _ _ =>
    have same := Option.some.inj (signature.symm.trans (declaration_signature found))
    cases same
    exact (wf.at found).result

theorem located_illegal_only_boot (wf : WellFormedProgram p)
    (located : V2.Origin.Located p origin (.call ty ident args))
    (found : p.functions[ident]? = some (.primitive row))
    (operation : row.operation = .illegalInstruction 0) : origin.function = p.entries.boot.function := by
  cases located with | intro caller occurrence =>
    exact wf.illegal_call_only_boot caller (occurrence.calls (by simp [ANL.Boot.calls])) found operation

theorem captureLegacy_complete (wf : WellFormedProgram p) (typed : Words.State.Typed p.carrier s.machine t)
    (aligned : V2.Origin.Aligned p s.machine s.origins)
    (controlEq : s.machine.control = .invoke ident none values)
    (found : p.functions[ident]? = some (.primitive row)) (operation : row.operation = .legacy op)
    (ordinal : 0 < s.nextOrdinal) : ∃ q, CapturedLegacy p s q := by
  obtain ⟨ty, terms, located, arity⟩ := invoke_source_at aligned controlEq
  have policy : V2.PrimitiveValid p row := wf.at found
  have allowed := policy.operation
  rw [operation] at allowed
  have legacyAllowed : op.Valid p.entries.hardware.function := by cases allowed with | legacy h => exact h
  have params : values.reverse.map Val.type = op.params := by
    simpa [operation, V2.Operation.params] using (typed_invoke_arguments_at typed controlEq found).trans policy.params
  have result : ty = op.result := by simpa [operation, V2.Operation.result] using located_call_result wf located found
  refine ⟨_, .invoke controlEq found operation ?_⟩
  refine ⟨rfl, aligned.function, ordinal, legacyAllowed, params, ?_⟩
  simp only [controlEq, found, V2.Origin.lookup_iff.mpr located]
  exact ⟨True.intro, True.intro, operation, result, by simpa using arity.symm, True.intro⟩

theorem captureFault_complete (wf : WellFormedProgram p) (input : InputValid p env)
    (typed : Words.State.Typed p.carrier s.machine t) (aligned : V2.Origin.Aligned p s.machine s.origins)
    (controlEq : s.machine.control = .invoke ident none values)
    (found : p.functions[ident]? = some (.primitive row)) (operation : row.operation = .illegalInstruction 0)
    (episode : s.episode = .boot) (unused : s.forwardingUsed = false)
    (ordinal : 0 < s.nextOrdinal) : ∃ q, CapturedFault p env s q := by
  obtain ⟨ty, terms, located, arity⟩ := invoke_source_at aligned controlEq
  have policy : V2.PrimitiveValid p row := wf.at found
  have signature := policy.illegal_signature operation
  have emptyReverse : values.reverse = [] :=
    List.map_eq_nil_iff.mp ((typed_invoke_arguments_at typed controlEq found).trans signature.1)
  have empty : values = [] := by simpa using congrArg List.reverse emptyReverse
  subst values
  have termsEmpty : terms = [] := List.length_eq_zero_iff.mp (by simpa using arity.symm)
  subst terms
  have result : ty = unitTy := by simpa [operation, V2.Operation.result] using located_call_result wf located found
  subst ty
  have source := located_illegal_only_boot wf located found operation
  have current : s.machine.current.function = p.entries.boot.function := aligned.function.symm.trans source
  have member : row ∈ p.primitives := by
    apply List.mem_filterMap.mpr
    exact ⟨.primitive row, List.mem_of_getElem? found, rfl⟩
  have presence := input.fault.presence.mpr ⟨row, member, operation⟩
  cases site : env.fault.illegalSitePc with
  | none => simp [site] at presence
  | some pc =>
    have operationAt : p.operationAt ident = some (.illegalInstruction 0) := by
      simp [V2.Program.operationAt, found, operation]
    refine ⟨_, .invoke controlEq operationAt site ?_⟩
    refine ⟨?_, ordinal, rfl, unused⟩
    refine ⟨episode, current, source, rfl, site, ?_⟩
    simp [controlEq, operationAt, V2.Origin.lookup_iff.mpr located]

theorem primitive_capture_complete (wf : WellFormedProgram p) (input : InputValid p env)
    (typed : Words.State.Typed p.carrier s.machine t) (aligned : V2.Origin.Aligned p s.machine s.origins)
    (frontier : V2.Origin.PrimitiveFrontier p s.machine) (episode : s.episode = .boot)
    (unused : s.forwardingUsed = false) (ordinal : 0 < s.nextOrdinal) :
    (∃ q, CapturedLegacy p s q) ∨ ∃ q, CapturedFault p env s q := by
  obtain ⟨ident, values, row, controlEq, found⟩ := frontier
  cases operation : row.operation with
  | legacy op => exact .inl (captureLegacy_complete wf typed aligned controlEq found operation ordinal)
  | illegalInstruction authority =>
    have allowed := (wf.at found).operation
    rw [operation] at allowed
    cases allowed
    exact .inr (captureFault_complete wf input typed aligned controlEq found operation episode unused ordinal)

end ANL.Boot.V3.Runtime
