import ANL.BootReferenceRequestWire

namespace ANL.Boot.Reference
open ANL.Boot.Runtime ANL.Boot.Runtime.Session

theorem checkRequestDocument_iff : checkRequestDocument p text = .ok request ↔
    readRequest text = .ok request ∧ RequestValid p request := by
  unfold checkRequestDocument
  cases raw : readRequest text with
  | error e => simp [bind, Except.bind]
  | ok r =>
    simp only [bind, Except.bind, checkRequest_iff, Except.ok.injEq]
    constructor
    · rintro ⟨rfl, valid⟩; exact ⟨rfl, valid⟩
    · rintro ⟨rfl, valid⟩; exact ⟨rfl, valid⟩

theorem checkDocuments_iff : checkDocuments coreText requestText = .ok input ↔
    Wire.checkCoreDocument coreText = .ok input.program ∧ ReferenceAdmissible input.program ∧
      readRequest requestText = .ok input.request ∧ RequestValid input.program input.request := by
  unfold checkDocuments
  cases core : checkCoreDocument coreText with
  | error e =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff]
    intro h
    have other := checkCoreDocument_iff.mpr ⟨h.1, h.2.1⟩
    rw [core] at other
    contradiction
  | ok p =>
    cases req : checkRequestDocument p requestText with
    | error e =>
      simp only [bind, Except.bind, req, reduceCtorEq, false_iff]
      intro h
      have equal := Except.ok.inj (core.symm.trans (checkCoreDocument_iff.mpr ⟨h.1, h.2.1⟩))
      cases equal
      have other := checkRequestDocument_iff.mpr h.2.2
      rw [req] at other
      contradiction
    | ok request =>
      simp only [bind, Except.bind, req, pure, Except.pure, Except.ok.injEq]
      constructor
      · intro equal
        cases equal
        exact ⟨(checkCoreDocument_iff.mp core).1, (checkCoreDocument_iff.mp core).2,
          (checkRequestDocument_iff.mp req).1, (checkRequestDocument_iff.mp req).2⟩
      · intro h
        have equal := Except.ok.inj (core.symm.trans (checkCoreDocument_iff.mpr ⟨h.1, h.2.1⟩))
        have equalRequest := Except.ok.inj (req.symm.trans (checkRequestDocument_iff.mpr (equal.symm ▸ h.2.2)))
        cases equal
        cases equalRequest
        cases input
        rfl

theorem core_failure_first (failure : checkCoreDocument coreText = .error e) :
    checkDocuments coreText requestText = .error e := by
  simp [checkDocuments, failure, bind, Except.bind]

theorem checked_program (checked : checkDocuments coreText requestText = .ok input) :
    WellFormedProgram input.program ∧ ReferenceAdmissible input.program :=
  ⟨Wire.checked_wellFormed (checkDocuments_iff.mp checked).1, (checkDocuments_iff.mp checked).2.1⟩

theorem checked_request (checked : checkDocuments coreText requestText = .ok input) :
    RequestValid input.program input.request := (checkDocuments_iff.mp checked).2.2.2

theorem checked_start_exists (checked : checkDocuments coreText requestText = .ok input) :
    ∃ first, Start input.program input.request.environment first :=
  Start.exists (checked_program checked).1 (checked_request checked).input

theorem checked_budget_bounds (checked : checkDocuments coreText requestText = .ok input) :
    budgets input.request.actions ≤ 65536 ∧ input.request.actions.length ≤ 32 ∧
      input.request.environment.reads.length ≤ 65536 ∧
      deliveryEdges input.request.environment.delivery ≤ 128 := by
  have valid := checked_request checked
  exact ⟨valid.limits.totalBudget, valid.limits.actions, valid.limits.reads, valid.limits.origin⟩

theorem checked_runtime_input (checked : checkDocuments coreText requestText = .ok input) :
    checkInput input.program input.request.environment = true :=
  checkInput_iff.mpr (checked_request checked).input

theorem scalar_failure_first (bad : ¬ RequestScalars request) :
    checkRequest p request = .error (invalid "invalid reference request scalar") := by
  have h : checkScalars request = false := Bool.eq_false_iff.mpr (fun h => bad (checkScalars_iff.mp h))
  simp [checkRequest, h]

theorem limit_precedes_shape_and_scope (scalars : RequestScalars request) (bad : ¬ RequestLimits request) :
    checkRequest p request = .error (limit "reference request structural or budget limit") := by
  have h : checkLimits request = false := Bool.eq_false_iff.mpr (fun h => bad (checkLimits_iff.mp h))
  simp [checkRequest, checkScalars_iff.mpr scalars, h]

theorem shape_precedes_scope (scalars : RequestScalars request) (limits : RequestLimits request)
    (bad : ¬ ActionShape request.actions) :
    checkRequest p request = .error (invalid "invalid reference action sequence") := by
  have h : checkShape request.actions = false := Bool.eq_false_iff.mpr (fun h => bad (checkShape_iff.mp h))
  simp [checkRequest, checkScalars_iff.mpr scalars, checkLimits_iff.mpr limits, h]

end ANL.Boot.Reference
