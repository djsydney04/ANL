import ANL.BootRuntimeBoundaryProofs

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

/-- Ordinary typing excludes invalid values but does not restrict the five shared trap tags. -/
def SupportedResult : Result → Prop
  | .trap kind => ∃ tag, LanguageTag kind tag
  | _ => True

def SupportedControl : Control → Prop
  | .trap kind => ∃ tag, LanguageTag kind tag
  | _ => True

 theorem legacyResult_supported (result : APL.Result) : SupportedResult (legacyResult result) := by
  cases result with
  | value _ | invalid => trivial
  | trap kind => cases kind <;> first | exact ⟨_, .overflow⟩ | exact ⟨_, .division⟩

 theorem wordResult_supported (result : ANL.Word.Outcome ANL.Word.Word) : SupportedResult (wordResult result) := by
  cases result with
  | value _ => simp only [wordResult]; split <;> trivial
  | invalidInput => trivial
  | trap kind => cases kind <;> first | exact ⟨_, .overflow⟩ | exact ⟨_, .division⟩ | exact ⟨_, .shift⟩

 theorem signedResult_supported (result : ANL.Word.Outcome Int) : SupportedResult (signedResult result) := by
  cases result with
  | value _ => simp only [signedResult]; split <;> trivial
  | invalidInput => trivial
  | trap kind => cases kind <;> first | exact ⟨_, .overflow⟩ | exact ⟨_, .division⟩ | exact ⟨_, .shift⟩

 theorem wordLiteral_supported : SupportedResult (wordLiteral width value) := by
  unfold wordLiteral
  split
  · trivial
  · exact wordResult_supported _

 theorem unary_supported : SupportedResult (Words.unary op value) := by
  unfold Words.unary
  repeat' split
  all_goals first | exact legacyResult_supported _ | exact wordResult_supported _ | trivial

 theorem binary_supported : SupportedResult (Words.binary op a b) := by
  unfold Words.binary
  repeat' split
  all_goals first | exact legacyResult_supported _ | exact wordResult_supported _ | trivial

 theorem convert_supported : SupportedResult (Words.convert mode target value) := by
  unfold Words.convert
  repeat' split
  all_goals first | exact wordResult_supported _ | exact signedResult_supported _ | trivial

 theorem construct_supported : SupportedResult (Words.construct values) := by
  unfold Words.construct
  split <;> trivial

 theorem project_supported : SupportedResult (Words.project value index) := by
  unfold Words.project
  repeat' split
  all_goals trivial

 theorem resume_supported (supported : SupportedResult result) : SupportedControl (resume result a k w).control := by
  cases result <;> exact supported

 theorem beginArguments_supported : SupportedControl (beginArguments f loan args values a k w).control := by
  cases args <;> trivial

 theorem admitted_step_supported (admitted : Origin.Admitted p s)
    (step : Words.Step p.carrier responses s next) : SupportedControl next.control := by
  cases step <;> simp_all only [Origin.Admitted]
  all_goals first
    | trivial
    | exact resume_supported wordLiteral_supported
    | exact resume_supported unary_supported
    | exact resume_supported binary_supported
    | exact resume_supported convert_supported
    | exact resume_supported construct_supported
    | exact resume_supported project_supported
    | exact beginArguments_supported

 theorem OriginStep.supported (step : Origin.Step p responses s origins next metadata) : SupportedControl next.control := by
  cases step with | ordinary admitted actual _ _ => exact admitted_step_supported admitted actual

 theorem SupportedControl.language (supported : SupportedControl (.trap kind)) : ∃ tag, LanguageTag kind tag := supported
 theorem SupportedControl.not_length (supported : SupportedControl ctl) : ctl ≠ .trap .invalidLength := by
  intro eq; subst ctl; obtain ⟨tag, impossible⟩ := supported; cases impossible
 theorem SupportedControl.not_bounds (supported : SupportedControl ctl) : ctl ≠ .trap .indexOutOfBounds := by
  intro eq; subst ctl; obtain ⟨tag, impossible⟩ := supported; cases impossible

end ANL.Boot.Runtime
