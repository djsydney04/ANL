import ANL.BootSessionCore

namespace ANL.Boot.Runtime.Session
variable {p : Program} {s : State}

theorem checkShape_iff : checkShape actions = true ↔ ActionShape actions := by
  cases actions with
  | nil => simp [checkShape, ActionShape]
  | cons first rest =>
    cases first with | mk kind budget =>
      cases kind <;> simp [checkShape, ActionShape, List.all_eq_true]
      constructor
      · intro valid; exact ⟨budget, rest, ⟨rfl, rfl⟩, valid⟩
      · rintro ⟨_, _, ⟨rfl, rfl⟩, valid⟩; exact valid

theorem ObservationView.compute (view : ObservationView p s observed) : observe p s = observed := by
  cases view with
  | absent absent => exact observe_none_iff.mpr absent
  | present present => exact present.compute

theorem observationView_iff : observe p s = observed ↔ ObservationView p s observed := by
  constructor
  · intro eq
    cases observed with
    | none => exact .absent (observe_none_iff.mp eq)
    | some kind => exact .present (observe_iff.mp eq)
  · exact ObservationView.compute

theorem nextKind_present (view : Observation p s observed) :
    nextKind reason (some observed) = some kind ↔ Applicable p (some reason) s kind := by
  constructor
  · intro eq
    cases reason <;> simp only [nextKind, Option.some.injEq] at eq
    all_goals first | contradiction | (subst kind; exact .resumed rfl trivial view)
  · intro allowed
    cases allowed with
    | fresh impossible => contradiction
    | continued reasonEq absent => exact False.elim (absent _ view)
    | resumed reasonEq nonterminal _ =>
      cases reasonEq
      cases reason <;> first | rfl | exact False.elim nonterminal

theorem nextKind_absent (absent : ∀ observed, ¬ Observation p s observed) :
    nextKind reason none = some kind ↔ Applicable p (some reason) s kind := by
  constructor
  · intro eq
    cases reason <;> simp [nextKind] at eq
    subst kind
    exact .continued rfl absent
  · intro allowed
    cases allowed with
    | fresh impossible => contradiction
    | continued reasonEq _ => cases reasonEq; rfl
    | resumed _ _ observed => exact False.elim (absent _ observed)

theorem nextKind_iff (view : ObservationView p s observed) :
    nextKind reason observed = some kind ↔ Applicable p (some reason) s kind := by
  cases view with
  | absent absent => exact nextKind_absent absent
  | present present => exact nextKind_present present

theorem applicable_iff : applicable p previous s kind = true ↔ Applicable p previous s kind := by
  cases previous with
  | none =>
    simp only [applicable, beq_iff_eq]
    constructor
    · intro eq; subst kind; exact .fresh rfl
    · intro allowed; cases allowed <;> first | rfl | contradiction
  | some reason =>
    simp only [applicable, beq_iff_eq, frontier]
    exact nextKind_iff (observationView_iff.mp rfl)

theorem ActionTo.compute (meaning : ActionTo p env action s result) : actionRun p env action s = result := by
  cases meaning with
  | run run | continued run => exact runTailRaw_iff.mpr run
  | resumed resume => exact resumeTailRaw_iff.mpr resume

theorem actionRun_sound : ActionTo p env action s (actionRun p env action s) := by
  cases action with | mk kind budget =>
    cases kind with
    | run => exact .run (runTailRaw_iff.mp rfl)
    | «continue» => exact .continued (runTailRaw_iff.mp rfl)
    | resume => exact .resumed (resumeTailRaw_iff.mp rfl)

theorem actionRun_iff : actionRun p env action s = result ↔ ActionTo p env action s result := by
  constructor
  · intro eq; rw [← eq]; exact actionRun_sound
  · exact ActionTo.compute

theorem ActionTo.prefix (meaning : ActionTo p env action s result) :
    BootStepsN p env result.used s result.state := by
  cases meaning with
  | run meaning | continued meaning => exact meaning.prefix
  | resumed meaning => exact meaning.prefix

theorem ActionTo.bound (meaning : ActionTo p env action s result) : result.used ≤ action.budget := by
  cases meaning with
  | run meaning | continued meaning => exact meaning.bound
  | resumed meaning => exact meaning.bound

theorem ActionTo.safety (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) (meaning : ActionTo p env action s result) :
    SafetyInvariant p env result.state ∧ result.reason ≠ .invalidState := by
  cases meaning with
  | run meaning | continued meaning => exact ⟨meaning.safety wf input safe, meaning.not_invalid wf input safe⟩
  | resumed meaning => exact ⟨meaning.safety wf input safe, meaning.not_invalid wf input safe⟩

inductive TerminalReason : StopReason → Ending → Prop where
  | blocked : TerminalReason .blockedRead .blocked
  | ineligible : TerminalReason .ineligibleDelivery .ineligible
  | invalid : TerminalReason .invalidState .invalid

theorem terminal_some_iff : terminal reason = some ending ↔ TerminalReason reason ending := by
  constructor
  · intro eq; cases reason <;> simp [terminal] at eq
    all_goals subst ending; constructor
  · intro meaning; cases meaning <;> rfl

theorem terminal_none_iff : terminal reason = none ↔ Nonterminal reason := by
  cases reason <;> simp [terminal, Nonterminal]

end ANL.Boot.Runtime.Session
