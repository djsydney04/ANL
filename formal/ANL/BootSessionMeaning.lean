import ANL.BootSessionPolicy

namespace ANL.Boot.Runtime.Session
variable {p : Program}

structure FrontierAt (p : Program) (reason : StopReason) (s : State) (value : Frontier) : Prop where
  observation : ObservationView p s value.observation
  next : ∀ kind, value.next = some kind ↔ Applicable p (some reason) s kind

inductive RowAt (p : Program) (env : Environment) (index : Nat) (action : Action)
    (total : Nat) (result : RunResult) : Row → Prop where
  | endpoint : FrontierAt p result.reason result.state view →
      RowAt p env index action total result
        ⟨index, action, result.used, total + result.used, result.reason, view,
          result.state.events.length, result.state.readCursor, deliveryView env result.state⟩

inductive ResultAt (p : Program) (s : State) (previous : Option StopReason) (total : Nat)
    (rows : List Row) (ending : Ending) : Result → Prop where
  | endpoint : FrontierAt p (previous.getD .exhausted) s view →
      ResultAt p s previous total rows ending ⟨s, previous.getD .exhausted, total, rows, ending, view⟩

/-- Finite action meaning. Past states exist only in this proposition, not in executable rows. -/
inductive SessionTo (p : Program) (env : Environment) : List Action → State → Option StopReason →
    Nat → Nat → List Row → Result → Prop where
  | done : ResultAt p s previous total rows .done result →
      SessionTo p env [] s previous index total rows result
  | rejected : ¬ Applicable p previous s action.kind →
      ResultAt p s previous total rows (.rejected index) result →
      SessionTo p env (action :: rest) s previous index total rows result
  | stopped : Applicable p previous s action.kind → ActionTo p env action s actionResult →
      RowAt p env index action total actionResult row → TerminalReason actionResult.reason ending →
      ResultAt p actionResult.state (some actionResult.reason) (total + actionResult.used) (rows ++ [row]) ending result →
      SessionTo p env (action :: rest) s previous index total rows result
  | advanced : Applicable p previous s action.kind → ActionTo p env action s actionResult →
      RowAt p env index action total actionResult row → Nonterminal actionResult.reason →
      SessionTo p env rest actionResult.state (some actionResult.reason) (index + 1)
        (total + actionResult.used) (rows ++ [row]) result →
      SessionTo p env (action :: rest) s previous index total rows result

variable {s : State}

theorem frontier_valid : FrontierAt p reason s (frontier p reason s) :=
  ⟨observationView_iff.mp rfl, fun _ => nextKind_iff (observationView_iff.mp rfl)⟩

theorem FrontierAt.compute (view : FrontierAt p reason s value) : frontier p reason s = value := by
  cases value with | mk observed next =>
    have obsEq := view.observation.compute
    have nextEq : nextKind reason observed = next := by
      have agrees : ∀ kind, nextKind reason observed = some kind ↔ next = some kind :=
        fun kind => (nextKind_iff view.observation).trans (view.next kind).symm
      cases h : nextKind reason observed <;> cases next <;> simp_all
    simp only [frontier, obsEq, nextEq]

theorem makeRow_valid (history : StateHistory p env result.state) :
    RowAt p env index action total result (makeRow p env index action total result) := by
  unfold makeRow
  rw [history.ordered_event_count]
  exact .endpoint frontier_valid

theorem RowAt.compute (history : StateHistory p env result.state)
    (view : RowAt p env index action total result row) : makeRow p env index action total result = row := by
  cases view with | endpoint actual =>
    simp only [makeRow, actual.compute, history.ordered_event_count]

theorem finish_valid : ResultAt p s previous total reverseRows.reverse ending
    (finish p s previous total reverseRows ending) := .endpoint frontier_valid

theorem ResultAt.compute (view : ResultAt p s previous total reverseRows.reverse ending result) :
    finish p s previous total reverseRows ending = result := by
  cases view with | endpoint actual => simp only [finish, actual.compute]

theorem SessionTo.compute (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s)
    (meaning : SessionTo p env actions s previous index total rows result)
    (rowOrder : reverseRows.reverse = rows) :
    loop p env actions s previous index total reverseRows = result := by
  induction meaning generalizing reverseRows with
  | done view =>
    rw [loop]
    apply ResultAt.compute
    simpa only [rowOrder] using view
  | rejected denied view =>
    rw [loop, ite_eq_right (by simpa only [Bool.not_eq_true] using (not_congr applicable_iff).mpr denied)]
    apply ResultAt.compute
    simpa only [rowOrder] using view
  | stopped allowed action row stopped view =>
    have nextSafe := (action.safety wf input safe).1
    rw [loop, ite_eq_left (applicable_iff.mpr allowed), action.compute]
    dsimp only
    rw [row.compute nextSafe.history, terminal_some_iff.mpr stopped]
    apply ResultAt.compute
    simpa only [List.reverse_cons, rowOrder] using view
  | advanced allowed action row ongoing rest ih =>
    have nextSafe := (action.safety wf input safe).1
    rw [loop, ite_eq_left (applicable_iff.mpr allowed), action.compute]
    dsimp only
    rw [row.compute nextSafe.history, terminal_none_iff.mpr ongoing]
    apply ih nextSafe
    simp only [List.reverse_cons, rowOrder]

theorem loop_sound (wf : WellFormedProgram p) (input : InputValid p env)
    (safe : SafetyInvariant p env s) :
    SessionTo p env actions s previous index total reverseRows.reverse
      (loop p env actions s previous index total reverseRows) := by
  induction actions generalizing s previous index total reverseRows with
  | nil => exact .done finish_valid
  | cons action rest ih =>
    rw [loop]
    split
    next allowed =>
      have actionMeaning := actionRun_sound (p := p) (env := env) (action := action) (s := s)
      have nextSafe := (actionMeaning.safety wf input safe).1
      have row := makeRow_valid (index := index) (action := action) (total := total) nextSafe.history
      dsimp only
      split
      next ending stopped =>
        exact .stopped (applicable_iff.mp allowed) actionMeaning row (terminal_some_iff.mp stopped)
          (by simpa only [List.reverse_cons] using (finish_valid (reverseRows := makeRow p env index action total (actionRun p env action s) :: reverseRows)))
      next ongoing =>
        exact .advanced (applicable_iff.mp allowed) actionMeaning row (terminal_none_iff.mp ongoing)
          (by simpa only [List.reverse_cons] using (ih
            (previous := some (actionRun p env action s).reason) (index := index + 1)
            (total := total + (actionRun p env action s).used)
            (reverseRows := makeRow p env index action total (actionRun p env action s) :: reverseRows) nextSafe))
    next denied => exact .rejected ((not_congr applicable_iff).mp denied) finish_valid

end ANL.Boot.Runtime.Session
