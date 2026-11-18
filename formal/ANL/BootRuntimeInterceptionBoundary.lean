import ANL.BootRuntimeNoReturn

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}

 theorem ordinary_not_primitive (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (ready : Ready p s .ordinary) : ¬ Origin.PrimitiveFrontier p s.machine := by
  intro frontier
  obtain ⟨q, captured⟩ := capture_complete wf old.typed old.aligned frontier old.ordinal
  cases ready with | ordinary _ _ _ absent => exact absent q captured

 theorem ordinary_admitted (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (ready : Ready p s .ordinary) : Origin.Admitted p s.machine := by
  rcases Origin.frontier_or_admitted wf old.typed old.aligned with primitive | admitted
  · exact False.elim (ordinary_not_primitive wf old ready primitive)
  · exact admitted

/-- A captured primitive can never use the carrier's invoke/grant/body transition. -/
 theorem captured_not_ordinary (captured : Captured p s q) :
    ¬ Origin.Step p responses s.machine s.origins next origins := by
  intro step
  cases step with | ordinary admitted _ _ _ => exact Origin.primitive_not_admitted captured.frontier admitted

 theorem primitive_dispatch (wf : WellFormedProgram p) (old : RuntimeInvariant p env s)
    (phase : s.phase = .ordinary) (frontier : Origin.PrimitiveFrontier p s.machine) :
    ∃ q, Ready p s (.captured q) ∧
      BootStep p env s (withPhase s (.primitiveBefore q)) := by
  obtain ⟨q, captured⟩ := capture_complete wf old.typed old.aligned frontier old.ordinal
  have notPark : ¬ FirstPark p s := by
    intro parked
    obtain ⟨values, row, controlEq, _⟩ := captured.valid.invocation
    have ctl := parked.1.2.2.2
    rw [controlEq] at ctl
    exact ctl
  have ready : Ready p s (.captured q) := .capture phase notPark captured
  exact ⟨q, ready, .advance ready .captured⟩

/-- A checked phase cannot silently restore a different caller or consume a response on return. -/
 theorem primitive_return_retains :
    (returnState s value).machine.current = s.machine.current ∧
    (returnState s value).machine.kont = s.machine.kont ∧
    (returnState s value).machine.world = s.machine.world ∧
    (returnState s value).origins = s.origins ∧
    (returnState s value).readCursor = s.readCursor ∧
    (returnState s value).nextOrdinal = s.nextOrdinal ∧
    (returnState s value).revEvents = s.revEvents := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.Runtime
