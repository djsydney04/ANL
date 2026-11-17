import ANL.MemoryWireSafety
import ANL.MemoryLoweringSoundness

namespace ANL.Memory

namespace Pair

theorem simulation_canonical (accepted : check p q = true) : Simulation.Canonical p q := by
  obtain ⟨core, _, lowered⟩ := (check_iff p q).mp accepted
  exact ⟨core, lowered⟩

theorem core_entry_to_mir (accepted : check p q = true)
    (path : Steps p responses (ANL.Memory.initial p) last) (done : Terminal last) :
    ∃ targetLast, Mir.Steps q responses (Mir.initial q) targetLast ∧ Mir.Terminal targetLast ∧
      Simulation.FinalRelated p last targetLast :=
  Simulation.core_entry_to_mir (simulation_canonical accepted) path done

theorem mir_entry_to_core (accepted : check p q = true)
    (path : Mir.Steps q responses (Mir.initial q) last) (done : Mir.RawStopped last) :
    ∃ sourceLast, Steps p responses (ANL.Memory.initial p) sourceLast ∧ Terminal sourceLast ∧
      Simulation.FinalRelated p sourceLast last :=
  Simulation.mir_entry_to_core (simulation_canonical accepted) path done

theorem mir_entry_not_invalid (accepted : check p q = true)
    (path : Mir.Steps q responses (Mir.initial q) last) : last.control ≠ .invalid :=
  Simulation.mir_entry_not_invalid (simulation_canonical accepted) path

theorem core_completed_run_to_mir (accepted : check p q = true)
    (completed : execute p responses coreBudget (ANL.Memory.initial p) = .completed sourceLast) :
    ∃ mirBudget targetLast, Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast ∧
      Simulation.FinalRelated p sourceLast targetLast :=
  Simulation.core_completed_run_to_mir (simulation_canonical accepted) completed

theorem mir_completed_run_to_core (accepted : check p q = true)
    (completed : Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast) :
    ∃ coreBudget sourceLast, execute p responses coreBudget (ANL.Memory.initial p) = .completed sourceLast ∧
      Simulation.FinalRelated p sourceLast targetLast :=
  Simulation.mir_completed_run_to_core (simulation_canonical accepted) completed

theorem mir_run_not_invalid (accepted : check p q = true) :
    (Mir.run q responses budget (Mir.initial q)).state.control ≠ .invalid :=
  Simulation.mir_run_not_invalid (simulation_canonical accepted)

theorem mir_normal_entry_cleanup (accepted : check p q = true)
    (path : Mir.Steps q responses (Mir.initial q) ⟨.ret value, targetActivation, [], world⟩) :
    value.type = .scalar .i64 ∧ world.owners = [] ∧ targetActivation.resources = [] ∧
      world.positiveHeap = [] ∧ world.activeEmpties = [] :=
  Simulation.mir_normal_entry_cleanup (simulation_canonical accepted) path

end Pair

namespace Wire

variable {ct mt : String}

/-- Conditional on the actual document checker returning this exact decoded pair. -/
theorem simulation_canonical (accepted : checkDocuments ct mt = .ok (p, q)) :
    Simulation.Canonical p q := by
  obtain ⟨core, _, lowered⟩ := accepted_documents accepted
  exact ⟨core, lowered⟩

theorem core_entry_to_mir (accepted : checkDocuments ct mt = .ok (p, q))
    (path : Steps p responses (ANL.Memory.initial p) last) (done : Terminal last) :
    ∃ targetLast, Mir.Steps q responses (Mir.initial q) targetLast ∧ Mir.Terminal targetLast ∧
      Simulation.FinalRelated p last targetLast :=
  Simulation.core_entry_to_mir (simulation_canonical accepted) path done

theorem mir_entry_to_core (accepted : checkDocuments ct mt = .ok (p, q))
    (path : Mir.Steps q responses (Mir.initial q) last) (done : Mir.RawStopped last) :
    ∃ sourceLast, Steps p responses (ANL.Memory.initial p) sourceLast ∧ Terminal sourceLast ∧
      Simulation.FinalRelated p sourceLast last :=
  Simulation.mir_entry_to_core (simulation_canonical accepted) path done

theorem mir_entry_not_invalid (accepted : checkDocuments ct mt = .ok (p, q))
    (path : Mir.Steps q responses (Mir.initial q) last) : last.control ≠ .invalid :=
  Simulation.mir_entry_not_invalid (simulation_canonical accepted) path

theorem core_completed_run_to_mir (accepted : checkDocuments ct mt = .ok (p, q))
    (completed : execute p responses coreBudget (ANL.Memory.initial p) = .completed sourceLast) :
    ∃ mirBudget targetLast, Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast ∧
      Simulation.FinalRelated p sourceLast targetLast :=
  Simulation.core_completed_run_to_mir (simulation_canonical accepted) completed

theorem mir_completed_run_to_core (accepted : checkDocuments ct mt = .ok (p, q))
    (completed : Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast) :
    ∃ coreBudget sourceLast, execute p responses coreBudget (ANL.Memory.initial p) = .completed sourceLast ∧
      Simulation.FinalRelated p sourceLast targetLast :=
  Simulation.mir_completed_run_to_core (simulation_canonical accepted) completed

theorem mir_run_not_invalid (accepted : checkDocuments ct mt = .ok (p, q)) :
    (Mir.run q responses budget (Mir.initial q)).state.control ≠ .invalid :=
  Simulation.mir_run_not_invalid (simulation_canonical accepted)

theorem mir_normal_entry_cleanup (accepted : checkDocuments ct mt = .ok (p, q))
    (path : Mir.Steps q responses (Mir.initial q) ⟨.ret value, targetActivation, [], world⟩) :
    value.type = .scalar .i64 ∧ world.owners = [] ∧ targetActivation.resources = [] ∧
      world.positiveHeap = [] ∧ world.activeEmpties = [] :=
  Simulation.mir_normal_entry_cleanup (simulation_canonical accepted) path

end Wire
end ANL.Memory
