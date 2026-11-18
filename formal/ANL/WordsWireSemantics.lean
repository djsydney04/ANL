import ANL.WordsPairWireSafety
import ANL.WordsPairSemantics

namespace ANL.Words.Wire

open ANL.Memory

/-- Accepted decoded documents use the exact cumulative Pair checker. -/
theorem documents_pair_checked
    (accepted : checkDocuments coreText mirText = .ok (p, q)) :
    Pair.check p q = true :=
  (Pair.check_iff p q).mpr (accepted_documents accepted)

/-- This bridge is conditional on byte-document acceptance, not a parser proof.
    Completion relates finite machine paths; source and target budgets may differ. -/
theorem simulation_canonical (accepted : checkDocuments coreText mirText = .ok (p, q)) : Simulation.Canonical p q := by
  exact Pair.simulation_canonical (documents_pair_checked accepted)

theorem core_entry_to_mir (accepted : checkDocuments coreText mirText = .ok (p, q))
    (path : Steps p responses (ANL.Words.initial p) last) (done : Terminal last) :
    ∃ targetLast, Mir.Steps q responses (Mir.initial q) targetLast ∧ Mir.Terminal targetLast ∧
      Simulation.FinalRelated p last targetLast :=
  Pair.core_entry_to_mir (documents_pair_checked accepted) path done

theorem mir_entry_to_core (accepted : checkDocuments coreText mirText = .ok (p, q))
    (path : Mir.Steps q responses (Mir.initial q) last) (done : Mir.RawStopped last) :
    ∃ sourceLast, Steps p responses (ANL.Words.initial p) sourceLast ∧ Terminal sourceLast ∧
      Simulation.FinalRelated p sourceLast last :=
  Pair.mir_entry_to_core (documents_pair_checked accepted) path done

theorem mir_entry_not_invalid (accepted : checkDocuments coreText mirText = .ok (p, q))
    (path : Mir.Steps q responses (Mir.initial q) last) : last.control ≠ .invalid :=
  Pair.mir_entry_not_invalid (documents_pair_checked accepted) path

theorem core_completed_run_to_mir (accepted : checkDocuments coreText mirText = .ok (p, q))
    (completed : execute p responses coreBudget (ANL.Words.initial p) = .completed sourceLast) :
    ∃ mirBudget targetLast, Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast ∧
      Simulation.FinalRelated p sourceLast targetLast :=
  Pair.core_completed_run_to_mir (documents_pair_checked accepted) completed

theorem mir_completed_run_to_core (accepted : checkDocuments coreText mirText = .ok (p, q))
    (completed : Mir.run q responses mirBudget (Mir.initial q) = .completed targetLast) :
    ∃ coreBudget sourceLast, execute p responses coreBudget (ANL.Words.initial p) = .completed sourceLast ∧
      Simulation.FinalRelated p sourceLast targetLast :=
  Pair.mir_completed_run_to_core (documents_pair_checked accepted) completed

theorem mir_run_not_invalid (accepted : checkDocuments coreText mirText = .ok (p, q)) :
    (Mir.run q responses budget (Mir.initial q)).state.control ≠ .invalid :=
  Pair.mir_run_not_invalid (documents_pair_checked accepted)

theorem mir_normal_entry_cleanup (accepted : checkDocuments coreText mirText = .ok (p, q))
    (path : Mir.Steps q responses (Mir.initial q) ⟨.ret value, targetActivation, [], world⟩) :
    value.type = .scalar (.legacy .i64) ∧ world.owners = [] ∧ targetActivation.resources = [] ∧
      world.positiveHeap = [] ∧ world.activeEmpties = [] :=
  Pair.mir_normal_entry_cleanup (documents_pair_checked accepted) path


end ANL.Words.Wire
