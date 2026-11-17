import ANL.MemoryLoweringProofs

namespace ANL.Memory.Pair

/-- Equality of the complete raw MIR to the accepted deterministic lowerer output. -/
def Canonical (core : Program) (mir : Mir.Program) : Prop :=
  Lowering.program core = some mir

instance (core : Program) (mir : Mir.Program) : Decidable (Canonical core mir) :=
  inferInstanceAs (Decidable (_ = _))

def check (core : Program) (mir : Mir.Program) : Bool :=
  checkProgram core && Mir.checkProgram mir && decide (Canonical core mir)

theorem check_iff (core : Program) (mir : Mir.Program) :
    check core mir = true ↔
      WellFormedProgram core ∧ mir.WellFormed ∧ Canonical core mir := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, checkProgram_iff,
    Mir.checkProgram_iff, and_assoc]

theorem canonical_accepted {core : Program} (h : WellFormedProgram core) :
    ∃ mir, Lowering.program core = some mir ∧ check core mir = true := by
  obtain ⟨mir, lowered, valid⟩ := Lowering.program_total_wellFormed h
  exact ⟨mir, lowered, (check_iff core mir).mpr ⟨h, valid, lowered⟩⟩

theorem accepted_metadata {core : Program} {mir : Mir.Program}
    (h : check core mir = true) :
    mir.allocationProfile = core.profile ∧ mir.semanticRevision = core.semanticRevision ∧
    mir.entry = core.entry := by
  have m := Lowering.program_metadata ((check_iff core mir).mp h).2.2
  exact ⟨m.2.2.1, m.2.1, m.2.2.2.1⟩

end ANL.Memory.Pair
