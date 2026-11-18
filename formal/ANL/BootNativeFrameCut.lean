import ANL.BootNativeFrameComposition

namespace ANL.Boot.NativeFrame

universe u
variable {H : Type u}

theorem Run.snoc_zero (run : Run step initial trace caller)
    (actual : step caller [] entered) :
    Run step initial (trace ++ [⟨caller, [], entered⟩]) entered := by
  induction run with
  | nil => exact .cons actual (.nil entered)
  | cons first _ ih => exact .cons first (ih actual)

theorem FramePrefix.snoc_zero (frame : FramePrefix T B initial trace caller)
    (sp : SP entered = SP caller) :
    FramePrefix T B initial (trace ++ [⟨caller, [], entered⟩]) entered := by
  have finish : StateInFrame T B entered := by
    simpa only [StateInFrame, sp] using frame.states.finish
  refine ⟨⟨frame.states.start, finish, ?_⟩, ?_⟩
  · intro edge member
    rcases List.mem_append.mp member with previous | last
    · exact frame.states.edges edge previous
    · have equal := List.mem_singleton.mp last
      subst edge
      exact ⟨frame.states.finish, finish⟩
  · intro edge member access present
    rcases List.mem_append.mp member with previous | last
    · exact frame.accesses edge previous access present
    · have equal := List.mem_singleton.mp last
      subst edge
      cases present

/-- The x0 transfer retains the actual input registers, including an earlier AUIPC's ra. -/
structure NonlinkingSound (step : Step H) (P : Nat) (target : Word)
    (caller entered : State H) : Prop where
  actual : step caller [] entered
  pc : caller.pc.val = P
  pcAligned : P % 4 = 0
  targetAligned : target.val % 4 = 0
  targetPC : entered.pc = target
  registers : entered.regs = caller.regs
  memory : entered.mem = caller.mem
  hardware : entered.hardware = caller.hardware

/-- This concludes at the slot; it does not execute the slot or deliver an exception. -/
theorem linked_cut_prefix (run : Run step initial trace caller)
    (frame : FramePrefix T B initial trace caller) (zero : Zero caller)
    (link : LinkSound step P slot caller entered) :
    Run step initial (trace ++ [⟨caller, [], entered⟩]) entered ∧
    FramePrefix T B initial (trace ++ [⟨caller, [], entered⟩]) entered ∧
    SP entered = SP caller ∧ entered.pc = slot ∧ RA entered = P + 4 ∧ Zero entered ∧
    SlotsEqual slots caller entered ∧ entered.hardware = caller.hardware := by
  refine ⟨run.snoc_zero link.actual, frame.snoc_zero link.sp, link.sp,
    link.targetPC, link.ra, link.zero zero, ?_, link.hardware⟩
  intro _ _ address _
  rw [link.memory]

theorem nonlinking_cut_prefix (run : Run step initial trace caller)
    (frame : FramePrefix T B initial trace caller) (zero : Zero caller)
    (transfer : NonlinkingSound step P slot caller entered) :
    Run step initial (trace ++ [⟨caller, [], entered⟩]) entered ∧
    FramePrefix T B initial (trace ++ [⟨caller, [], entered⟩]) entered ∧
    SP entered = SP caller ∧ entered.pc = slot ∧ RA entered = RA caller ∧ Zero entered ∧
    SlotsEqual slots caller entered ∧ entered.hardware = caller.hardware := by
  have sp : SP entered = SP caller := by unfold SP; rw [transfer.registers]
  have ra : RA entered = RA caller := by unfold RA; rw [transfer.registers]
  have enteredZero : Zero entered := by
    unfold Zero at zero ⊢
    rw [transfer.registers]
    exact zero
  refine ⟨run.snoc_zero transfer.actual, frame.snoc_zero sp, sp,
    transfer.targetPC, ra, enteredZero, ?_, transfer.hardware⟩
  intro _ _ address _
  rw [transfer.memory]

/-- Two independent completed roots share a reservation sized by max, never a boot-frame sum. -/
theorem independent_terminal_roots {hardwareStep languageStep : Step H}
    (ordered : L ≤ T) (topBound : T < modulus) (aligned : T % 16 = 0)
    (capacity : max hardwareBound languageBound ≤ T - L) (mapped : MappedRW rw L T)
    (hardwareThunk : RootThunkContract hardwareStep .hardware T hardwarePC hardwareArguments
      hardwarePrefix hardwareCompleted hardwareNonlinking)
    (languageThunk : RootThunkContract languageStep .language T languagePC languageArguments
      languagePrefix languageCompleted languageNonlinking)
    (hardwareFinished : hardwareCompleted hardwareIncoming hardwareThunkTrace hardwareEntry)
    (languageFinished : languageCompleted languageIncoming languageThunkTrace languageEntry)
    (hardwareFrame : FramePrefix T hardwareBound hardwareEntry hardwareTrace hardwareFinal)
    (languageFrame : FramePrefix T languageBound languageEntry languageTrace languageFinal) :
    SP hardwareEntry = T ∧ SP languageEntry = T ∧
    RegionPrefix L T hardwareEntry hardwareTrace hardwareFinal ∧
    RegionPrefix L T languageEntry languageTrace languageFinal ∧
    (∀ edge ∈ hardwareTrace, ∀ access ∈ edge.accesses, ∀ address,
      access.Covers address → rw address) ∧
    (∀ edge ∈ languageTrace, ∀ access ∈ edge.accesses, ∀ address,
      access.Covers address → rw address) := by
  have separate := (terminal_requirement ordered).mp capacity
  rcases root_substitution ordered topBound aligned separate.1 mapped hardwareThunk
    hardwareFinished hardwareFrame with ⟨hardwareSP, _, _, _, _, hardwareRegion, hardwareMapped⟩
  rcases root_substitution ordered topBound aligned separate.2 mapped languageThunk
    languageFinished languageFrame with ⟨languageSP, _, _, _, _, languageRegion, languageMapped⟩
  exact ⟨hardwareSP, languageSP, hardwareRegion, languageRegion, hardwareMapped, languageMapped⟩

end ANL.Boot.NativeFrame
