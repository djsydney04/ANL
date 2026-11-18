import ANL.BootNativeFrame

namespace ANL.Boot.NativeFrame

universe u

structure BeforeReturn (step : Step H) (isReturn : State H → Prop)
    (s : State H) (trace : List (Edge H)) (t : State H) : Prop where
  run : Run step s trace t
  earlier : ∀ edge ∈ trace, ¬ isReturn edge.before

structure LocalPrefixContract (localStep : Step H) (E bound : Nat)
    (s : State H) : Prop where
  safe : ∀ trace t, Run localStep s trace t →
    FramePrefix E bound s trace t ∧ TraceStates s trace t Zero

structure LeafEntry (E R h : Nat) (target : Word) (EntryOK : State H → Prop)
    (s : State H) : Prop where
  depth : h ≤ E
  entryBound : E < modulus
  entryAligned : E % 16 = 0
  returnBound : R < modulus
  returnAligned : R % 4 = 0
  zero : Zero s
  pc : s.pc = target
  sp : SP s = E
  ra : RA s = R
  ready : EntryOK s

structure Restored (E R : Nat) (s t : State H) : Prop where
  sp : SP t = E
  ra : RA t = R
  saved : ∀ r, Saved r → t.regs r = s.regs r

structure LeafContract (step : Step H) (isReturn isCall : State H → Prop)
    (ownsPC : Word → Prop) (EntryOK : State H → Prop) (target : Word) (h : Nat) : Prop where
  safe : ∀ E R s trace t, LeafEntry E R h target EntryOK s →
    BeforeReturn step isReturn s trace t →
    FramePrefix E h s trace t ∧ TraceStates s trace t Zero ∧
      TraceStates s trace t (fun v => ownsPC v.pc)
  restore : ∀ E R s trace t, LeafEntry E R h target EntryOK s →
    BeforeReturn step isReturn s trace t → isReturn t → Restored E R s t
  callFree : ∀ s, ownsPC s.pc → ¬ isCall s

structure LinkSound (step : Step H) (P : Nat) (target : Word)
    (s enter : State H) : Prop where
  actual : step s [] enter
  pc : s.pc.val = P
  pcAligned : P % 4 = 0
  returnBound : P + 4 < modulus
  targetAligned : target.val % 4 = 0
  targetPC : enter.pc = target
  ra : RA enter = P + 4
  others : ∀ r, r ≠ raReg → enter.regs r = s.regs r
  memory : enter.mem = s.mem
  hardware : enter.hardware = s.hardware

theorem LinkSound.sp (link : LinkSound step P target s enter) : SP enter = SP s := by
  unfold SP
  rw [link.others spReg (by decide)]

theorem LinkSound.zero (link : LinkSound step P target s enter) (zero : Zero s) : Zero enter := by
  unfold Zero at zero ⊢
  rw [link.others zeroReg (by decide)]
  exact zero

theorem continuation_aligned (aligned : P % 4 = 0) (bound : P + 4 < modulus) :
    ∃ R : Word, R.val = P + 4 ∧ R.val % 4 = 0 := by
  refine ⟨⟨P + 4, bound⟩, rfl, ?_⟩
  dsimp
  omega

def clearLowBit (R : Nat) : Nat := R - R % 2

theorem return_low_bit_neutral (bound : R < modulus) (aligned : R % 4 = 0) :
    clearLowBit R = R := by
  have _ := bound
  unfold clearLowBit
  omega

structure ReturnEffect (s t : State H) : Prop where
  pc : t.pc.val = clearLowBit (RA s)
  registers : t.regs = s.regs
  memory : t.mem = s.mem
  hardware : t.hardware = s.hardware

def ReturnSound (step : Step H) (isReturn : State H → Prop) : Prop :=
  ∀ s accesses t, isReturn s → step s accesses t → accesses = [] ∧ ReturnEffect s t

theorem LinkSound.leaf_entry (link : LinkSound step P target call enter)
    (fit : h ≤ E - d) (entryBound : E < modulus)
    (callSP : SP call = E - d) (callAligned : SP call % 16 = 0)
    (zero : Zero call) (ready : EntryOK enter) :
    LeafEntry (E - d) (P + 4) h target EntryOK enter := by
  refine ⟨fit, by omega, ?_, link.returnBound, by have := link.pcAligned; omega,
    link.zero zero, link.targetPC, ?_, link.ra, ready⟩
  · omega
  · exact link.sp.trans callSP

theorem call_prefix_bound
    (localContract : LocalPrefixContract localStep E previous initial)
    (callerRun : Run localStep initial callerTrace call)
    (initialSP : SP initial = E) (entryBound : E < modulus)
    (depth : d ≤ previous) (previousBound : previous ≤ E) (fit : h ≤ E - d)
    (callSP : SP call = E - d)
    (link : LinkSound step P target call enter)
    (ready : EntryOK enter)
    (leaf : LeafContract step isReturn isCall ownsPC EntryOK target h)
    (writes : WriteSound step)
    (calleeRun : BeforeReturn step isReturn enter calleeTrace stopped)
    (slotsWithin : SlotsWithin (E - d) E slots) :
    RegionPrefix (E - max previous (d + h)) E initial
      (callerTrace ++ [⟨call, [], enter⟩] ++ calleeTrace) stopped ∧
    TraceStates enter calleeTrace stopped (SlotsEqual slots call) := by
  have _ := initialSP
  have localSafe := localContract.safe callerTrace call callerRun
  have aligned := localSafe.1.states.finish.2.2
  have entered := link.leaf_entry fit entryBound callSP aligned localSafe.2.finish ready
  have leafSafe := leaf.safe (E - d) (P + 4) enter calleeTrace stopped entered calleeRun
  have rebased := callee_prefix_rebased (by omega : d ≤ E) fit leafSafe.1
  have localRegion : RegionPrefix (E - max previous (d + h)) E initial callerTrace call :=
    localSafe.1.region.widen (by omega) (by omega)
  have leafRegion : RegionPrefix (E - max previous (d + h)) E enter calleeTrace stopped :=
    rebased.1.widen (by omega) (by omega)
  have callState := localRegion.states.finish
  have enterState := leafRegion.states.start
  have linkRegion : RegionPrefix (E - max previous (d + h)) E call [⟨call, [], enter⟩] enter := by
    refine ⟨⟨callState, enterState, ?_⟩, ?_⟩
    · intro edge member
      have equal := List.mem_singleton.mp member
      subst edge
      exact ⟨callState, enterState⟩
    · intro edge member access present
      have equal := List.mem_singleton.mp member
      subst edge
      cases present
  refine ⟨(localRegion.append linkRegion).append leafRegion, ?_⟩
  have retained := write_prefix_noninterference writes calleeRun.run fit leafSafe.1
  apply retained.map
  intro v same
  have slotsSame := frame_preserves_slots (by omega : d ≤ E) fit slotsWithin same
  intro slot member address covers
  have equal := slotsSame slot member address covers
  rw [link.memory] at equal
  exact equal

theorem call_return_frame
    (depth : d ≤ E) (fit : h ≤ E - d)
    (link : LinkSound step P target call enter)
    (entered : LeafEntry (E - d) (P + 4) h target EntryOK enter)
    (leaf : LeafContract step isReturn isCall ownsPC EntryOK target h)
    (writes : WriteSound step)
    («prefix» : BeforeReturn step isReturn enter trace beforeReturn)
    (atReturn : isReturn beforeReturn) (actualReturn : step beforeReturn accesses resumed)
    (returns : ReturnSound step isReturn)
    (OwnedResume : Nat → Nat → Nat → Prop) (owned : OwnedResume caller P (P + 4))
    (slotsWithin : SlotsWithin (E - d) E slots) :
    resumed.pc.val = P + 4 ∧ SP resumed = E - d ∧ RA resumed = P + 4 ∧ Zero resumed ∧
    (∀ r, Saved r → resumed.regs r = call.regs r) ∧ SlotsEqual slots call resumed ∧
    OwnedResume caller P resumed.pc.val := by
  have safe := leaf.safe (E - d) (P + 4) enter trace beforeReturn entered «prefix»
  have restored := leaf.restore (E - d) (P + 4) enter trace beforeReturn entered «prefix» atReturn
  have returned := (returns beforeReturn accesses resumed atReturn actualReturn).2
  have pc : resumed.pc.val = P + 4 := by
    rw [returned.pc, restored.ra]
    exact return_low_bit_neutral entered.returnBound entered.returnAligned
  have sp : SP resumed = E - d := by
    unfold SP
    rw [returned.registers]
    exact restored.sp
  have ra : RA resumed = P + 4 := by
    unfold RA
    rw [returned.registers]
    exact restored.ra
  have zero : Zero resumed := by
    unfold Zero
    rw [returned.registers]
    exact safe.2.1.finish
  have memory := (write_prefix_noninterference writes «prefix».run fit safe.1).finish
  have slotsSame := frame_preserves_slots depth fit slotsWithin memory
  refine ⟨pc, sp, ra, zero, ?_, ?_, ?_⟩
  · intro r saved
    have other : r ≠ raReg := by
      intro equal
      subst r
      simp [Saved, raReg] at saved
    rw [returned.registers, restored.saved r saved, link.others r other]
  · intro slot member address covers
    have equal := slotsSame slot member address covers
    rw [link.memory] at equal
    rw [returned.memory]
    exact equal
  · rw [pc]
    exact owned

inductive RootRole where
  | boot | hardware | language
  deriving DecidableEq

abbrev TraceRelation (H : Type u) := State H → List (Edge H) → State H → Prop

structure RootThunkContract (step : Step H) (role : RootRole) (T : Nat) (entryPC : Word)
    (arguments : State H → State H → Prop)
    («prefix» completed nonlinking : TraceRelation H) : Prop where
  actual : ∀ s trace t, «prefix» s trace t → Run step s trace t
  stackless : ∀ s trace t, «prefix» s trace t → ∀ edge ∈ trace, edge.accesses = []
  completion : ∀ s trace t, completed s trace t → «prefix» s trace t ∧
    SP t = T ∧ t.pc = entryPC ∧ arguments s t ∧ t.mem = s.mem ∧ Zero t
  terminalTransfer : ∀ s trace t, completed s trace t → nonlinking s trace t

def MappedRW (rw : Word → Prop) (L T : Nat) : Prop :=
  ∀ address, Inside L T address.val → rw address

theorem root_substitution
    (ordered : L ≤ T) (topBound : T < modulus) (aligned : T % 16 = 0)
    (capacity : B ≤ T - L) (mapped : MappedRW rw L T)
    (thunk : RootThunkContract step role T entryPC arguments thunkPrefix completed nonlinking)
    (finished : completed incoming thunkTrace roleEntry)
    (expanded : FramePrefix T B roleEntry roleTrace final) :
    SP roleEntry = T ∧ roleEntry.pc = entryPC ∧ arguments incoming roleEntry ∧
    nonlinking incoming thunkTrace roleEntry ∧
    (∀ edge ∈ thunkTrace, edge.accesses = []) ∧ RegionPrefix L T roleEntry roleTrace final ∧
    (∀ edge ∈ roleTrace, ∀ access ∈ edge.accesses, ∀ address,
      access.Covers address → rw address) := by
  have _ := topBound
  have _ := aligned
  have entered := thunk.completion incoming thunkTrace roleEntry finished
  have region : RegionPrefix L T roleEntry roleTrace final :=
    expanded.region.widen (by omega) (by omega)
  refine ⟨entered.2.1, entered.2.2.1, entered.2.2.2.1,
    thunk.terminalTransfer incoming thunkTrace roleEntry finished,
    thunk.stackless incoming thunkTrace roleEntry entered.1, region, ?_⟩
  intro edge member access present address covers
  have span := region.accesses edge member access present
  apply mapped address
  simp only [Fits] at span
  simp only [Access.Covers, Inside] at covers ⊢
  omega

end ANL.Boot.NativeFrame
