import Std

namespace ANL.Boot.NativeFrame

universe u

def modulus : Nat := 2 ^ 64
abbrev Word := Fin modulus
abbrev Byte := Fin 256
abbrev Reg := Fin 32

def zeroReg : Reg := ⟨0, by decide⟩
def raReg : Reg := ⟨1, by decide⟩
def spReg : Reg := ⟨2, by decide⟩

structure State (H : Type u) where
  pc : Word
  regs : Reg → Word
  mem : Word → Byte
  hardware : H

def SP (s : State H) : Nat := (s.regs spReg).val
def RA (s : State H) : Nat := (s.regs raReg).val
def Zero (s : State H) : Prop := (s.regs zeroReg).val = 0
def Saved (r : Reg) : Prop := r.val = 8 ∨ r.val = 9 ∨ (18 ≤ r.val ∧ r.val ≤ 27)

def Inside (lo hi address : Nat) : Prop := lo ≤ address ∧ address < hi
def Fits (lo hi address bytes : Nat) : Prop := 0 < bytes ∧ lo ≤ address ∧ address + bytes ≤ hi

structure Slot where
  address : Word
  bytes : Nat
  positive : 0 < bytes

def Slot.Covers (slot : Slot) (address : Word) : Prop :=
  Inside slot.address.val (slot.address.val + slot.bytes) address.val

def SlotsWithin (lo hi : Nat) (slots : List Slot) : Prop :=
  ∀ slot ∈ slots, Fits lo hi slot.address.val slot.bytes

def SlotsEqual (slots : List Slot) (s t : State H) : Prop :=
  ∀ slot ∈ slots, ∀ address, slot.Covers address → s.mem address = t.mem address

def AgreesOutside (lo hi : Nat) (s t : State H) : Prop :=
  ∀ address, ¬ Inside lo hi address.val → s.mem address = t.mem address

theorem AgreesOutside.refl (s : State H) : AgreesOutside lo hi s s := by
  intro address _
  rfl

theorem AgreesOutside.trans (first : AgreesOutside lo hi s t)
    (second : AgreesOutside lo hi t v) : AgreesOutside lo hi s v := by
  intro address outside
  exact (first address outside).trans (second address outside)

theorem frame_separated (depth : d ≤ E) (leaf : h ≤ E - d) :
    (∀ a, Inside (E - d - h) (E - d) a → ¬ Inside (E - d) E a) ∧
    (∀ a n b, Fits (E - d) E a n → Inside a (a + n) b →
      ¬ Inside (E - d - h) (E - d) b) := by
  have _ := depth
  have _ := leaf
  constructor
  · intro a lower upper
    simp only [Inside] at lower upper
    omega
  · intro a n b span byte lower
    simp only [Fits] at span
    simp only [Inside] at byte lower
    omega

theorem frame_preserves_slots (depth : d ≤ E) (leaf : h ≤ E - d)
    (within : SlotsWithin (E - d) E slots)
    (same : AgreesOutside (E - d - h) (E - d) s t) : SlotsEqual slots s t := by
  intro slot member address covers
  apply same address
  exact (frame_separated depth leaf).2 slot.address.val slot.bytes address.val
    (within slot member) covers

inductive AccessKind where
  | read | write
  deriving DecidableEq

structure Access where
  kind : AccessKind
  address : Word
  bytes : Nat
  positive : 0 < bytes

def Access.Covers (access : Access) (address : Word) : Prop :=
  Inside access.address.val (access.address.val + access.bytes) address.val

abbrev Step (H : Type u) := State H → List Access → State H → Prop

structure Edge (H : Type u) where
  before : State H
  accesses : List Access
  after : State H

inductive Run (step : Step H) : State H → List (Edge H) → State H → Prop where
  | nil (s) : Run step s [] s
  | cons : step s accesses next → Run step next rest t →
      Run step s (⟨s, accesses, next⟩ :: rest) t

structure TraceStates (s : State H) (trace : List (Edge H)) (t : State H)
    (property : State H → Prop) : Prop where
  start : property s
  finish : property t
  edges : ∀ edge ∈ trace, property edge.before ∧ property edge.after

theorem TraceStates.map (states : TraceStates s trace t P)
    (implication : ∀ v, P v → Q v) : TraceStates s trace t Q := by
  refine ⟨implication s states.start, implication t states.finish, ?_⟩
  intro edge member
  exact ⟨implication edge.before (states.edges edge member).1,
    implication edge.after (states.edges edge member).2⟩

def StateInFrame (E bound : Nat) (s : State H) : Prop :=
  E - bound ≤ SP s ∧ SP s ≤ E ∧ SP s % 16 = 0

structure FramePrefix (E bound : Nat) (s : State H) (trace : List (Edge H))
    (t : State H) : Prop where
  states : TraceStates s trace t (StateInFrame E bound)
  accesses : ∀ edge ∈ trace, ∀ access ∈ edge.accesses,
    Fits (SP edge.before) E access.address.val access.bytes

structure RegionPrefix (lo hi : Nat) (s : State H) (trace : List (Edge H))
    (t : State H) : Prop where
  states : TraceStates s trace t (fun v => lo ≤ SP v ∧ SP v ≤ hi ∧ SP v % 16 = 0)
  accesses : ∀ edge ∈ trace, ∀ access ∈ edge.accesses,
    Fits lo hi access.address.val access.bytes

theorem FramePrefix.region (frame : FramePrefix E bound s trace t) :
    RegionPrefix (E - bound) E s trace t := by
  refine ⟨frame.states, ?_⟩
  intro edge member access present
  have state := (frame.states.edges edge member).1
  have span := frame.accesses edge member access present
  simp only [StateInFrame] at state
  simp only [Fits] at span ⊢
  omega

theorem RegionPrefix.widen (region : RegionPrefix lo hi s trace t)
    (lower : newLo ≤ lo) (upper : hi ≤ newHi) :
    RegionPrefix newLo newHi s trace t := by
  refine ⟨region.states.map (fun _ bound => by omega), ?_⟩
  intro edge member access present
  have := region.accesses edge member access present
  simp only [Fits] at this ⊢
  omega

theorem RegionPrefix.append (first : RegionPrefix lo hi s left middle)
    (second : RegionPrefix lo hi middle right t) :
    RegionPrefix lo hi s (left ++ right) t := by
  refine ⟨⟨first.states.start, second.states.finish, ?_⟩, ?_⟩
  · intro edge member
    rcases List.mem_append.mp member with present | present
    · exact first.states.edges edge present
    · exact second.states.edges edge present
  · intro edge member access present
    rcases List.mem_append.mp member with found | found
    · exact first.accesses edge found access present
    · exact second.accesses edge found access present

def WriteSound (step : Step H) : Prop :=
  ∀ s accesses t, step s accesses t → ∀ address,
    (∀ access ∈ accesses, access.kind = .write → ¬ access.Covers address) →
    s.mem address = t.mem address

theorem write_prefix_noninterference (sound : WriteSound step)
    (run : Run step s trace t) (bound : b ≤ E) (frame : FramePrefix E b s trace t) :
    TraceStates s trace t (AgreesOutside (E - b) E s) := by
  have _ := bound
  revert frame
  induction run with
  | nil s =>
      intro frame
      refine ⟨.refl s, .refl s, ?_⟩
      intro edge member
      cases member
  | @cons s accesses next rest t transition tail ih =>
      intro frame
      let head : Edge _ := ⟨s, accesses, next⟩
      have member : head ∈ head :: rest := by simp
      have nextFrame : FramePrefix E b next rest t := by
        refine ⟨⟨(frame.states.edges head member).2, frame.states.finish, ?_⟩, ?_⟩
        · intro edge present
          exact frame.states.edges edge (List.mem_cons_of_mem head present)
        · intro edge present access found
          exact frame.accesses edge (List.mem_cons_of_mem head present) access found
      have first : AgreesOutside (E - b) E s next := by
        intro address outside
        apply sound s accesses next transition address
        intro access present _ covers
        have span := frame.accesses head member access present
        have state := frame.states.start
        change Fits (SP s) E access.address.val access.bytes at span
        simp only [Fits] at span
        simp only [StateInFrame] at state
        simp only [Access.Covers, Inside] at covers
        apply outside
        simp only [Inside]
        omega
      have remaining := ih nextFrame
      refine ⟨.refl s, first.trans remaining.finish, ?_⟩
      intro edge present
      rcases List.mem_cons.mp present with equal | later
      · subst edge
        exact ⟨.refl s, first⟩
      · exact ⟨first.trans (remaining.edges edge later).1,
          first.trans (remaining.edges edge later).2⟩

theorem callee_prefix_rebased (depth : d ≤ E) (leaf : h ≤ E - d)
    (frame : FramePrefix (E - d) h s trace t) :
    RegionPrefix (E - (d + h)) E s trace t ∧
    TraceStates s trace t (fun v => E - SP v ≤ d + h) := by
  have _ := leaf
  have region := frame.region
  constructor
  · exact region.widen (by omega) (by omega)
  · apply frame.states.map
    intro v state
    simp only [StateInFrame] at state
    omega

theorem sequential_peak (previous d1 h1 d2 h2 : Nat) :
    max (max previous (d1 + h1)) (d2 + h2) =
      max previous (max (d1 + h1) (d2 + h2)) := by omega

theorem terminal_requirement {L T bh bl : Nat} (ordered : L ≤ T) :
    max bh bl ≤ T - L ↔ bh ≤ T - L ∧ bl ≤ T - L := by
  have _ := ordered
  omega

end ANL.Boot.NativeFrame
