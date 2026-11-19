import ANL.BootNativeByteState

namespace ANL.Boot.NativeByte.Device

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
open ANL.Boot.NativeByte.State
universe u
variable {Origin : Type u}

def PreservesKnown (facts : Word → Fact Origin) (before after : Memory) : Prop :=
  ∀ address, facts address ≠ .unknown → after address = before address

theorem memory_preserves (valuation : Origin → Byte) (facts : Word → Fact Origin)
    (before after : Memory) (related : MemHolds valuation facts before)
    (preserved : PreservesKnown facts before after) : MemHolds valuation facts after := by
  intro address
  cases tag : facts address with
  | unknown => simp [Holds]
  | constant value =>
      rw [preserved address (by simp [tag])]
      simpa only [tag] using related address
  | origin token =>
      rw [preserved address (by simp [tag])]
      simpa only [tag] using related address

theorem inv_preserves (valuation : Origin → Byte) (state : Pair Origin) (after : Memory)
    (before : Inv valuation state)
    (preserved : PreservesKnown state.memoryFacts state.memory after) :
    Inv valuation ⟨state.registers, state.registerFacts, after, state.memoryFacts⟩ :=
  ⟨before.1, memory_preserves valuation state.memoryFacts state.memory after before.2 preserved⟩

theorem read_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (destination : Reg) (token : Origin) (response : Byte) (after : Memory)
    (before : Inv valuation state) (interpreted : valuation token = response)
    (preserved : PreservesKnown state.memoryFacts state.memory after) :
    Inv valuation
      ⟨writeW state.registers destination (word response.val),
       writeF state.registerFacts destination (.origin token), after, state.memoryFacts⟩ := by
  have zeroExtended : low8 (word response.val) = response := by
    apply Fin.ext
    exact (low8_word response.val).trans (Nat.mod_eq_of_lt response.isLt)
  have known : Holds valuation (.origin token) (low8 (word response.val)) := by
    change low8 (word response.val) = valuation token
    exact zeroExtended.trans interpreted.symm
  exact ⟨writeback_preserves valuation state.registerFacts state.registers destination
           (.origin token) (word response.val) before.1 known,
         memory_preserves valuation state.memoryFacts state.memory after before.2 preserved⟩

theorem origin_register_byte (valuation : Origin → Byte) (state : Pair Origin)
    (source : Reg) (token : Origin) (before : Inv valuation state)
    (tag : state.registerFacts source = .origin token) :
    low8 (state.registers source) = valuation token := by
  simpa only [tag, Holds] using before.1 source

theorem write_preserves_and_payload (valuation : Origin → Byte) (state : Pair Origin)
    (source : Reg) (entryToken : Origin) (entryArgument : Word) (after : Memory)
    (before : Inv valuation state) (tag : state.registerFacts source = .origin entryToken)
    (interpreted : valuation entryToken = low8 entryArgument)
    (preserved : PreservesKnown state.memoryFacts state.memory after) :
    Inv valuation ⟨state.registers, state.registerFacts, after, state.memoryFacts⟩ ∧
    low8 (state.registers source) = low8 entryArgument :=
  ⟨inv_preserves valuation state after before preserved,
   (origin_register_byte valuation state source entryToken before tag).trans interpreted⟩

theorem finite_origin_endpoint (valuation : Origin → Byte)
    (step : Nat → Pair Origin → Pair Origin → Prop) (trace : Nat → Pair Origin) (count : Nat)
    (resultRegister : Reg) (token : Origin)
    (initial : Inv valuation (trace 0))
    (steps : ∀ index, index < count → step index (trace index) (trace (index + 1)))
    (preserves : ∀ index, index < count → ∀ before after,
      step index before after → Inv valuation before → Inv valuation after)
    (tag : (trace count).registerFacts resultRegister = .origin token) :
    low8 ((trace count).registers resultRegister) = valuation token :=
  origin_register_byte valuation (trace count) resultRegister token
    (finite_prefix valuation step trace count initial steps preserves count (Nat.le_refl count)) tag

end ANL.Boot.NativeByte.Device
