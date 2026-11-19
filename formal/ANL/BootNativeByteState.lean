import ANL.BootNativeByteRegisters

namespace ANL.Boot.NativeByte.State

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
universe u

structure Pair (Origin : Type u) where
  registers : WordRegs
  registerFacts : FactRegs Origin
  memory : Memory
  memoryFacts : Word → Fact Origin

variable {Origin : Type u}

def Inv (valuation : Origin → Byte) (state : Pair Origin) : Prop :=
  RegsHold valuation state.registerFacts state.registers ∧
    MemHolds valuation state.memoryFacts state.memory

theorem addi_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (source destination : Reg) (immediate : Int) (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination
          (addW (state.registers source) (wordInt immediate)),
       writeF state.registerFacts destination (addiFact (state.registerFacts source) immediate),
       state.memory, state.memoryFacts⟩ :=
  ⟨addi_writeback valuation state.registerFacts state.registers source destination immediate before.1,
   before.2⟩

theorem andi_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (source destination : Reg) (immediate : Int) (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination
          (andW (state.registers source) (wordInt immediate)),
       writeF state.registerFacts destination (andiFact (state.registerFacts source) immediate),
       state.memory, state.memoryFacts⟩ :=
  ⟨andi_writeback valuation state.registerFacts state.registers source destination immediate before.1,
   before.2⟩

theorem lui_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (destination : Reg) (immediate : Int) (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination (wordInt immediate),
       writeF state.registerFacts destination (luiFact immediate),
       state.memory, state.memoryFacts⟩ :=
  ⟨lui_writeback valuation state.registerFacts state.registers destination immediate before.1,
   before.2⟩

theorem auipc_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (destination : Reg) (pc : Word) (immediate : Int) (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination (addW pc (wordInt immediate)),
       writeF state.registerFacts destination (auipcFact pc immediate),
       state.memory, state.memoryFacts⟩ :=
  ⟨auipc_writeback valuation state.registerFacts state.registers destination pc immediate before.1,
   before.2⟩

theorem unknown_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (destination : Reg) (value : Word) (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination value,
       writeF state.registerFacts destination .unknown, state.memory, state.memoryFacts⟩ :=
  ⟨unknown_writeback valuation state.registerFacts state.registers destination value before.1,
   before.2⟩

theorem unchanged (valuation : Origin → Byte) (state : Pair Origin)
    (before : Inv valuation state) : Inv valuation state := before

theorem unsigned_load_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (destination : Reg) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width)
    (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination (unsignedLoad state.memory address width span),
       writeF state.registerFacts destination (state.memoryFacts address),
       state.memory, state.memoryFacts⟩ :=
  ⟨writeback_preserves valuation state.registerFacts state.registers destination _ _ before.1
      (unsignedLoad_preserves valuation state.memoryFacts state.memory address width span
        supported before.2),
   before.2⟩

theorem signed_load_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (destination : Reg) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width)
    (before : Inv valuation state) :
    Inv valuation
      ⟨writeW state.registers destination (signedLoad state.memory address width span),
       writeF state.registerFacts destination (state.memoryFacts address),
       state.memory, state.memoryFacts⟩ :=
  ⟨writeback_preserves valuation state.registerFacts state.registers destination _ _ before.1
      (signedLoad_preserves valuation state.memoryFacts state.memory address width span
        supported before.2),
   before.2⟩

theorem store_preserves (valuation : Origin → Byte) (state : Pair Origin)
    (source : Reg) (address : Word) (width : Nat)
    (span : address.val + width ≤ modulus) (supported : SupportedWidth width)
    (before : Inv valuation state) :
    Inv valuation
      ⟨state.registers, state.registerFacts,
       storeLE state.memory address width span (state.registers source),
       overwrite state.memoryFacts address width span (state.registerFacts source)⟩ :=
  ⟨before.1,
   ANL.Boot.NativeByte.store_preserves valuation state.memoryFacts state.memory address width span
     (supported_positive supported) (state.registers source) (state.registerFacts source)
     before.2 (before.1 source)⟩

theorem unsigned_reload_low8 (registers : WordRegs) (memory : Memory)
    (source destination : Reg) (address : Word) (storeWidth loadWidth : Nat)
    (storeSpan : address.val + storeWidth ≤ modulus)
    (loadSpan : address.val + loadWidth ≤ modulus)
    (storeSupported : SupportedWidth storeWidth) (loadSupported : SupportedWidth loadWidth)
    (nonzero : destination ≠ zeroReg) :
    low8 (writeW registers destination
      (unsignedLoad (storeLE memory address storeWidth storeSpan (registers source))
        address loadWidth loadSpan) destination) = low8 (registers source) := by
  simpa [writeW, nonzero] using
    unsignedLoad_after_store memory address storeWidth loadWidth storeSpan loadSpan
      storeSupported loadSupported (registers source)

theorem signed_reload_low8 (registers : WordRegs) (memory : Memory)
    (source destination : Reg) (address : Word) (storeWidth loadWidth : Nat)
    (storeSpan : address.val + storeWidth ≤ modulus)
    (loadSpan : address.val + loadWidth ≤ modulus)
    (storeSupported : SupportedWidth storeWidth) (loadSupported : SupportedWidth loadWidth)
    (nonzero : destination ≠ zeroReg) :
    low8 (writeW registers destination
      (signedLoad (storeLE memory address storeWidth storeSpan (registers source))
        address loadWidth loadSpan) destination) = low8 (registers source) := by
  simpa [writeW, nonzero] using
    signedLoad_after_store memory address storeWidth loadWidth storeSpan loadSpan
      storeSupported loadSupported (registers source)

theorem finite_prefix (valuation : Origin → Byte)
    (step : Nat → Pair Origin → Pair Origin → Prop) (trace : Nat → Pair Origin) (count : Nat)
    (initial : Inv valuation (trace 0))
    (steps : ∀ index, index < count → step index (trace index) (trace (index + 1)))
    (preserves : ∀ index, index < count → ∀ before after,
      step index before after → Inv valuation before → Inv valuation after) :
    ∀ index, index ≤ count → Inv valuation (trace index) := by
  intro index
  induction index with
  | zero =>
      intro _
      exact initial
  | succ index ih =>
      intro bounded
      have within : index < count := by omega
      exact preserves index within (trace index) (trace (index + 1))
        (steps index within) (ih (by omega))

end ANL.Boot.NativeByte.State
