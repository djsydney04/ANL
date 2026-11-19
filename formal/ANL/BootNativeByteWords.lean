import ANL.BootNativeByteState

namespace ANL.Boot.NativeByte.Words

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
universe u

abbrev Raw := Fin (2 ^ 32)

inductive Op where
  | addi (destination source : Reg) (immediate : Int)
  | lui (destination : Reg) (immediate : Int)
  | ld (destination base : Reg) (offset : Int)
  | lbu (destination base : Reg) (offset : Int)
  | sd (source base : Reg) (offset : Int)
  | sb (source base : Reg) (offset : Int)
  | fence
  | ret
  deriving DecidableEq, Repr

def fieldReg (raw : Raw) (shift : Nat) : Reg :=
  ⟨raw.val / 2 ^ shift % 32, Nat.mod_lt _ (by decide)⟩

def signed (value bits : Nat) : Int :=
  if value < 2 ^ (bits - 1) then (value : Int) else (value : Int) - (2 ^ bits : Nat)

def immediateI (raw : Raw) : Int := signed (raw.val / 2 ^ 20) 12
def immediateS (raw : Raw) : Int :=
  signed (raw.val / 2 ^ 25 * 32 + raw.val / 2 ^ 7 % 32) 12
def immediateU (raw : Raw) : Int := signed (raw.val / 4096 * 4096) 32

def decode (raw : Raw) : Option Op :=
  let destination := fieldReg raw 7
  let base := fieldReg raw 15
  let source := fieldReg raw 20
  let minor := raw.val / 4096 % 8
  match raw.val % 128 with
  | 0x13 => if minor = 0 then some (.addi destination base (immediateI raw)) else none
  | 0x37 => some (.lui destination (immediateU raw))
  | 0x03 =>
      if minor = 3 then some (.ld destination base (immediateI raw))
      else if minor = 4 then some (.lbu destination base (immediateI raw)) else none
  | 0x23 =>
      if minor = 3 then some (.sd source base (immediateS raw))
      else if minor = 0 then some (.sb source base (immediateS raw)) else none
  | 0x67 => if raw.val = 0x00008067 then some .ret else none
  | 0x0f => if raw.val = 0x0ff0000f then some .fence else none
  | _ => none

structure Concrete where
  pc : Word
  registers : WordRegs
  memory : Memory

def address (state : Concrete) (base : Reg) (offset : Int) : Word :=
  addW (state.registers base) (wordInt offset)

def advance (state : Concrete) (registers : WordRegs) (memory : Memory) : Concrete :=
  ⟨addW state.pc (word 4), registers, memory⟩

def returnTarget (state : Concrete) : Word :=
  -- Division by two then multiplication clears only the unsigned low bit.
  word ((state.registers raReg).val / 2 * 2)

inductive AddressClass where
  | ordinary
  | device
  | unavailable
  deriving DecidableEq

structure EEI where
  fetch : Word → Raw → Prop
  executable : Word → Nat → Prop
  addressClass : Word → AddressClass
  readable : Word → Nat → Prop
  writable : Word → Nat → Prop
  loadCompleted : Concrete → Word → Nat → Prop
  storeCompleted : Concrete → Word → Nat → Word → Prop
  deviceReadCompleted : Concrete → Word → Byte → Memory → Prop
  deviceWriteCompleted : Concrete → Word → Byte → Memory → Prop
  fenceCompleted : Concrete → Memory → Prop

structure FetchReady (env : EEI) (raw : Raw) (state : Concrete) : Prop where
  aligned : state.pc.val % 4 = 0
  span : state.pc.val + 4 ≤ modulus
  fetch : env.fetch state.pc raw
  permission : env.executable state.pc 4
  zero : state.registers zeroReg = word 0

-- Natural alignment restricts this selected profile, not all RV64 executions.
structure LoadReady (env : EEI) (state : Concrete) (location : Word) (width : Nat) : Prop where
  span : location.val + width ≤ modulus
  aligned : location.val % width = 0
  ordinary : ∀ index : Fin width,
    env.addressClass (word (location.val + index.val)) = .ordinary
  permission : env.readable location width
  completed : env.loadCompleted state location width

structure StoreReady (env : EEI) (state : Concrete) (location : Word)
    (width : Nat) (value : Word) : Prop where
  span : location.val + width ≤ modulus
  aligned : location.val % width = 0
  ordinary : ∀ index : Fin width,
    env.addressClass (word (location.val + index.val)) = .ordinary
  permission : env.writable location width
  completed : env.storeCompleted state location width value

inductive OrdinaryStep (env : EEI) : Op → Concrete → Concrete → Prop where
  | addi (state : Concrete) (destination source : Reg) (immediate : Int) :
      OrdinaryStep env (.addi destination source immediate) state
        (advance state (writeW state.registers destination
          (addW (state.registers source) (wordInt immediate))) state.memory)
  | lui (state : Concrete) (destination : Reg) (immediate : Int) :
      OrdinaryStep env (.lui destination immediate) state
        (advance state (writeW state.registers destination (wordInt immediate)) state.memory)
  | ld (state : Concrete) (destination base : Reg) (offset : Int)
      (ready : LoadReady env state (address state base offset) 8) :
      OrdinaryStep env (.ld destination base offset) state
        (advance state (writeW state.registers destination
          (unsignedLoad state.memory (address state base offset) 8 ready.span)) state.memory)
  | lbu (state : Concrete) (destination base : Reg) (offset : Int)
      (ready : LoadReady env state (address state base offset) 1) :
      OrdinaryStep env (.lbu destination base offset) state
        (advance state (writeW state.registers destination
          (unsignedLoad state.memory (address state base offset) 1 ready.span)) state.memory)
  | sd (state : Concrete) (source base : Reg) (offset : Int)
      (ready : StoreReady env state (address state base offset) 8 (state.registers source)) :
      OrdinaryStep env (.sd source base offset) state
        (advance state state.registers
          (storeLE state.memory (address state base offset) 8 ready.span (state.registers source)))
  | sb (state : Concrete) (source base : Reg) (offset : Int)
      (ready : StoreReady env state (address state base offset) 1 (state.registers source)) :
      OrdinaryStep env (.sb source base offset) state
        (advance state state.registers
          (storeLE state.memory (address state base offset) 1 ready.span (state.registers source)))
  | ret (state : Concrete) (aligned : (returnTarget state).val % 4 = 0) :
      OrdinaryStep env .ret state ⟨returnTarget state, state.registers, state.memory⟩

inductive Action where
  | silent
  | read (location : Word) (response : Byte)
  | write (location : Word) (value : Byte)
  | fence

inductive NormalStep (env : EEI) (raw : Raw) (before : Concrete) :
    Action → Concrete → Prop where
  | ordinary {op : Op} {after : Concrete}
      (ready : FetchReady env raw before) (decoded : decode raw = some op)
      (step : OrdinaryStep env op before after) :
      NormalStep env raw before .silent after
  | read (destination base : Reg) (offset : Int) (response : Byte) (memory : Memory)
      (ready : FetchReady env raw before)
      (decoded : decode raw = some (.lbu destination base offset))
      (kind : env.addressClass (address before base offset) = .device)
      (permission : env.readable (address before base offset) 1)
      (completed : env.deviceReadCompleted before (address before base offset) response memory) :
      NormalStep env raw before (.read (address before base offset) response)
        (advance before (writeW before.registers destination (word response.val)) memory)
  | write (source base : Reg) (offset : Int) (memory : Memory)
      (ready : FetchReady env raw before)
      (decoded : decode raw = some (.sb source base offset))
      (kind : env.addressClass (address before base offset) = .device)
      (permission : env.writable (address before base offset) 1)
      (completed : env.deviceWriteCompleted before (address before base offset)
        (low8 (before.registers source)) memory) :
      NormalStep env raw before
        (.write (address before base offset) (low8 (before.registers source)))
        (advance before before.registers memory)
  | fence (memory : Memory) (ready : FetchReady env raw before)
      (decoded : decode raw = some .fence)
      (completed : env.fenceCompleted before memory) :
      NormalStep env raw before .fence (advance before before.registers memory)

variable {Origin : Type u}

def paired (registerFacts : FactRegs Origin) (memoryFacts : Word → Fact Origin)
    (state : Concrete) : State.Pair Origin :=
  ⟨state.registers, registerFacts, state.memory, memoryFacts⟩

inductive Lift : Op → State.Pair Origin → State.Pair Origin → Prop where
  | addi (state : State.Pair Origin) (destination source : Reg) (immediate : Int) :
      Lift (.addi destination source immediate) state
        ⟨writeW state.registers destination (addW (state.registers source) (wordInt immediate)),
         writeF state.registerFacts destination (addiFact (state.registerFacts source) immediate),
         state.memory, state.memoryFacts⟩
  | lui (state : State.Pair Origin) (destination : Reg) (immediate : Int) :
      Lift (.lui destination immediate) state
        ⟨writeW state.registers destination (wordInt immediate),
         writeF state.registerFacts destination (luiFact immediate), state.memory, state.memoryFacts⟩
  | ld (state : State.Pair Origin) (destination base : Reg) (offset : Int)
      (span : (addW (state.registers base) (wordInt offset)).val + 8 ≤ modulus) :
      Lift (.ld destination base offset) state
        ⟨writeW state.registers destination
           (unsignedLoad state.memory (addW (state.registers base) (wordInt offset)) 8 span),
         writeF state.registerFacts destination
           (state.memoryFacts (addW (state.registers base) (wordInt offset))),
         state.memory, state.memoryFacts⟩
  | lbu (state : State.Pair Origin) (destination base : Reg) (offset : Int)
      (span : (addW (state.registers base) (wordInt offset)).val + 1 ≤ modulus) :
      Lift (.lbu destination base offset) state
        ⟨writeW state.registers destination
           (unsignedLoad state.memory (addW (state.registers base) (wordInt offset)) 1 span),
         writeF state.registerFacts destination
           (state.memoryFacts (addW (state.registers base) (wordInt offset))),
         state.memory, state.memoryFacts⟩
  | sd (state : State.Pair Origin) (source base : Reg) (offset : Int)
      (span : (addW (state.registers base) (wordInt offset)).val + 8 ≤ modulus) :
      Lift (.sd source base offset) state
        ⟨state.registers, state.registerFacts,
         storeLE state.memory (addW (state.registers base) (wordInt offset)) 8 span
           (state.registers source),
         overwrite state.memoryFacts (addW (state.registers base) (wordInt offset)) 8 span
           (state.registerFacts source)⟩
  | sb (state : State.Pair Origin) (source base : Reg) (offset : Int)
      (span : (addW (state.registers base) (wordInt offset)).val + 1 ≤ modulus) :
      Lift (.sb source base offset) state
        ⟨state.registers, state.registerFacts,
         storeLE state.memory (addW (state.registers base) (wordInt offset)) 1 span
           (state.registers source),
         overwrite state.memoryFacts (addW (state.registers base) (wordInt offset)) 1 span
           (state.registerFacts source)⟩
  | ret (state : State.Pair Origin) : Lift .ret state state

end ANL.Boot.NativeByte.Words
