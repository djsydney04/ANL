import ANL.BootNativeByteMemory

namespace ANL.Boot.NativeByte.Registers

open ANL.Boot.NativeFrame ANL.Boot.NativeByte
universe u

def wordInt (value : Int) : Word :=
  ⟨(value % (modulus : Int)).toNat, by
    have nonnegative := Int.emod_nonneg value (show (modulus : Int) ≠ 0 by decide)
    have upper := Int.emod_lt_of_pos value (show 0 < (modulus : Int) by decide)
    exact (Int.toNat_lt nonnegative).2 upper⟩

def byteInt (value : Int) : Byte :=
  ⟨(value % 256).toNat, by
    have nonnegative := Int.emod_nonneg value (show (256 : Int) ≠ 0 by decide)
    have upper := Int.emod_lt_of_pos value (show 0 < (256 : Int) by decide)
    exact (Int.toNat_lt nonnegative).2 upper⟩

def byteNat (value : Nat) : Byte :=
  ⟨value % 256, Nat.mod_lt _ (by decide)⟩

def addW (left right : Word) : Word := word (left.val + right.val)
def andW (left right : Word) : Word := word (left.val &&& right.val)
def addB (left right : Byte) : Byte := byteNat (left.val + right.val)
def andB (left right : Byte) : Byte := byteNat (left.val &&& right.val)

theorem low8_wordInt (value : Int) : low8 (wordInt value) = byteInt value := by
  apply Fin.ext
  change (value % (modulus : Int)).toNat % 256 = (value % 256).toNat
  have nonnegative := Int.emod_nonneg value (show (modulus : Int) ≠ 0 by decide)
  calc
    (value % (modulus : Int)).toNat % 256 =
        ((value % (modulus : Int)) % 256).toNat :=
      (Int.toNat_emod nonnegative (show 0 ≤ (256 : Int) by decide)).symm
    _ = (value % 256).toNat :=
      congrArg Int.toNat (Int.emod_emod_of_dvd value
        (show (256 : Int) ∣ (modulus : Int) by decide))

theorem low8_addW (left right : Word) :
    low8 (addW left right) = addB (low8 left) (low8 right) := by
  apply Fin.ext
  change (low8 (word (left.val + right.val))).val =
    ((left.val % 256) + (right.val % 256)) % 256
  rw [low8_word]
  exact Nat.add_mod left.val right.val 256

theorem low8_andW (left right : Word) :
    low8 (andW left right) = andB (low8 left) (low8 right) := by
  apply Fin.ext
  change (low8 (word (left.val &&& right.val))).val =
    ((left.val % 256) &&& (right.val % 256)) % 256
  rw [low8_word]
  have projected : (left.val &&& right.val) % 256 =
      (left.val % 256) &&& (right.val % 256) :=
    Nat.and_mod_two_pow (a := left.val) (b := right.val) (n := 8)
  rw [← projected, Nat.mod_mod]

theorem wordInt_zero : wordInt 0 = word 0 := by
  apply Fin.ext
  simp [wordInt, word]

theorem byteInt_zero : byteInt 0 = byteNat 0 := by
  apply Fin.ext
  simp [byteInt, byteNat]

theorem addW_zero (value : Word) : addW value (word 0) = value := by
  apply Fin.ext
  simp [addW, word, Nat.mod_eq_of_lt value.isLt]

theorem zero_addW (value : Word) : addW (word 0) value = value := by
  apply Fin.ext
  simp [addW, word, Nat.mod_eq_of_lt value.isLt]

theorem addB_zero (value : Byte) : addB value (byteNat 0) = value := by
  apply Fin.ext
  simp [addB, byteNat, Nat.mod_eq_of_lt value.isLt]

theorem zero_addB (value : Byte) : addB (byteNat 0) value = value := by
  apply Fin.ext
  simp [addB, byteNat, Nat.mod_eq_of_lt value.isLt]

theorem andB_ones (value : Byte) : andB value (byteNat 255) = value := by
  apply Fin.ext
  change (value.val &&& 255) % 256 = value.val
  have masked : value.val &&& 255 = value.val :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) value.isLt
  rw [masked]
  exact Nat.mod_eq_of_lt value.isLt

variable {Origin : Type u}

def addiFact (fact : Fact Origin) (immediate : Int) : Fact Origin :=
  match fact with
  | .constant value => .constant (addB value (byteInt immediate))
  | other => if immediate = 0 then other else .unknown

def andiFact (fact : Fact Origin) (immediate : Int) : Fact Origin :=
  if byteInt immediate = byteNat 255 then fact
  else match fact with
    | .constant value => .constant (andB value (byteInt immediate))
    | _ => .unknown

def luiFact (immediate : Int) : Fact Origin := .constant (byteInt immediate)
def auipcFact (pc : Word) (immediate : Int) : Fact Origin :=
  .constant (low8 (addW pc (wordInt immediate)))

theorem addiFact_constant (value : Byte) (immediate : Int) :
    addiFact (Origin := Origin) (.constant value) immediate =
      .constant (addB value (byteInt immediate)) := rfl

theorem addiFact_zero (fact : Fact Origin) : addiFact fact 0 = fact := by
  cases fact <;> simp [addiFact, byteInt_zero, addB_zero]

theorem andiFact_mask (fact : Fact Origin) (immediate : Int)
    (mask : byteInt immediate = byteNat 255) : andiFact fact immediate = fact := by
  simp [andiFact, mask]

theorem andiFact_constant (value : Byte) (immediate : Int) :
    andiFact (Origin := Origin) (.constant value) immediate =
      .constant (andB value (byteInt immediate)) := by
  by_cases mask : byteInt immediate = byteNat 255
  · simp [andiFact, mask, andB_ones]
  · simp [andiFact, mask]

theorem addi_sound (valuation : Origin → Byte) (fact : Fact Origin)
    (value : Word) (immediate : Int) (before : Holds valuation fact (low8 value)) :
    Holds valuation (addiFact fact immediate) (low8 (addW value (wordInt immediate))) := by
  rw [low8_addW, low8_wordInt]
  cases fact with
  | unknown => simp [addiFact, Holds]
  | constant expected =>
    change low8 value = expected at before
    change addB (low8 value) (byteInt immediate) = addB expected (byteInt immediate)
    rw [before]
  | origin token =>
    by_cases zero : immediate = 0
    · subst immediate
      simpa [addiFact, Holds, byteInt_zero, addB_zero] using before
    · simp [addiFact, zero, Holds]

theorem addi_zero_sound (valuation : Origin → Byte) (fact : Fact Origin)
    (value : Word) (before : Holds valuation fact (low8 value)) :
    Holds valuation fact (low8 (addW value (wordInt 0))) := by
  simpa [wordInt_zero, addW_zero] using before

theorem andi_sound (valuation : Origin → Byte) (fact : Fact Origin)
    (value : Word) (immediate : Int) (before : Holds valuation fact (low8 value)) :
    Holds valuation (andiFact fact immediate) (low8 (andW value (wordInt immediate))) := by
  rw [low8_andW, low8_wordInt]
  by_cases mask : byteInt immediate = byteNat 255
  · simpa [andiFact, mask, andB_ones] using before
  · cases fact with
    | unknown => simp [andiFact, mask, Holds]
    | constant expected =>
      change low8 value = expected at before
      simp [andiFact, mask, Holds, before]
    | origin token => simp [andiFact, mask, Holds]

theorem andi_mask_sound (valuation : Origin → Byte) (fact : Fact Origin)
    (value : Word) (immediate : Int) (before : Holds valuation fact (low8 value))
    (mask : byteInt immediate = byteNat 255) :
    Holds valuation fact (low8 (andW value (wordInt immediate))) := by
  simpa [andiFact, mask] using andi_sound valuation fact value immediate before

theorem lui_sound (valuation : Origin → Byte) (immediate : Int) :
    Holds valuation (luiFact immediate) (low8 (wordInt immediate)) := by
  exact low8_wordInt immediate

theorem auipc_sound (valuation : Origin → Byte) (pc : Word) (immediate : Int) :
    Holds valuation (auipcFact pc immediate) (low8 (addW pc (wordInt immediate))) := rfl

theorem auipcFact_bytes (pc : Word) (immediate : Int) :
    auipcFact (Origin := Origin) pc immediate =
      .constant (addB (low8 pc) (byteInt immediate)) := by
  simp [auipcFact, low8_addW, low8_wordInt]

abbrev WordRegs := Reg → Word
abbrev FactRegs (Origin : Type u) := Reg → Fact Origin

def RegsHold (valuation : Origin → Byte) (facts : FactRegs Origin) (registers : WordRegs) : Prop :=
  ∀ reg, Holds valuation (facts reg) (low8 (registers reg))

def writeW (registers : WordRegs) (destination : Reg) (value : Word) : WordRegs :=
  if destination = zeroReg then registers
  else fun reg => if reg = destination then value else registers reg

def writeF (facts : FactRegs Origin) (destination : Reg) (fact : Fact Origin) : FactRegs Origin :=
  if destination = zeroReg then facts
  else fun reg => if reg = destination then fact else facts reg

theorem writeW_zero (registers : WordRegs) (value : Word) :
    writeW registers zeroReg value = registers := by simp [writeW]

theorem writeF_zero (facts : FactRegs Origin) (fact : Fact Origin) :
    writeF facts zeroReg fact = facts := by simp [writeF]

theorem writeW_other (registers : WordRegs) (destination reg : Reg) (value : Word)
    (other : reg ≠ destination) : writeW registers destination value reg = registers reg := by
  by_cases zero : destination = zeroReg <;> simp [writeW, zero, other]

theorem writeF_other (facts : FactRegs Origin) (destination reg : Reg) (fact : Fact Origin)
    (other : reg ≠ destination) : writeF facts destination fact reg = facts reg := by
  by_cases zero : destination = zeroReg <;> simp [writeF, zero, other]

theorem writeW_at_zero (registers : WordRegs) (destination : Reg) (value : Word) :
    writeW registers destination value zeroReg = registers zeroReg := by
  by_cases zero : destination = zeroReg
  · simp [writeW, zero]
  · exact writeW_other registers destination zeroReg value (Ne.symm zero)

theorem writeF_at_zero (facts : FactRegs Origin) (destination : Reg) (fact : Fact Origin) :
    writeF facts destination fact zeroReg = facts zeroReg := by
  by_cases zero : destination = zeroReg
  · simp [writeF, zero]
  · exact writeF_other facts destination zeroReg fact (Ne.symm zero)

theorem writeW_preserves_zero (registers : WordRegs) (destination : Reg) (value : Word)
    (zero : registers zeroReg = word 0) : writeW registers destination value zeroReg = word 0 :=
  (writeW_at_zero registers destination value).trans zero

theorem writeF_preserves_zero (facts : FactRegs Origin) (destination : Reg) (fact : Fact Origin)
    (zero : facts zeroReg = .constant (byteNat 0)) :
    writeF facts destination fact zeroReg = .constant (byteNat 0) :=
  (writeF_at_zero facts destination fact).trans zero

theorem writeback_preserves (valuation : Origin → Byte) (facts : FactRegs Origin)
    (registers : WordRegs) (destination : Reg) (fact : Fact Origin) (value : Word)
    (before : RegsHold valuation facts registers) (known : Holds valuation fact (low8 value)) :
    RegsHold valuation (writeF facts destination fact) (writeW registers destination value) := by
  intro reg
  by_cases zero : destination = zeroReg
  · simpa [writeF, writeW, zero] using before reg
  · by_cases selected : reg = destination
    · simpa [writeF, writeW, zero, selected] using known
    · simpa [writeF, writeW, zero, selected] using before reg

theorem addi_writeback (valuation : Origin → Byte) (facts : FactRegs Origin)
    (registers : WordRegs) (source destination : Reg) (immediate : Int)
    (before : RegsHold valuation facts registers) :
    RegsHold valuation (writeF facts destination (addiFact (facts source) immediate))
      (writeW registers destination (addW (registers source) (wordInt immediate))) :=
  writeback_preserves valuation facts registers destination _ _ before
    (addi_sound valuation (facts source) (registers source) immediate (before source))

theorem andi_writeback (valuation : Origin → Byte) (facts : FactRegs Origin)
    (registers : WordRegs) (source destination : Reg) (immediate : Int)
    (before : RegsHold valuation facts registers) :
    RegsHold valuation (writeF facts destination (andiFact (facts source) immediate))
      (writeW registers destination (andW (registers source) (wordInt immediate))) :=
  writeback_preserves valuation facts registers destination _ _ before
    (andi_sound valuation (facts source) (registers source) immediate (before source))

theorem lui_writeback (valuation : Origin → Byte) (facts : FactRegs Origin)
    (registers : WordRegs) (destination : Reg) (immediate : Int)
    (before : RegsHold valuation facts registers) :
    RegsHold valuation (writeF facts destination (luiFact immediate))
      (writeW registers destination (wordInt immediate)) :=
  writeback_preserves valuation facts registers destination _ _ before
    (lui_sound valuation immediate)

theorem auipc_writeback (valuation : Origin → Byte) (facts : FactRegs Origin)
    (registers : WordRegs) (destination : Reg) (pc : Word) (immediate : Int)
    (before : RegsHold valuation facts registers) :
    RegsHold valuation (writeF facts destination (auipcFact pc immediate))
      (writeW registers destination (addW pc (wordInt immediate))) :=
  writeback_preserves valuation facts registers destination _ _ before
    (auipc_sound valuation pc immediate)

theorem holds_unknown (valuation : Origin → Byte) (value : Byte) :
    Holds valuation .unknown value := True.intro

theorem weaken_unknown (valuation : Origin → Byte) (fact : Fact Origin) (value : Byte) :
    Holds valuation fact value → Holds valuation .unknown value :=
  fun _ => holds_unknown valuation value

theorem unknown_writeback (valuation : Origin → Byte) (facts : FactRegs Origin)
    (registers : WordRegs) (destination : Reg) (value : Word)
    (before : RegsHold valuation facts registers) :
    RegsHold valuation (writeF facts destination .unknown) (writeW registers destination value) :=
  writeback_preserves valuation facts registers destination _ _ before
    (holds_unknown valuation (low8 value))

theorem unchanged (valuation : Origin → Byte) (facts : FactRegs Origin) (registers : WordRegs)
    (before : RegsHold valuation facts registers) : RegsHold valuation facts registers := before

end ANL.Boot.NativeByte.Registers
