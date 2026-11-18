import ANL.BootV2FaultAPI
import Init.Data.Nat.Bitwise.Lemmas

set_option linter.unusedSimpArgs false

namespace ANL.Boot.V2.Fault

theorem hasIllegal_iff : hasIllegal p = true ↔ HasIllegal p := by
  simp [hasIllegal, HasIllegal, List.any_eq_true]

theorem inputValid_iff : InputValid p input ↔
    (input.illegalSitePc.isSome = true ↔ HasIllegal p) ∧
    (∀ pc, input.illegalSitePc = some pc → SiteValid p pc) ∧
    (input.forwarding.isSome = true → HasIllegal p) := by
  constructor
  · intro h
    exact ⟨h.presence, h.site, h.responseScope⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, c⟩

theorem checkInput_iff : checkInput p input = true ↔ InputValid p input := by
  rw [inputValid_iff]
  have hi := hasIllegal_iff (p := p)
  rcases input with ⟨pc, response⟩
  cases pc <;> cases response <;> cases hb : hasIllegal p <;>
    simp_all [checkInput]

theorem InputValid.pc_bound (h : InputValid p input)
    (found : input.illegalSitePc = some pc) : pc < modulus :=
  (h.site pc found).1

theorem InputValid.slot_bound (h : InputValid p input)
    (found : input.illegalSitePc = some pc) : pc + 4 ≤ modulus :=
  (h.site pc found).2.2.1

theorem SiteValid.byte_bound (h : SiteValid p pc) (offset : Nat) (within : offset < 4) :
    pc + offset < modulus := by
  have bound := h.2.2.1
  omega

theorem SiteValid.aligned (h : SiteValid p pc) : pc % 4 = 0 := h.2.1

theorem SiteValid.image_slot (h : SiteValid p pc) :
    p.image.base ≤ pc ∧ pc + 4 ≤ p.image.base + p.image.limit := h.2.2.2

theorem Event.fixed_cause (event : Event) : event.scause = 2 := rfl

theorem Event.fixed_value (event : Event) : event.stval = 0 := rfl

theorem TransferValid.fixed_payload (h : TransferValid p request transfer) :
    transfer.scause = 2 ∧ transfer.sepc = request.pc ∧ transfer.stval = 0 := h.2.2

theorem TransferValid.pc_bound (h : TransferValid p request transfer)
    (site : SiteValid p request.pc) : transfer.sepc < modulus := by
  rw [h.2.2.2.1]
  exact site.1

theorem modulus_eq : modulus = 2 ^ 64 := rfl

theorem forwardedStatus_bound (status : Nat) : forwardedStatus status < modulus := by
  have mask : modulus - 1 - 0x122 < 2 ^ 64 := by decide +kernel
  have spp : (0x100 : Nat) < 2 ^ 64 := by decide +kernel
  have base := Nat.or_lt_two_pow (Nat.and_lt_two_pow status mask) spp
  unfold forwardedStatus
  split
  · exact Nat.or_lt_two_pow base (by decide +kernel)
  · exact Nat.or_lt_two_pow base (by decide +kernel)

private theorem sie_mask (status : Nat) :
    status &&& 2 = if status.testBit 1 then 2 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have bit : (2 : Nat).testBit i = decide (i = 1) := by
    simpa [eq_comm] using (Nat.testBit_two_pow (n := 1) (m := i))
  cases h : status.testBit 1 <;> by_cases index : i = 1 <;>
    simp [Nat.testBit_and, bit, h, index]

theorem forwardedStatus_sie (status : Nat) : (forwardedStatus status).testBit 1 = false := by
  have mask : (modulus - 1 - 0x122).testBit 1 = false := by decide +kernel
  have a : (0x100 : Nat).testBit 1 = false := by decide +kernel
  have b : (0x20 : Nat).testBit 1 = false := by decide +kernel
  unfold forwardedStatus
  split <;> simp [Nat.testBit_or, Nat.testBit_and, mask, a, b]

theorem forwardedStatus_spp (status : Nat) : (forwardedStatus status).testBit 8 = true := by
  have a : (0x100 : Nat).testBit 8 = true := by decide +kernel
  unfold forwardedStatus
  split <;> simp [Nat.testBit_or, a]

theorem forwardedStatus_spie (status : Nat) :
    (forwardedStatus status).testBit 5 = status.testBit 1 := by
  have mask : (modulus - 1 - 0x122).testBit 5 = false := by decide +kernel
  have a : (0x100 : Nat).testBit 5 = false := by decide +kernel
  have b : (0x20 : Nat).testBit 5 = true := by decide +kernel
  unfold forwardedStatus
  rw [sie_mask]
  cases h : status.testBit 1 <;> simp [h, Nat.testBit_or, Nat.testBit_and, mask, a, b]

end ANL.Boot.V2.Fault
