import NativeUartFenceCertificate
import ANL.BootNativeByteMemoryFull

namespace NativeUartFenceRestoration

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
open ANL.Boot.NativeByte.Words ANL.Boot.NativeByte.MemoryFull
open NativeByteWordsLiterals NativeUartFenceCertificate

private theorem slot_values (entry : Word) :
    (word (entry.val - 8)).val = entry.val - 8 ∧
    (word (entry.val - 16)).val = entry.val - 16 := by
  have upper := entry.isLt
  constructor <;> exact Nat.mod_eq_of_lt (by omega)

theorem saved_spans (entry : Word) (depth : 16 ≤ entry.val) :
    (word (entry.val - 8)).val + 8 ≤ modulus ∧
    (word (entry.val - 16)).val + 8 ≤ modulus := by
  obtain ⟨high, low⟩ := slot_values entry
  have upper := entry.isLt
  rw [high, low]
  omega

private theorem slots_adjacent (entry : Word) (depth : 16 ≤ entry.val) :
    (word (entry.val - 16)).val + 8 = (word (entry.val - 8)).val := by
  obtain ⟨high, low⟩ := slot_values entry
  rw [high, low]
  omega

private theorem addi_equations (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.addi destination source immediate)) :
    after.registers = writeW before.registers destination
      (addW (before.registers source) (wordInt immediate)) ∧
    after.memory = before.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary
      exact ⟨rfl, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem sd_equations (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.sd source base offset)) :
    ∃ ready : StoreReady env before (address before base offset) 8 (before.registers source),
      after.registers = before.registers ∧
      after.memory = storeLE before.memory (address before base offset) 8 ready.span
        (before.registers source) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | sd _ _ _ _ ready => exact ⟨ready, rfl, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem ld_equations (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.ld destination base offset)) :
    ∃ ready : LoadReady env before (address before base offset) 8,
      after.registers = writeW before.registers destination
        (unsignedLoad before.memory (address before base offset) 8 ready.span) ∧
      after.memory = before.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | ld _ _ _ _ ready => exact ⟨ready, rfl, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem store_transport {leftMemory rightMemory : Memory}
    {leftAddress rightAddress : Word} {leftValue rightValue : Word}
    {leftSpan : leftAddress.val + 8 ≤ modulus} {rightSpan : rightAddress.val + 8 ≤ modulus}
    (memoryEqual : leftMemory = rightMemory) (addressEqual : leftAddress = rightAddress)
    (valueEqual : leftValue = rightValue) :
    storeLE leftMemory leftAddress 8 leftSpan leftValue =
      storeLE rightMemory rightAddress 8 rightSpan rightValue := by
  subst rightMemory
  subst rightAddress
  subst rightValue
  rfl

private theorem load_transport {leftMemory rightMemory : Memory}
    {leftAddress rightAddress : Word}
    {leftSpan : leftAddress.val + 8 ≤ modulus} {rightSpan : rightAddress.val + 8 ≤ modulus}
    (memoryEqual : leftMemory = rightMemory) (addressEqual : leftAddress = rightAddress) :
    unsignedLoad leftMemory leftAddress 8 leftSpan =
      unsignedLoad rightMemory rightAddress 8 rightSpan := by
  subst rightMemory
  subst rightAddress
  rfl

theorem restored_prefix (env : EEI) (states : Fin 10 → Concrete)
    (actions : Fin 9 → Action) (entry : Word) (trace : Prefix env states actions)
    (entryPC : (states 0).pc = word 0x80200328)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 16 ≤ entry.val)
    (keptRa : AgreesOn (states 4).memory (states 5).memory
      (word (entry.val - 8)) 8 (saved_spans entry depth).1)
    (keptFp : AgreesOn (states 4).memory (states 5).memory
      (word (entry.val - 16)) 8 (saved_spans entry depth).2) :
    (states 9).registers raReg = (states 0).registers raReg ∧
    (states 9).registers ⟨8, by decide⟩ = (states 0).registers ⟨8, by decide⟩ ∧
    (states 9).registers spReg = entry ∧
    (states 9).registers ⟨10, by decide⟩ = word 0 ∧
    (states 9).pc = word 0x8020034c := by
  obtain ⟨⟨result9, sp9⟩, ⟨pcs, _⟩, ea1, ea2, ea6, ea7, _, _, _, _, _⟩ :=
    prefix_projection env states actions entry trace entryPC zero stack depth
  rcases trace with ⟨h0, h1, h2, h3, _, h5, h6, h7, h8⟩
  obtain ⟨r1, m1⟩ := addi_equations h0 decode_word_202
  obtain ⟨_, r2, m2⟩ := sd_equations h1 decode_word_203
  obtain ⟨_, _, m3⟩ := sd_equations h2 decode_word_204
  obtain ⟨_, m4⟩ := addi_equations h3 decode_word_205
  obtain ⟨_, m6⟩ := addi_equations h5 decode_word_207
  obtain ⟨loadRa, r7, m7⟩ := ld_equations h6 decode_word_208
  obtain ⟨loadFp, r8, _⟩ := ld_equations h7 decode_word_209
  obtain ⟨r9, _⟩ := addi_equations h8 decode_word_210
  have sourceRa : (states 1).registers raReg = (states 0).registers raReg := by
    rw [r1] <;> rfl
  have sourceFp : (states 2).registers ⟨8, by decide⟩ =
      (states 0).registers ⟨8, by decide⟩ := by
    rw [r2, r1] <;> rfl
  have saveRa : (states 2).memory =
      storeLE (states 0).memory (word (entry.val - 8)) 8
        (saved_spans entry depth).1 ((states 0).registers raReg) := by
    exact m2.trans (store_transport m1 ea1 sourceRa)
  have beforeFence : (states 4).memory =
      storeLE (states 2).memory (word (entry.val - 16)) 8
        (saved_spans entry depth).2 ((states 0).registers ⟨8, by decide⟩) := by
    exact m4.trans (m3.trans (store_transport rfl ea2 sourceFp))
  have adjacent := slots_adjacent entry depth
  have firstToCut : AgreesOn (states 2).memory (states 4).memory
      (word (entry.val - 8)) 8 (saved_spans entry depth).1 := by
    rw [beforeFence]
    exact store_preserves_range (states 2).memory (word (entry.val - 16)) 8
      (saved_spans entry depth).2 ((states 0).registers ⟨8, by decide⟩)
      (word (entry.val - 8)) 8 (saved_spans entry depth).1 (Or.inl (by omega))
  have raAgreement := agrees_trans (states 2).memory (states 4).memory (states 5).memory
    (word (entry.val - 8)) 8 (saved_spans entry depth).1 firstToCut keptRa
  rw [saveRa] at raAgreement
  have reloadRa : unsignedLoad (states 5).memory (word (entry.val - 8)) 8
      (saved_spans entry depth).1 = (states 0).registers raReg :=
    (reload_saved_eight (states 0).memory (states 5).memory (word (entry.val - 8))
      (saved_spans entry depth).1 ((states 0).registers raReg) raAgreement).1
  rw [beforeFence] at keptFp
  have reloadFp : unsignedLoad (states 5).memory (word (entry.val - 16)) 8
      (saved_spans entry depth).2 = (states 0).registers ⟨8, by decide⟩ :=
    (reload_saved_eight (states 2).memory (states 5).memory (word (entry.val - 16))
      (saved_spans entry depth).2 ((states 0).registers ⟨8, by decide⟩) keptFp).1
  have ra7 : (states 7).registers raReg = (states 0).registers raReg := by
    rw [r7]
    change unsignedLoad (states 6).memory (address (states 6) spReg 8) 8
      loadRa.span = (states 0).registers raReg
    exact (load_transport m6 ea6).trans reloadRa
  have fp8 : (states 8).registers ⟨8, by decide⟩ =
      (states 0).registers ⟨8, by decide⟩ := by
    rw [r8]
    change unsignedLoad (states 7).memory (address (states 7) spReg 0) 8
      loadFp.span = (states 0).registers ⟨8, by decide⟩
    exact (load_transport (m7.trans m6) ea7).trans reloadFp
  have ra9 : (states 9).registers raReg = (states 0).registers raReg := by
    rw [r9]
    change (states 8).registers raReg = (states 0).registers raReg
    rw [r8]
    change (states 7).registers raReg = (states 0).registers raReg
    exact ra7
  have fp9 : (states 9).registers ⟨8, by decide⟩ =
      (states 0).registers ⟨8, by decide⟩ := by
    rw [r9]
    change (states 8).registers ⟨8, by decide⟩ = (states 0).registers ⟨8, by decide⟩
    exact fp8
  have lastPC := congrArg List.getLast? pcs
  change some ((states 9).pc) = some (word 0x8020034c) at lastPC
  exact ⟨ra9, fp9, sp9, result9, Option.some.inj lastPC⟩

private theorem return_equations (step : NormalStep env raw before action after)
    (decoded : decode raw = some .ret) :
    action = .silent ∧ after.pc = returnTarget before ∧
      after.registers = before.registers ∧ after.memory = before.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary
      exact ⟨rfl, rfl, rfl, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

theorem restored_return (env : EEI) (states : Fin 10 → Concrete)
    (actions : Fin 9 → Action) (entry : Word) (trace : Prefix env states actions)
    (entryPC : (states 0).pc = word 0x80200328)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 16 ≤ entry.val)
    (keptRa : AgreesOn (states 4).memory (states 5).memory
      (word (entry.val - 8)) 8 (saved_spans entry depth).1)
    (keptFp : AgreesOn (states 4).memory (states 5).memory
      (word (entry.val - 16)) 8 (saved_spans entry depth).2)
    (returnAction : Action) (after : Concrete)
    (returned : NormalStep env ⟨0x00008067, by decide⟩ (states 9) returnAction after)
    (entryAligned : ((states 0).registers raReg).val % 4 = 0) :
    returnAction = .silent ∧ after.pc = (states 0).registers raReg ∧
    after.registers raReg = (states 0).registers raReg ∧
    after.registers ⟨8, by decide⟩ = (states 0).registers ⟨8, by decide⟩ ∧
    after.registers spReg = entry ∧ after.registers ⟨10, by decide⟩ = word 0 ∧
    after.memory = (states 9).memory := by
  obtain ⟨ra, fp, sp, result, _⟩ :=
    restored_prefix env states actions entry trace entryPC zero stack depth keptRa keptFp
  obtain ⟨action, target, registers, memory⟩ := return_equations returned return_word
  have restoredTarget : returnTarget (states 9) = (states 0).registers raReg := by
    unfold returnTarget
    rw [ra]
    apply Fin.ext
    change (((states 0).registers raReg).val / 2 * 2) % modulus =
      ((states 0).registers raReg).val
    have clearLowBit : ((states 0).registers raReg).val / 2 * 2 =
        ((states 0).registers raReg).val := by omega
    rw [clearLowBit, Nat.mod_eq_of_lt ((states 0).registers raReg).isLt]
  refine ⟨action, target.trans restoredTarget, ?_, ?_, ?_, ?_, memory⟩
  · rw [registers]
    exact ra
  · rw [registers]
    exact fp
  · rw [registers]
    exact sp
  · rw [registers]
    exact result

end NativeUartFenceRestoration
