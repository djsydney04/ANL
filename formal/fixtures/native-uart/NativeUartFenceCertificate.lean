import NativeByteWordsLiterals

namespace NativeUartFenceCertificate

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
open ANL.Boot.NativeByte.Words NativeByteWordsLiterals

def Prefix (env : EEI) (states : Fin 10 → Concrete) (actions : Fin 9 → Action) : Prop :=
  NormalStep env ⟨0xff010113, by decide⟩ (states 0) (actions 0) (states 1) ∧
  NormalStep env ⟨0x00113423, by decide⟩ (states 1) (actions 1) (states 2) ∧
  NormalStep env ⟨0x00813023, by decide⟩ (states 2) (actions 2) (states 3) ∧
  NormalStep env ⟨0x01010413, by decide⟩ (states 3) (actions 3) (states 4) ∧
  NormalStep env ⟨0x0ff0000f, by decide⟩ (states 4) (actions 4) (states 5) ∧
  NormalStep env ⟨0x00000513, by decide⟩ (states 5) (actions 5) (states 6) ∧
  NormalStep env ⟨0x00813083, by decide⟩ (states 6) (actions 6) (states 7) ∧
  NormalStep env ⟨0x00013403, by decide⟩ (states 7) (actions 7) (states 8) ∧
  NormalStep env ⟨0x01010113, by decide⟩ (states 8) (actions 8) (states 9)

private theorem addi_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.addi destination source immediate)) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      after.registers = writeW before.registers destination
        (addW (before.registers source) (wordInt immediate)) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary
      exact ⟨rfl, rfl, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem sd_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.sd source base offset)) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      after.registers = before.registers ∧
      StoreReady env before (address before base offset) 8 (before.registers source) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | sd _ _ _ _ ready => exact ⟨rfl, rfl, rfl, ready⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem ld_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.ld destination base offset)) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      ∃ ready : LoadReady env before (address before base offset) 8,
        after.registers = writeW before.registers destination
          (unsignedLoad before.memory (address before base offset) 8 ready.span) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | ld _ _ _ _ ready => exact ⟨rfl, rfl, ready, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem fence_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some .fence) :
    action = .fence ∧ after.pc = addW before.pc (word 4) ∧
      after.registers = before.registers ∧ env.fenceCompleted before after.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ _ completed => exact ⟨rfl, rfl, rfl, completed⟩

private theorem sub_sixteen (entry : Word) (depth : 16 ≤ entry.val) :
    addW entry (wordInt (-16)) = word (entry.val - 16) := by
  apply Fin.ext
  change (entry.val + (wordInt (-16)).val) % modulus = (entry.val - 16) % modulus
  have negative : (wordInt (-16)).val = modulus - 16 := by decide
  rw [negative]
  have rearrange : entry.val + (modulus - 16) = (entry.val - 16) + modulus := by
    have large : 16 ≤ modulus := by decide
    omega
  rw [rearrange, Nat.add_mod_right]

private theorem restore_sixteen (entry : Word) (depth : 16 ≤ entry.val) :
    addW (word (entry.val - 16)) (wordInt 16) = entry := by
  apply Fin.ext
  change ((entry.val - 16) % modulus + (wordInt 16).val) % modulus = entry.val
  have small : entry.val - 16 < modulus := by have bound := entry.isLt; omega
  have positive : (wordInt 16).val = 16 := by decide
  rw [Nat.mod_eq_of_lt small, positive, Nat.sub_add_cancel depth,
    Nat.mod_eq_of_lt entry.isLt]

private theorem slot_eight (entry : Word) (depth : 16 ≤ entry.val) :
    addW (word (entry.val - 16)) (wordInt 8) = word (entry.val - 8) := by
  apply Fin.ext
  change ((entry.val - 16) % modulus + (wordInt 8).val) % modulus =
    (entry.val - 8) % modulus
  have small : entry.val - 16 < modulus := by have bound := entry.isLt; omega
  have positive : (wordInt 8).val = 8 := by decide
  rw [Nat.mod_eq_of_lt small, positive]
  have rearrange : entry.val - 16 + 8 = entry.val - 8 := by omega
  rw [rearrange]

theorem frame_bounds (entry : Word) (depth : 16 ≤ entry.val)
    (aligned : entry.val % 16 = 0) :
    (word (entry.val - 8)).val = entry.val - 8 ∧
    (word (entry.val - 16)).val = entry.val - 16 ∧
    entry.val - 16 ≤ (word (entry.val - 8)).val ∧
    (word (entry.val - 8)).val + 8 ≤ entry.val ∧
    (word (entry.val - 16)).val + 8 ≤ entry.val ∧
    (word (entry.val - 8)).val % 8 = 0 ∧
    (word (entry.val - 16)).val % 8 = 0 ∧
    (word (entry.val - 8)).val + 8 ≤ modulus ∧
    (word (entry.val - 16)).val + 8 ≤ modulus := by
  have upper := entry.isLt
  have first : (word (entry.val - 8)).val = entry.val - 8 :=
    Nat.mod_eq_of_lt (by omega)
  have second : (word (entry.val - 16)).val = entry.val - 16 :=
    Nat.mod_eq_of_lt (by omega)
  rw [first, second]
  omega

theorem prefix_projection (env : EEI) (states : Fin 10 → Concrete)
    (actions : Fin 9 → Action) (entry : Word) (trace : Prefix env states actions)
    (entryPC : (states 0).pc = word 0x80200328)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 16 ≤ entry.val) :
    ((states 9).registers ⟨10, by decide⟩ = word 0 ∧
      (states 9).registers spReg = entry) ∧
    ([(states 0).pc, (states 1).pc, (states 2).pc, (states 3).pc, (states 4).pc,
      (states 5).pc, (states 6).pc, (states 7).pc, (states 8).pc, (states 9).pc] =
      [word 0x80200328, word 0x8020032c, word 0x80200330, word 0x80200334,
       word 0x80200338, word 0x8020033c, word 0x80200340, word 0x80200344,
       word 0x80200348, word 0x8020034c] ∧
     [actions 0, actions 1, actions 2, actions 3, actions 4,
      actions 5, actions 6, actions 7, actions 8] =
      [.silent, .silent, .silent, .silent, .fence, .silent, .silent, .silent, .silent]) ∧
    (address (states 1) spReg 8 = word (entry.val - 8) ∧
     address (states 2) spReg 0 = word (entry.val - 16) ∧
     address (states 6) spReg 8 = word (entry.val - 8) ∧
     address (states 7) spReg 0 = word (entry.val - 16) ∧
     StoreReady env (states 1) (word (entry.val - 8)) 8 ((states 1).registers raReg) ∧
     StoreReady env (states 2) (word (entry.val - 16)) 8 ((states 2).registers ⟨8, by decide⟩) ∧
     LoadReady env (states 6) (word (entry.val - 8)) 8 ∧
     LoadReady env (states 7) (word (entry.val - 16)) 8 ∧
     env.fenceCompleted (states 4) (states 5).memory) := by
  rcases trace with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨a0, p1, r1⟩ := addi_projection h0 decode_word_202
  obtain ⟨a1, p2, r2, storeRa⟩ := sd_projection h1 decode_word_203
  obtain ⟨a2, p3, r3, storeX8⟩ := sd_projection h2 decode_word_204
  obtain ⟨a3, p4, r4⟩ := addi_projection h3 decode_word_205
  obtain ⟨a4, p5, r5, completed⟩ := fence_projection h4 decode_word_206
  obtain ⟨a5, p6, r6⟩ := addi_projection h5 decode_word_207
  obtain ⟨a6, p7, loadRa, r7⟩ := ld_projection h6 decode_word_208
  obtain ⟨a7, p8, loadX8, r8⟩ := ld_projection h7 decode_word_209
  obtain ⟨a8, p9, r9⟩ := addi_projection h8 decode_word_210
  have sp1 : (states 1).registers spReg = word (entry.val - 16) := by
    rw [r1]
    change addW ((states 0).registers spReg) (wordInt (-16)) = word (entry.val - 16)
    rw [stack, sub_sixteen entry depth]
  have sp2 : (states 2).registers spReg = word (entry.val - 16) := by rw [r2]; exact sp1
  have sp3 : (states 3).registers spReg = word (entry.val - 16) := by rw [r3]; exact sp2
  have sp4 : (states 4).registers spReg = word (entry.val - 16) := by
    rw [r4]
    change (states 3).registers spReg = word (entry.val - 16)
    exact sp3
  have sp5 : (states 5).registers spReg = word (entry.val - 16) := by rw [r5]; exact sp4
  have sp6 : (states 6).registers spReg = word (entry.val - 16) := by
    rw [r6]
    change (states 5).registers spReg = word (entry.val - 16)
    exact sp5
  have sp7 : (states 7).registers spReg = word (entry.val - 16) := by
    rw [r7]
    change (states 6).registers spReg = word (entry.val - 16)
    exact sp6
  have sp8 : (states 8).registers spReg = word (entry.val - 16) := by
    rw [r8]
    change (states 7).registers spReg = word (entry.val - 16)
    exact sp7
  have sp9 : (states 9).registers spReg = entry := by
    rw [r9]
    change addW ((states 8).registers spReg) (wordInt 16) = entry
    rw [sp8, restore_sixteen entry depth]
  have zero5 : (states 5).registers zeroReg = word 0 := by
    rw [r5, r4, r3, r2, r1]
    simp only [writeW_at_zero]
    exact zero
  have result6 : (states 6).registers ⟨10, by decide⟩ = word 0 := by
    rw [r6]
    change addW ((states 5).registers zeroReg) (wordInt 0) = word 0
    rw [zero5, wordInt_zero, addW_zero]
  have result7 : (states 7).registers ⟨10, by decide⟩ = word 0 := by
    rw [r7]
    change (states 6).registers ⟨10, by decide⟩ = word 0
    exact result6
  have result8 : (states 8).registers ⟨10, by decide⟩ = word 0 := by
    rw [r8]
    change (states 7).registers ⟨10, by decide⟩ = word 0
    exact result7
  have result9 : (states 9).registers ⟨10, by decide⟩ = word 0 := by
    rw [r9]
    change (states 8).registers ⟨10, by decide⟩ = word 0
    exact result8
  have pc1 : (states 1).pc = word 0x8020032c := by rw [p1, entryPC] <;> decide
  have pc2 : (states 2).pc = word 0x80200330 := by rw [p2, pc1] <;> decide
  have pc3 : (states 3).pc = word 0x80200334 := by rw [p3, pc2] <;> decide
  have pc4 : (states 4).pc = word 0x80200338 := by rw [p4, pc3] <;> decide
  have pc5 : (states 5).pc = word 0x8020033c := by rw [p5, pc4] <;> decide
  have pc6 : (states 6).pc = word 0x80200340 := by rw [p6, pc5] <;> decide
  have pc7 : (states 7).pc = word 0x80200344 := by rw [p7, pc6] <;> decide
  have pc8 : (states 8).pc = word 0x80200348 := by rw [p8, pc7] <;> decide
  have pc9 : (states 9).pc = word 0x8020034c := by rw [p9, pc8] <;> decide
  have ea1 : address (states 1) spReg 8 = word (entry.val - 8) := by
    unfold address
    rw [sp1, slot_eight entry depth]
  have ea2 : address (states 2) spReg 0 = word (entry.val - 16) := by
    unfold address
    rw [sp2, wordInt_zero, addW_zero]
  have ea6 : address (states 6) spReg 8 = word (entry.val - 8) := by
    unfold address
    rw [sp6, slot_eight entry depth]
  have ea7 : address (states 7) spReg 0 = word (entry.val - 16) := by
    unfold address
    rw [sp7, wordInt_zero, addW_zero]
  refine ⟨⟨result9, sp9⟩, ⟨?_, ?_⟩, ea1, ea2, ea6, ea7, ?_, ?_, ?_, ?_, completed⟩
  · rw [entryPC, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9]
  · rw [a0, a1, a2, a3, a4, a5, a6, a7, a8]
  · rw [← ea1]
    exact storeRa
  · rw [← ea2]
    exact storeX8
  · rw [← ea6]
    exact loadRa
  · rw [← ea7]
    exact loadX8

theorem return_word : decode ⟨0x00008067, by decide⟩ = some .ret := decode_word_211

end NativeUartFenceCertificate
