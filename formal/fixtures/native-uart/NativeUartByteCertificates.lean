import NativeByteWordsLiterals

namespace NativeUartByteCertificates

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
open ANL.Boot.NativeByte.Words NativeByteWordsLiterals

abbrev a0 : Reg := ⟨10, by decide⟩
abbrev a1 : Reg := ⟨11, by decide⟩
abbrev fp : Reg := ⟨8, by decide⟩

def ReadPrefix (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) : Prop :=
  NormalStep env ⟨0xfe010113, by decide⟩ (states 0) (actions 0) (states 1) ∧
  NormalStep env ⟨0x00113c23, by decide⟩ (states 1) (actions 1) (states 2) ∧
  NormalStep env ⟨0x00813823, by decide⟩ (states 2) (actions 2) (states 3) ∧
  NormalStep env ⟨0x02010413, by decide⟩ (states 3) (actions 3) (states 4) ∧
  NormalStep env ⟨0x10000537, by decide⟩ (states 4) (actions 4) (states 5) ∧
  NormalStep env ⟨0x00550513, by decide⟩ (states 5) (actions 5) (states 6) ∧
  NormalStep env ⟨0x00054503, by decide⟩ (states 6) (actions 6) (states 7) ∧
  NormalStep env ⟨0xfea43423, by decide⟩ (states 7) (actions 7) (states 8) ∧
  NormalStep env ⟨0xfe844503, by decide⟩ (states 8) (actions 8) (states 9) ∧
  NormalStep env ⟨0x01813083, by decide⟩ (states 9) (actions 9) (states 10) ∧
  NormalStep env ⟨0x01013403, by decide⟩ (states 10) (actions 10) (states 11) ∧
  NormalStep env ⟨0x02010113, by decide⟩ (states 11) (actions 11) (states 12)

def WritePrefix (offsetRaw : Raw) (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) : Prop :=
  NormalStep env ⟨0xfe010113, by decide⟩ (states 0) (actions 0) (states 1) ∧
  NormalStep env ⟨0x00113c23, by decide⟩ (states 1) (actions 1) (states 2) ∧
  NormalStep env ⟨0x00813823, by decide⟩ (states 2) (actions 2) (states 3) ∧
  NormalStep env ⟨0x02010413, by decide⟩ (states 3) (actions 3) (states 4) ∧
  NormalStep env ⟨0xfea407a3, by decide⟩ (states 4) (actions 4) (states 5) ∧
  NormalStep env ⟨0xfef44503, by decide⟩ (states 5) (actions 5) (states 6) ∧
  NormalStep env ⟨0x100005b7, by decide⟩ (states 6) (actions 6) (states 7) ∧
  NormalStep env offsetRaw (states 7) (actions 7) (states 8) ∧
  NormalStep env ⟨0x00a58023, by decide⟩ (states 8) (actions 8) (states 9) ∧
  NormalStep env ⟨0x00000513, by decide⟩ (states 9) (actions 9) (states 10) ∧
  NormalStep env ⟨0x01813083, by decide⟩ (states 10) (actions 10) (states 11) ∧
  NormalStep env ⟨0x01013403, by decide⟩ (states 11) (actions 11) (states 12) ∧
  NormalStep env ⟨0x02010113, by decide⟩ (states 12) (actions 12) (states 13)

def WriteZeroPrefix (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) : Prop :=
  NormalStep env ⟨0xfe010113, by decide⟩ (states 0) (actions 0) (states 1) ∧
  NormalStep env ⟨0x00113c23, by decide⟩ (states 1) (actions 1) (states 2) ∧
  NormalStep env ⟨0x00813823, by decide⟩ (states 2) (actions 2) (states 3) ∧
  NormalStep env ⟨0x02010413, by decide⟩ (states 3) (actions 3) (states 4) ∧
  NormalStep env ⟨0xfea407a3, by decide⟩ (states 4) (actions 4) (states 5) ∧
  NormalStep env ⟨0xfef44503, by decide⟩ (states 5) (actions 5) (states 6) ∧
  NormalStep env ⟨0x100005b7, by decide⟩ (states 6) (actions 6) (states 7) ∧
  NormalStep env ⟨0x00a58023, by decide⟩ (states 7) (actions 7) (states 8) ∧
  NormalStep env ⟨0x00000513, by decide⟩ (states 8) (actions 8) (states 9) ∧
  NormalStep env ⟨0x01813083, by decide⟩ (states 9) (actions 9) (states 10) ∧
  NormalStep env ⟨0x01013403, by decide⟩ (states 10) (actions 10) (states 11) ∧
  NormalStep env ⟨0x02010113, by decide⟩ (states 11) (actions 11) (states 12)

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

private theorem lui_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.lui destination immediate)) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      after.registers = writeW before.registers destination (wordInt immediate) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary
      exact ⟨rfl, rfl, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem store_class (ready : StoreReady env before location width value)
    (positive : 0 < width) : env.addressClass location = .ordinary := by
  have same : word location.val = location := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt location.isLt
  simpa only [Nat.add_zero, same] using ready.ordinary ⟨0, positive⟩

private theorem load_class (ready : LoadReady env before location width)
    (positive : 0 < width) : env.addressClass location = .ordinary := by
  have same : word location.val = location := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt location.isLt
  simpa only [Nat.add_zero, same] using ready.ordinary ⟨0, positive⟩

private theorem sd_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.sd source base offset)) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      after.registers = before.registers ∧
      ∃ ready : StoreReady env before (address before base offset) 8 (before.registers source),
        after.memory = storeLE before.memory (address before base offset) 8 ready.span
          (before.registers source) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | sd _ _ _ _ ready => exact ⟨rfl, rfl, rfl, ready, rfl⟩
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

private theorem sb_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.sb source base offset))
    (ordinaryClass : env.addressClass (address before base offset) = .ordinary) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      after.registers = before.registers ∧
      ∃ ready : StoreReady env before (address before base offset) 1 (before.registers source),
        after.memory = storeLE before.memory (address before base offset) 1 ready.span
          (before.registers source) := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | sb _ _ _ _ ready => exact ⟨rfl, rfl, rfl, ready, rfl⟩
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ _ actual kind _ _ =>
      have same := Option.some.inj (actual.symm.trans decoded)
      cases same
      cases ordinaryClass.symm.trans kind
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem lbu_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.lbu destination base offset))
    (ordinaryClass : env.addressClass (address before base offset) = .ordinary) :
    action = .silent ∧ after.pc = addW before.pc (word 4) ∧
      ∃ ready : LoadReady env before (address before base offset) 1,
        after.registers = writeW before.registers destination
          (unsignedLoad before.memory (address before base offset) 1 ready.span) ∧
        after.memory = before.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | lbu _ _ _ _ ready => exact ⟨rfl, rfl, ready, rfl, rfl⟩
  | read _ _ _ _ _ _ actual kind _ _ =>
      have same := Option.some.inj (actual.symm.trans decoded)
      cases same
      cases ordinaryClass.symm.trans kind
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem device_read_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.lbu destination base offset))
    (deviceClass : env.addressClass (address before base offset) = .device) :
    ∃ response : Byte, action = .read (address before base offset) response ∧
      after.pc = addW before.pc (word 4) ∧
      after.registers = writeW before.registers destination (word response.val) ∧
      FetchReady env raw before ∧ env.readable (address before base offset) 1 ∧
      env.deviceReadCompleted before (address before base offset) response after.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | lbu _ _ _ _ ready => cases (load_class ready (by decide)).symm.trans deviceClass
  | read _ _ _ response _ fetch actual _ permission completed =>
      have same := Option.some.inj (actual.symm.trans decoded)
      cases same
      exact ⟨response, rfl, rfl, rfl, fetch, permission, completed⟩
  | write _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem device_write_projection (step : NormalStep env raw before action after)
    (decoded : decode raw = some (.sb source base offset))
    (deviceClass : env.addressClass (address before base offset) = .device) :
    action = .write (address before base offset) (low8 (before.registers source)) ∧
      after.pc = addW before.pc (word 4) ∧ after.registers = before.registers ∧
      FetchReady env raw before ∧ env.writable (address before base offset) 1 ∧
      env.deviceWriteCompleted before (address before base offset)
        (low8 (before.registers source)) after.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary with
      | sb _ _ _ _ ready => cases (store_class ready (by decide)).symm.trans deviceClass
  | read _ _ _ _ _ _ actual _ _ _ => cases Option.some.inj (actual.symm.trans decoded)
  | write _ _ _ _ fetch actual _ permission completed =>
      have same := Option.some.inj (actual.symm.trans decoded)
      cases same
      exact ⟨rfl, rfl, rfl, fetch, permission, completed⟩
  | fence _ _ actual _ => cases Option.some.inj (actual.symm.trans decoded)

private theorem subtract_known (entry : Word) (amount : Nat) (depth : amount ≤ entry.val)
    (encoded : (wordInt (-(amount : Int))).val = modulus - amount) :
    addW entry (wordInt (-(amount : Int))) = word (entry.val - amount) := by
  apply Fin.ext
  change (entry.val + (wordInt (-(amount : Int))).val) % modulus = (entry.val - amount) % modulus
  rw [encoded]
  have rearrange : entry.val + (modulus - amount) = (entry.val - amount) + modulus := by
    have upper := entry.isLt
    omega
  rw [rearrange, Nat.add_mod_right]

private theorem sub_thirtytwo (entry : Word) (depth : 32 ≤ entry.val) :
    addW entry (wordInt (-32)) = word (entry.val - 32) :=
  subtract_known entry 32 depth (by decide)

private theorem sub_twentyfour (entry : Word) (depth : 32 ≤ entry.val) :
    addW entry (wordInt (-24)) = word (entry.val - 24) :=
  subtract_known entry 24 (by omega) (by decide)

private theorem sub_seventeen (entry : Word) (depth : 32 ≤ entry.val) :
    addW entry (wordInt (-17)) = word (entry.val - 17) :=
  subtract_known entry 17 (by omega) (by decide)

private theorem restore_thirtytwo (entry : Word) (depth : 32 ≤ entry.val) :
    addW (word (entry.val - 32)) (wordInt 32) = entry := by
  apply Fin.ext
  change ((entry.val - 32) % modulus + (wordInt 32).val) % modulus = entry.val
  have small : entry.val - 32 < modulus := by have bound := entry.isLt; omega
  have positive : (wordInt 32).val = 32 := by decide
  rw [Nat.mod_eq_of_lt small, positive, Nat.sub_add_cancel depth,
    Nat.mod_eq_of_lt entry.isLt]

private theorem stack_slot (entry : Word) (depth : 32 ≤ entry.val)
    (offset : Nat) (bounded : offset ≤ 32) :
    addW (word (entry.val - 32)) (word offset) = word (entry.val - (32 - offset)) := by
  apply Fin.ext
  change ((entry.val - 32) % modulus + offset % modulus) % modulus =
    (entry.val - (32 - offset)) % modulus
  have small : entry.val - 32 < modulus := by have upper := entry.isLt; omega
  have offsetSmall : offset < modulus := by
    have large : 32 < modulus := by decide
    omega
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt offsetSmall]
  congr 1
  omega

private theorem slot_twentyfour (entry : Word) (depth : 32 ≤ entry.val) :
    addW (word (entry.val - 32)) (wordInt 24) = word (entry.val - 8) := by
  have encoding : wordInt 24 = word 24 := by decide
  rw [encoding]
  exact stack_slot entry depth 24 (by decide)

private theorem slot_sixteen (entry : Word) (depth : 32 ≤ entry.val) :
    addW (word (entry.val - 32)) (wordInt 16) = word (entry.val - 16) := by
  have encoding : wordInt 16 = word 16 := by decide
  rw [encoding]
  exact stack_slot entry depth 16 (by decide)

private theorem add_words (left right : Nat) :
    addW (word left) (word right) = word (left + right) := by
  apply Fin.ext
  exact (Nat.add_mod left right modulus).symm

private theorem uart_offset (offset : Nat) (lower : 1 ≤ offset) (upper : offset ≤ 4) :
    addW (wordInt 268435456) (wordInt (offset : Int)) = word (0x10000000 + offset) := by
  have choices : offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 := by omega
  rcases choices with rfl | rfl | rfl | rfl <;> decide

private theorem byte_word (value : Byte) : low8 (word value.val) = value := by
  apply Fin.ext
  rw [low8_word, Nat.mod_eq_of_lt value.isLt]

private theorem reload_same_address (memory : Memory) (storeLocation loadLocation : Word)
    (storeWidth loadWidth : Nat) (storeSpan : storeLocation.val + storeWidth ≤ modulus)
    (loadSpan : loadLocation.val + loadWidth ≤ modulus)
    (storeSupported : SupportedWidth storeWidth) (loadSupported : SupportedWidth loadWidth)
    (sameLocation : loadLocation = storeLocation) (value : Word) :
    low8 (unsignedLoad (storeLE memory storeLocation storeWidth storeSpan value)
      loadLocation loadWidth loadSpan) = low8 value := by
  subst loadLocation
  exact unsignedLoad_after_store memory storeLocation storeWidth loadWidth storeSpan loadSpan
    storeSupported loadSupported value

def FrameBounds32 (entry : Word) : Prop :=
  ∀ offset width : Nat, (offset, width) ∈ [(8, 8), (16, 8), (24, 8), (17, 1)] →
    (word (entry.val - offset)).val = entry.val - offset ∧
    entry.val - 32 ≤ (word (entry.val - offset)).val ∧
    (word (entry.val - offset)).val + width ≤ entry.val ∧
    (word (entry.val - offset)).val + width ≤ modulus ∧
    (word (entry.val - offset)).val % width = 0

private theorem frame_bounds (entry : Word) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0) : FrameBounds32 entry := by
  intro offset width member
  have value (n : Nat) : (word (entry.val - n)).val = entry.val - n :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) entry.isLt)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rw [value]
  all_goals have upper := entry.isLt
  all_goals omega

def ReadConclusion (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) (entry : Word) : Prop :=
  ∃ response : Byte,
    low8 ((states 12).registers a0) = response ∧ (states 12).registers spReg = entry ∧
    [actions 0, actions 1, actions 2, actions 3, actions 4, actions 5, actions 6, actions 7, actions 8, actions 9, actions 10, actions 11] =
      [.silent, .silent, .silent, .silent, .silent, .silent, .read (word 0x10000005) response, .silent, .silent, .silent, .silent, .silent] ∧
    [(states 0).pc, (states 1).pc, (states 2).pc, (states 3).pc, (states 4).pc, (states 5).pc, (states 6).pc, (states 7).pc, (states 8).pc, (states 9).pc, (states 10).pc, (states 11).pc, (states 12).pc] =
      [word 0x80200350, word 0x80200354, word 0x80200358, word 0x8020035c, word 0x80200360, word 0x80200364, word 0x80200368, word 0x8020036c, word 0x80200370, word 0x80200374, word 0x80200378, word 0x8020037c, word 0x80200380] ∧
    (states 12).pc.val = 0x80200380 ∧ FrameBounds32 entry ∧
    address (states 6) a0 0 = word 0x10000005 ∧
    FetchReady env ⟨0x00054503, by decide⟩ (states 6) ∧
    env.readable (word 0x10000005) 1 ∧
    env.deviceReadCompleted (states 6) (word 0x10000005) response (states 7).memory ∧
    address (states 1) spReg 24 = word (entry.val - 8) ∧
    StoreReady env (states 1) (word (entry.val - 8)) 8 ((states 1).registers raReg) ∧
    address (states 2) spReg 16 = word (entry.val - 16) ∧
    StoreReady env (states 2) (word (entry.val - 16)) 8 ((states 2).registers fp) ∧
    address (states 7) fp (-24) = word (entry.val - 24) ∧
    StoreReady env (states 7) (word (entry.val - 24)) 8 ((states 7).registers a0) ∧
    address (states 8) fp (-24) = word (entry.val - 24) ∧
    LoadReady env (states 8) (word (entry.val - 24)) 1 ∧
    address (states 9) spReg 24 = word (entry.val - 8) ∧
    LoadReady env (states 9) (word (entry.val - 8)) 8 ∧
    address (states 10) spReg 16 = word (entry.val - 16) ∧
    LoadReady env (states 10) (word (entry.val - 16)) 8

def WriteConclusion (pcStart offset : Nat) (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) (entry : Word) : Prop :=
  (states 13).registers a0 = word 0 ∧ (states 13).registers spReg = entry ∧
    [actions 0, actions 1, actions 2, actions 3, actions 4, actions 5, actions 6, actions 7, actions 8, actions 9, actions 10, actions 11, actions 12] =
      [.silent, .silent, .silent, .silent, .silent, .silent, .silent, .silent, .write (word (0x10000000 + offset)) (low8 ((states 0).registers a0)), .silent, .silent, .silent, .silent] ∧
    [(states 0).pc, (states 1).pc, (states 2).pc, (states 3).pc, (states 4).pc, (states 5).pc, (states 6).pc, (states 7).pc, (states 8).pc, (states 9).pc, (states 10).pc, (states 11).pc, (states 12).pc, (states 13).pc] =
      [word (pcStart + 0), word (pcStart + 4), word (pcStart + 8), word (pcStart + 12), word (pcStart + 16), word (pcStart + 20), word (pcStart + 24), word (pcStart + 28), word (pcStart + 32), word (pcStart + 36), word (pcStart + 40), word (pcStart + 44), word (pcStart + 48), word (pcStart + 52)] ∧
    (states 13).pc.val = pcStart + 52 ∧ FrameBounds32 entry ∧
    address (states 8) a1 0 = word (0x10000000 + offset) ∧
    FetchReady env ⟨0x00a58023, by decide⟩ (states 8) ∧
    env.writable (word (0x10000000 + offset)) 1 ∧
    env.deviceWriteCompleted (states 8) (word (0x10000000 + offset)) (low8 ((states 0).registers a0)) (states 9).memory ∧
    address (states 1) spReg 24 = word (entry.val - 8) ∧
    StoreReady env (states 1) (word (entry.val - 8)) 8 ((states 1).registers raReg) ∧
    address (states 2) spReg 16 = word (entry.val - 16) ∧
    StoreReady env (states 2) (word (entry.val - 16)) 8 ((states 2).registers fp) ∧
    address (states 4) fp (-17) = word (entry.val - 17) ∧
    StoreReady env (states 4) (word (entry.val - 17)) 1 ((states 4).registers a0) ∧
    address (states 5) fp (-17) = word (entry.val - 17) ∧
    LoadReady env (states 5) (word (entry.val - 17)) 1 ∧
    address (states 10) spReg 24 = word (entry.val - 8) ∧
    LoadReady env (states 10) (word (entry.val - 8)) 8 ∧
    address (states 11) spReg 16 = word (entry.val - 16) ∧
    LoadReady env (states 11) (word (entry.val - 16)) 8

def WriteZeroConclusion (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) (entry : Word) : Prop :=
  (states 12).registers a0 = word 0 ∧ (states 12).registers spReg = entry ∧
    [actions 0, actions 1, actions 2, actions 3, actions 4, actions 5, actions 6, actions 7, actions 8, actions 9, actions 10, actions 11] =
      [.silent, .silent, .silent, .silent, .silent, .silent, .silent, .write (word 0x10000000) (low8 ((states 0).registers a0)), .silent, .silent, .silent, .silent] ∧
    [(states 0).pc, (states 1).pc, (states 2).pc, (states 3).pc, (states 4).pc, (states 5).pc, (states 6).pc, (states 7).pc, (states 8).pc, (states 9).pc, (states 10).pc, (states 11).pc, (states 12).pc] =
      [word 0x8020049c, word 0x802004a0, word 0x802004a4, word 0x802004a8, word 0x802004ac, word 0x802004b0, word 0x802004b4, word 0x802004b8, word 0x802004bc, word 0x802004c0, word 0x802004c4, word 0x802004c8, word 0x802004cc] ∧
    (states 12).pc.val = 0x802004cc ∧ FrameBounds32 entry ∧
    address (states 7) a1 0 = word 0x10000000 ∧
    FetchReady env ⟨0x00a58023, by decide⟩ (states 7) ∧
    env.writable (word 0x10000000) 1 ∧
    env.deviceWriteCompleted (states 7) (word 0x10000000) (low8 ((states 0).registers a0)) (states 8).memory ∧
    address (states 1) spReg 24 = word (entry.val - 8) ∧
    StoreReady env (states 1) (word (entry.val - 8)) 8 ((states 1).registers raReg) ∧
    address (states 2) spReg 16 = word (entry.val - 16) ∧
    StoreReady env (states 2) (word (entry.val - 16)) 8 ((states 2).registers fp) ∧
    address (states 4) fp (-17) = word (entry.val - 17) ∧
    StoreReady env (states 4) (word (entry.val - 17)) 1 ((states 4).registers a0) ∧
    address (states 5) fp (-17) = word (entry.val - 17) ∧
    LoadReady env (states 5) (word (entry.val - 17)) 1 ∧
    address (states 9) spReg 24 = word (entry.val - 8) ∧
    LoadReady env (states 9) (word (entry.val - 8)) 8 ∧
    address (states 10) spReg 16 = word (entry.val - 16) ∧
    LoadReady env (states 10) (word (entry.val - 16)) 8

private theorem read_projection (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) (entry : Word) (trace : ReadPrefix env states actions)
    (entryPC : (states 0).pc = word 0x80200350)
    (_zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (device : env.addressClass (word 0x10000005) = .device) :
    ReadConclusion env states actions entry := by
  rcases trace with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨act0, p1, r1⟩ := addi_projection h0 decode_word_212
  obtain ⟨act1, p2, r2, storeRa, m2⟩ := sd_projection h1 decode_word_213
  obtain ⟨act2, p3, r3, storeFp, m3⟩ := sd_projection h2 decode_word_214
  obtain ⟨act3, p4, r4⟩ := addi_projection h3 decode_word_215
  obtain ⟨act4, p5, r5⟩ := lui_projection h4 decode_word_216
  obtain ⟨act5, p6, r6⟩ := addi_projection h5 decode_word_217
  have sp1 : (states 1).registers spReg = word (entry.val - 32) := by
    rw [r1]
    change addW ((states 0).registers spReg) (wordInt (-32)) = word (entry.val - 32)
    rw [stack, sub_thirtytwo entry depth]
  have sp2 : (states 2).registers spReg = word (entry.val - 32) := by
    rw [r2]
    change (states 1).registers spReg = word (entry.val - 32)
    exact sp1
  have sp3 : (states 3).registers spReg = word (entry.val - 32) := by
    rw [r3]
    change (states 2).registers spReg = word (entry.val - 32)
    exact sp2
  have sp4 : (states 4).registers spReg = word (entry.val - 32) := by
    rw [r4]
    change (states 3).registers spReg = word (entry.val - 32)
    exact sp3
  have sp5 : (states 5).registers spReg = word (entry.val - 32) := by
    rw [r5]
    change (states 4).registers spReg = word (entry.val - 32)
    exact sp4
  have sp6 : (states 6).registers spReg = word (entry.val - 32) := by
    rw [r6]
    change (states 5).registers spReg = word (entry.val - 32)
    exact sp5
  have fp4 : (states 4).registers fp = entry := by
    rw [r4]
    change addW ((states 3).registers spReg) (wordInt 32) = entry
    rw [sp3, restore_thirtytwo entry depth]
  have fp5 : (states 5).registers fp = entry := by
    rw [r5]
    change (states 4).registers fp = entry
    exact fp4
  have fp6 : (states 6).registers fp = entry := by
    rw [r6]
    change (states 5).registers fp = entry
    exact fp5
  have arg5 : (states 5).registers a0 = wordInt 268435456 := by rw [r5]; rfl
  have arg6 : (states 6).registers a0 = word 0x10000005 := by
    rw [r6]
    change addW ((states 5).registers a0) (wordInt 5) = word 0x10000005
    rw [arg5]
    decide
  have ioEA : address (states 6) a0 0 = word 0x10000005 := by
    unfold address
    rw [arg6, wordInt_zero, addW_zero]
  obtain ⟨response, act6, p7, r7, fetch, permission, completed⟩ :=
    device_read_projection h6 decode_word_218 (by change env.addressClass (address (states 6) a0 0) = .device; rw [ioEA]; exact device)
  have sp7 : (states 7).registers spReg = word (entry.val - 32) := by
    rw [r7]
    change (states 6).registers spReg = word (entry.val - 32)
    exact sp6
  have fp7 : (states 7).registers fp = entry := by
    rw [r7]
    change (states 6).registers fp = entry
    exact fp6
  have response7 : (states 7).registers a0 = word response.val := by rw [r7]; rfl
  obtain ⟨act7, p8, r8, storeSpill, m8⟩ := sd_projection h7 decode_word_219
  have sp8 : (states 8).registers spReg = word (entry.val - 32) := by
    rw [r8]
    change (states 7).registers spReg = word (entry.val - 32)
    exact sp7
  have fp8 : (states 8).registers fp = entry := by
    rw [r8]
    change (states 7).registers fp = entry
    exact fp7
  have ea7 : address (states 7) fp (-24) = word (entry.val - 24) := by
    unfold address
    rw [fp7, sub_twentyfour entry depth]
  have ea8 : address (states 8) fp (-24) = word (entry.val - 24) := by
    unfold address
    rw [fp8, sub_twentyfour entry depth]
  have ordinary8 : env.addressClass (address (states 8) fp (-24)) = .ordinary := by
    rw [ea8, ← ea7]
    exact store_class storeSpill (by decide)
  obtain ⟨act8, p9, loadSpill, r9, m9⟩ := lbu_projection h8 decode_word_220 ordinary8
  obtain ⟨act9, p10, loadRa, r10⟩ := ld_projection h9 decode_word_221
  obtain ⟨act10, p11, loadFp, r11⟩ := ld_projection h10 decode_word_222
  obtain ⟨act11, p12, r12⟩ := addi_projection h11 decode_word_223
  have sp9 : (states 9).registers spReg = word (entry.val - 32) := by
    rw [r9]
    change (states 8).registers spReg = word (entry.val - 32)
    exact sp8
  have sp10 : (states 10).registers spReg = word (entry.val - 32) := by
    rw [r10]
    change (states 9).registers spReg = word (entry.val - 32)
    exact sp9
  have sp11 : (states 11).registers spReg = word (entry.val - 32) := by
    rw [r11]
    change (states 10).registers spReg = word (entry.val - 32)
    exact sp10
  have sp12 : (states 12).registers spReg = entry := by
    rw [r12]
    change addW ((states 11).registers spReg) (wordInt 32) = entry
    rw [sp11, restore_thirtytwo entry depth]
  have reload : low8 ((states 9).registers a0) = low8 ((states 7).registers a0) := by
    rw [r9]
    change low8 (unsignedLoad (states 8).memory (address (states 8) fp (-24)) 1 loadSpill.span) = _
    rw [m8]
    change low8 (unsignedLoad
      (storeLE (states 7).memory (address (states 7) fp (-24)) 8 storeSpill.span
        ((states 7).registers a0)) (address (states 8) fp (-24)) 1 loadSpill.span) = _
    exact reload_same_address (states 7).memory (address (states 7) fp (-24))
      (address (states 8) fp (-24)) 8 1 storeSpill.span loadSpill.span
      (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (ea8.trans ea7.symm)
      ((states 7).registers a0)
  have result9 : low8 ((states 9).registers a0) = response := by rw [reload, response7, byte_word]
  have result10 : low8 ((states 10).registers a0) = response := by
    rw [r10]
    change low8 ((states 9).registers a0) = response
    exact result9
  have result11 : low8 ((states 11).registers a0) = response := by
    rw [r11]
    change low8 ((states 10).registers a0) = response
    exact result10
  have result12 : low8 ((states 12).registers a0) = response := by
    rw [r12]
    change low8 ((states 11).registers a0) = response
    exact result11
  have pc1 : (states 1).pc = word 0x80200354 := by
    rw [p1, entryPC] <;> decide
  have pc2 : (states 2).pc = word 0x80200358 := by
    rw [p2, pc1] <;> decide
  have pc3 : (states 3).pc = word 0x8020035c := by
    rw [p3, pc2] <;> decide
  have pc4 : (states 4).pc = word 0x80200360 := by
    rw [p4, pc3] <;> decide
  have pc5 : (states 5).pc = word 0x80200364 := by
    rw [p5, pc4] <;> decide
  have pc6 : (states 6).pc = word 0x80200368 := by
    rw [p6, pc5] <;> decide
  have pc7 : (states 7).pc = word 0x8020036c := by
    rw [p7, pc6] <;> decide
  have pc8 : (states 8).pc = word 0x80200370 := by
    rw [p8, pc7] <;> decide
  have pc9 : (states 9).pc = word 0x80200374 := by
    rw [p9, pc8] <;> decide
  have pc10 : (states 10).pc = word 0x80200378 := by
    rw [p10, pc9] <;> decide
  have pc11 : (states 11).pc = word 0x8020037c := by
    rw [p11, pc10] <;> decide
  have pc12 : (states 12).pc = word 0x80200380 := by
    rw [p12, pc11] <;> decide
  have ea1 : address (states 1) spReg 24 = word (entry.val - 8) := by
    unfold address
    rw [sp1, slot_twentyfour entry depth]
  have ea2 : address (states 2) spReg 16 = word (entry.val - 16) := by
    unfold address
    rw [sp2, slot_sixteen entry depth]
  have ea9 : address (states 9) spReg 24 = word (entry.val - 8) := by
    unfold address
    rw [sp9, slot_twentyfour entry depth]
  have ea10 : address (states 10) spReg 16 = word (entry.val - 16) := by
    unfold address
    rw [sp10, slot_sixteen entry depth]
  refine ⟨response, result12, sp12, ?_, ?_, ?_, frame_bounds entry depth aligned, ioEA, fetch,
    ?_, ?_, ea1, ?_, ea2, ?_, ea7, ?_, ea8, ?_, ea9, ?_, ea10, ?_⟩
  · rw [act0, act1, act2, act3, act4, act5, act6, act7, act8, act9, act10, act11, ioEA]
  · rw [entryPC, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12]
  · rw [pc12]; decide
  · simpa only [ioEA] using permission
  · simpa only [ioEA] using completed
  · rw [← ea1]
    exact storeRa
  · rw [← ea2]
    exact storeFp
  · rw [← ea7]
    exact storeSpill
  · rw [← ea8]
    exact loadSpill
  · rw [← ea9]
    exact loadRa
  · rw [← ea10]
    exact loadFp

private theorem write_projection (offsetRaw : Raw) (offset pcStart : Nat) (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) (entry : Word)
    (trace : WritePrefix offsetRaw env states actions)
    (entryPC : (states 0).pc = word pcStart)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word (0x10000000 + offset)) = .device)
    (lower : 1 ≤ offset) (upper : offset ≤ 4) (codeSpan : pcStart + 52 < modulus)
    (offsetDecoded : decode offsetRaw = some (.addi a1 a1 (offset : Int))) :
    WriteConclusion pcStart offset env states actions entry := by
  rcases trace with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  obtain ⟨act0, p1, r1⟩ := addi_projection h0 decode_word_239
  obtain ⟨act1, p2, r2, storeRa, m2⟩ := sd_projection h1 decode_word_240
  obtain ⟨act2, p3, r3, storeFp, m3⟩ := sd_projection h2 decode_word_241
  obtain ⟨act3, p4, r4⟩ := addi_projection h3 decode_word_242
  have sp1 : (states 1).registers spReg = word (entry.val - 32) := by
    rw [r1]
    change addW ((states 0).registers spReg) (wordInt (-32)) = word (entry.val - 32)
    rw [stack, sub_thirtytwo entry depth]
  have sp2 : (states 2).registers spReg = word (entry.val - 32) := by
    rw [r2]
    change (states 1).registers spReg = word (entry.val - 32)
    exact sp1
  have sp3 : (states 3).registers spReg = word (entry.val - 32) := by
    rw [r3]
    change (states 2).registers spReg = word (entry.val - 32)
    exact sp2
  have sp4 : (states 4).registers spReg = word (entry.val - 32) := by
    rw [r4]
    change (states 3).registers spReg = word (entry.val - 32)
    exact sp3
  have fp4 : (states 4).registers fp = entry := by
    rw [r4]
    change addW ((states 3).registers spReg) (wordInt 32) = entry
    rw [sp3, restore_thirtytwo entry depth]
  have ea4 : address (states 4) fp (-17) = word (entry.val - 17) := by
    unfold address
    rw [fp4, sub_seventeen entry depth]
  have arg4 : (states 4).registers a0 = (states 0).registers a0 := by
    rw [r4, r3, r2, r1]
    rfl
  obtain ⟨act4, p5, r5, storeSpill, m5⟩ := sb_projection h4 decode_word_243
    (by change env.addressClass (address (states 4) fp (-17)) = .ordinary; rw [ea4]; exact ordinary)
  have sp5 : (states 5).registers spReg = word (entry.val - 32) := by
    rw [r5]
    change (states 4).registers spReg = word (entry.val - 32)
    exact sp4
  have fp5 : (states 5).registers fp = entry := by
    rw [r5]
    change (states 4).registers fp = entry
    exact fp4
  have ea5 : address (states 5) fp (-17) = word (entry.val - 17) := by
    unfold address
    rw [fp5, sub_seventeen entry depth]
  obtain ⟨act5, p6, loadSpill, r6, m6⟩ := lbu_projection h5 decode_word_244
    (by change env.addressClass (address (states 5) fp (-17)) = .ordinary; rw [ea5]; exact ordinary)
  have sp6 : (states 6).registers spReg = word (entry.val - 32) := by
    rw [r6]
    change (states 5).registers spReg = word (entry.val - 32)
    exact sp5
  have reload : low8 ((states 6).registers a0) = low8 ((states 4).registers a0) := by
    rw [r6]
    change low8 (unsignedLoad (states 5).memory (address (states 5) fp (-17)) 1 loadSpill.span) = _
    rw [m5]
    change low8 (unsignedLoad
      (storeLE (states 4).memory (address (states 4) fp (-17)) 1 storeSpill.span
        ((states 4).registers a0)) (address (states 5) fp (-17)) 1 loadSpill.span) = _
    exact reload_same_address (states 4).memory (address (states 4) fp (-17))
      (address (states 5) fp (-17)) 1 1 storeSpill.span loadSpill.span
      (Or.inl rfl) (Or.inl rfl) (ea5.trans ea4.symm) ((states 4).registers a0)
  have payload6 : low8 ((states 6).registers a0) = low8 ((states 0).registers a0) := by rw [reload, arg4]
  obtain ⟨act6, p7, r7⟩ := lui_projection h6 decode_word_245
  have sp7 : (states 7).registers spReg = word (entry.val - 32) := by
    rw [r7]
    change (states 6).registers spReg = word (entry.val - 32)
    exact sp6
  have payload7 : low8 ((states 7).registers a0) = low8 ((states 0).registers a0) := by
    rw [r7]
    change low8 ((states 6).registers a0) = _
    exact payload6
  have port7 : (states 7).registers a1 = wordInt 268435456 := by rw [r7]; rfl
  obtain ⟨act7, p8, r8⟩ := addi_projection h7 offsetDecoded
  have sp8 : (states 8).registers spReg = word (entry.val - 32) := by
    rw [r8]
    change (states 7).registers spReg = word (entry.val - 32)
    exact sp7
  have payload8 : low8 ((states 8).registers a0) = low8 ((states 0).registers a0) := by
    rw [r8]
    change low8 ((states 7).registers a0) = _
    exact payload7
  have port8 : (states 8).registers a1 = word (0x10000000 + offset) := by
    rw [r8]
    change addW ((states 7).registers a1) (wordInt (offset : Int)) = _
    rw [port7, uart_offset offset lower upper]
  have ioEA : address (states 8) a1 0 = word (0x10000000 + offset) := by
    unfold address
    rw [port8, wordInt_zero, addW_zero]
  obtain ⟨act8, p9, r9, fetch, permission, completed⟩ :=
    device_write_projection h8 decode_word_247 (by change env.addressClass (address (states 8) a1 0) = .device; rw [ioEA]; exact device)
  have sp9 : (states 9).registers spReg = word (entry.val - 32) := by
    rw [r9]
    change (states 8).registers spReg = word (entry.val - 32)
    exact sp8
  obtain ⟨act9, p10, r10⟩ := addi_projection h9 decode_word_248
  have sp10 : (states 10).registers spReg = word (entry.val - 32) := by
    rw [r10]
    change (states 9).registers spReg = word (entry.val - 32)
    exact sp9
  have zero9 : (states 9).registers zeroReg = word 0 := by
    rw [r9, r8, r7, r6, r5, r4, r3, r2, r1]
    simp only [writeW_at_zero]
    exact zero
  have result10 : (states 10).registers a0 = word 0 := by
    rw [r10]
    change addW ((states 9).registers zeroReg) (wordInt 0) = word 0
    rw [zero9, wordInt_zero, addW_zero]
  obtain ⟨act10, p11, loadRa, r11⟩ := ld_projection h10 decode_word_249
  obtain ⟨act11, p12, loadFp, r12⟩ := ld_projection h11 decode_word_250
  obtain ⟨act12, p13, r13⟩ := addi_projection h12 decode_word_251
  have sp11 : (states 11).registers spReg = word (entry.val - 32) := by
    rw [r11]
    change (states 10).registers spReg = word (entry.val - 32)
    exact sp10
  have result11 : (states 11).registers a0 = word 0 := by
    rw [r11]
    change (states 10).registers a0 = word 0
    exact result10
  have sp12 : (states 12).registers spReg = word (entry.val - 32) := by
    rw [r12]
    change (states 11).registers spReg = word (entry.val - 32)
    exact sp11
  have result12 : (states 12).registers a0 = word 0 := by
    rw [r12]
    change (states 11).registers a0 = word 0
    exact result11
  have sp13 : (states 13).registers spReg = entry := by
    rw [r13]
    change addW ((states 12).registers spReg) (wordInt 32) = entry
    rw [sp12, restore_thirtytwo entry depth]
  have result13 : (states 13).registers a0 = word 0 := by
    rw [r13]
    change (states 12).registers a0 = word 0
    exact result12
  have pc1 : (states 1).pc = word (pcStart + 4) := by
    rw [p1, entryPC, add_words]
  have pc2 : (states 2).pc = word (pcStart + 8) := by
    rw [p2, pc1, add_words]
  have pc3 : (states 3).pc = word (pcStart + 12) := by
    rw [p3, pc2, add_words]
  have pc4 : (states 4).pc = word (pcStart + 16) := by
    rw [p4, pc3, add_words]
  have pc5 : (states 5).pc = word (pcStart + 20) := by
    rw [p5, pc4, add_words]
  have pc6 : (states 6).pc = word (pcStart + 24) := by
    rw [p6, pc5, add_words]
  have pc7 : (states 7).pc = word (pcStart + 28) := by
    rw [p7, pc6, add_words]
  have pc8 : (states 8).pc = word (pcStart + 32) := by
    rw [p8, pc7, add_words]
  have pc9 : (states 9).pc = word (pcStart + 36) := by
    rw [p9, pc8, add_words]
  have pc10 : (states 10).pc = word (pcStart + 40) := by
    rw [p10, pc9, add_words]
  have pc11 : (states 11).pc = word (pcStart + 44) := by
    rw [p11, pc10, add_words]
  have pc12 : (states 12).pc = word (pcStart + 48) := by
    rw [p12, pc11, add_words]
  have pc13 : (states 13).pc = word (pcStart + 52) := by
    rw [p13, pc12, add_words]
  have ea1 : address (states 1) spReg 24 = word (entry.val - 8) := by
    unfold address
    rw [sp1, slot_twentyfour entry depth]
  have ea2 : address (states 2) spReg 16 = word (entry.val - 16) := by
    unfold address
    rw [sp2, slot_sixteen entry depth]
  have ea10 : address (states 10) spReg 24 = word (entry.val - 8) := by
    unfold address
    rw [sp10, slot_twentyfour entry depth]
  have ea11 : address (states 11) spReg 16 = word (entry.val - 16) := by
    unfold address
    rw [sp11, slot_sixteen entry depth]
  refine ⟨result13, sp13, ?_, ?_, ?_, frame_bounds entry depth aligned, ioEA, fetch,
    ?_, ?_, ea1, ?_, ea2, ?_, ea4, ?_, ea5, ?_, ea10, ?_, ea11, ?_⟩
  · rw [act0, act1, act2, act3, act4, act5, act6, act7, act8, act9, act10, act11, act12, ioEA, payload8]
  · rw [entryPC, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12, pc13]
    simp only [Nat.add_zero]
  · rw [pc13]
    exact Nat.mod_eq_of_lt codeSpan
  · simpa only [ioEA] using permission
  · simpa only [ioEA, payload8] using completed
  · rw [← ea1]
    exact storeRa
  · rw [← ea2]
    exact storeFp
  · rw [← ea4]
    exact storeSpill
  · rw [← ea5]
    exact loadSpill
  · rw [← ea10]
    exact loadRa
  · rw [← ea11]
    exact loadFp

private theorem write_zero_projection (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) (entry : Word)
    (trace : WriteZeroPrefix env states actions)
    (entryPC : (states 0).pc = word 0x8020049c)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word 0x10000000) = .device)
    :
    WriteZeroConclusion env states actions entry := by
  rcases trace with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨act0, p1, r1⟩ := addi_projection h0 decode_word_295
  obtain ⟨act1, p2, r2, storeRa, m2⟩ := sd_projection h1 decode_word_296
  obtain ⟨act2, p3, r3, storeFp, m3⟩ := sd_projection h2 decode_word_297
  obtain ⟨act3, p4, r4⟩ := addi_projection h3 decode_word_298
  have sp1 : (states 1).registers spReg = word (entry.val - 32) := by
    rw [r1]
    change addW ((states 0).registers spReg) (wordInt (-32)) = word (entry.val - 32)
    rw [stack, sub_thirtytwo entry depth]
  have sp2 : (states 2).registers spReg = word (entry.val - 32) := by
    rw [r2]
    change (states 1).registers spReg = word (entry.val - 32)
    exact sp1
  have sp3 : (states 3).registers spReg = word (entry.val - 32) := by
    rw [r3]
    change (states 2).registers spReg = word (entry.val - 32)
    exact sp2
  have sp4 : (states 4).registers spReg = word (entry.val - 32) := by
    rw [r4]
    change (states 3).registers spReg = word (entry.val - 32)
    exact sp3
  have fp4 : (states 4).registers fp = entry := by
    rw [r4]
    change addW ((states 3).registers spReg) (wordInt 32) = entry
    rw [sp3, restore_thirtytwo entry depth]
  have ea4 : address (states 4) fp (-17) = word (entry.val - 17) := by
    unfold address
    rw [fp4, sub_seventeen entry depth]
  have arg4 : (states 4).registers a0 = (states 0).registers a0 := by
    rw [r4, r3, r2, r1]
    rfl
  obtain ⟨act4, p5, r5, storeSpill, m5⟩ := sb_projection h4 decode_word_299
    (by change env.addressClass (address (states 4) fp (-17)) = .ordinary; rw [ea4]; exact ordinary)
  have sp5 : (states 5).registers spReg = word (entry.val - 32) := by
    rw [r5]
    change (states 4).registers spReg = word (entry.val - 32)
    exact sp4
  have fp5 : (states 5).registers fp = entry := by
    rw [r5]
    change (states 4).registers fp = entry
    exact fp4
  have ea5 : address (states 5) fp (-17) = word (entry.val - 17) := by
    unfold address
    rw [fp5, sub_seventeen entry depth]
  obtain ⟨act5, p6, loadSpill, r6, m6⟩ := lbu_projection h5 decode_word_300
    (by change env.addressClass (address (states 5) fp (-17)) = .ordinary; rw [ea5]; exact ordinary)
  have sp6 : (states 6).registers spReg = word (entry.val - 32) := by
    rw [r6]
    change (states 5).registers spReg = word (entry.val - 32)
    exact sp5
  have reload : low8 ((states 6).registers a0) = low8 ((states 4).registers a0) := by
    rw [r6]
    change low8 (unsignedLoad (states 5).memory (address (states 5) fp (-17)) 1 loadSpill.span) = _
    rw [m5]
    change low8 (unsignedLoad
      (storeLE (states 4).memory (address (states 4) fp (-17)) 1 storeSpill.span
        ((states 4).registers a0)) (address (states 5) fp (-17)) 1 loadSpill.span) = _
    exact reload_same_address (states 4).memory (address (states 4) fp (-17))
      (address (states 5) fp (-17)) 1 1 storeSpill.span loadSpill.span
      (Or.inl rfl) (Or.inl rfl) (ea5.trans ea4.symm) ((states 4).registers a0)
  have payload6 : low8 ((states 6).registers a0) = low8 ((states 0).registers a0) := by rw [reload, arg4]
  obtain ⟨act6, p7, r7⟩ := lui_projection h6 decode_word_301
  have sp7 : (states 7).registers spReg = word (entry.val - 32) := by
    rw [r7]
    change (states 6).registers spReg = word (entry.val - 32)
    exact sp6
  have payload7 : low8 ((states 7).registers a0) = low8 ((states 0).registers a0) := by
    rw [r7]
    change low8 ((states 6).registers a0) = _
    exact payload6
  have port7 : (states 7).registers a1 = wordInt 268435456 := by rw [r7]; rfl
  have ioEA : address (states 7) a1 0 = word 0x10000000 := by
    unfold address
    rw [port7, wordInt_zero, addW_zero]
    decide
  obtain ⟨act7, p8, r8, fetch, permission, completed⟩ :=
    device_write_projection h7 decode_word_302 (by change env.addressClass (address (states 7) a1 0) = .device; rw [ioEA]; exact device)
  have sp8 : (states 8).registers spReg = word (entry.val - 32) := by
    rw [r8]
    change (states 7).registers spReg = word (entry.val - 32)
    exact sp7
  obtain ⟨act8, p9, r9⟩ := addi_projection h8 decode_word_303
  have sp9 : (states 9).registers spReg = word (entry.val - 32) := by
    rw [r9]
    change (states 8).registers spReg = word (entry.val - 32)
    exact sp8
  have zero8 : (states 8).registers zeroReg = word 0 := by
    rw [r8, r7, r6, r5, r4, r3, r2, r1]
    simp only [writeW_at_zero]
    exact zero
  have result9 : (states 9).registers a0 = word 0 := by
    rw [r9]
    change addW ((states 8).registers zeroReg) (wordInt 0) = word 0
    rw [zero8, wordInt_zero, addW_zero]
  obtain ⟨act9, p10, loadRa, r10⟩ := ld_projection h9 decode_word_304
  obtain ⟨act10, p11, loadFp, r11⟩ := ld_projection h10 decode_word_305
  obtain ⟨act11, p12, r12⟩ := addi_projection h11 decode_word_306
  have sp10 : (states 10).registers spReg = word (entry.val - 32) := by
    rw [r10]
    change (states 9).registers spReg = word (entry.val - 32)
    exact sp9
  have result10 : (states 10).registers a0 = word 0 := by
    rw [r10]
    change (states 9).registers a0 = word 0
    exact result9
  have sp11 : (states 11).registers spReg = word (entry.val - 32) := by
    rw [r11]
    change (states 10).registers spReg = word (entry.val - 32)
    exact sp10
  have result11 : (states 11).registers a0 = word 0 := by
    rw [r11]
    change (states 10).registers a0 = word 0
    exact result10
  have sp12 : (states 12).registers spReg = entry := by
    rw [r12]
    change addW ((states 11).registers spReg) (wordInt 32) = entry
    rw [sp11, restore_thirtytwo entry depth]
  have result12 : (states 12).registers a0 = word 0 := by
    rw [r12]
    change (states 11).registers a0 = word 0
    exact result11
  have pc1 : (states 1).pc = word 0x802004a0 := by
    rw [p1, entryPC] <;> decide
  have pc2 : (states 2).pc = word 0x802004a4 := by
    rw [p2, pc1] <;> decide
  have pc3 : (states 3).pc = word 0x802004a8 := by
    rw [p3, pc2] <;> decide
  have pc4 : (states 4).pc = word 0x802004ac := by
    rw [p4, pc3] <;> decide
  have pc5 : (states 5).pc = word 0x802004b0 := by
    rw [p5, pc4] <;> decide
  have pc6 : (states 6).pc = word 0x802004b4 := by
    rw [p6, pc5] <;> decide
  have pc7 : (states 7).pc = word 0x802004b8 := by
    rw [p7, pc6] <;> decide
  have pc8 : (states 8).pc = word 0x802004bc := by
    rw [p8, pc7] <;> decide
  have pc9 : (states 9).pc = word 0x802004c0 := by
    rw [p9, pc8] <;> decide
  have pc10 : (states 10).pc = word 0x802004c4 := by
    rw [p10, pc9] <;> decide
  have pc11 : (states 11).pc = word 0x802004c8 := by
    rw [p11, pc10] <;> decide
  have pc12 : (states 12).pc = word 0x802004cc := by
    rw [p12, pc11] <;> decide
  have ea1 : address (states 1) spReg 24 = word (entry.val - 8) := by
    unfold address
    rw [sp1, slot_twentyfour entry depth]
  have ea2 : address (states 2) spReg 16 = word (entry.val - 16) := by
    unfold address
    rw [sp2, slot_sixteen entry depth]
  have ea9 : address (states 9) spReg 24 = word (entry.val - 8) := by
    unfold address
    rw [sp9, slot_twentyfour entry depth]
  have ea10 : address (states 10) spReg 16 = word (entry.val - 16) := by
    unfold address
    rw [sp10, slot_sixteen entry depth]
  refine ⟨result12, sp12, ?_, ?_, ?_, frame_bounds entry depth aligned, ioEA, fetch,
    ?_, ?_, ea1, ?_, ea2, ?_, ea4, ?_, ea5, ?_, ea9, ?_, ea10, ?_⟩
  · rw [act0, act1, act2, act3, act4, act5, act6, act7, act8, act9, act10, act11, ioEA, payload7]
  · rw [entryPC, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, pc11, pc12]
  · rw [pc12]
    decide
  · simpa only [ioEA] using permission
  · simpa only [ioEA, payload7] using completed
  · rw [← ea1]
    exact storeRa
  · rw [← ea2]
    exact storeFp
  · rw [← ea4]
    exact storeSpill
  · rw [← ea5]
    exact loadSpill
  · rw [← ea9]
    exact loadRa
  · rw [← ea10]
    exact loadFp


/- Closed artifact instances: no decode or desired-endpoint premises. -/

theorem read_f7 (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) (entry : Word) (trace : ReadPrefix env states actions)
    (entryPC : (states 0).pc = word 0x80200350)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (device : env.addressClass (word 0x10000005) = .device) :
    ReadConclusion env states actions entry ∧ decode ⟨0x00008067, by decide⟩ = some .ret := by
  exact ⟨read_projection env states actions entry trace entryPC zero stack depth aligned device,
    decode_word_224⟩

theorem write_f8 (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) (entry : Word)
    (trace : WritePrefix ⟨0x00358593, by decide⟩ env states actions)
    (entryPC : (states 0).pc = word 0x802003bc)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word (0x10000000 + 3)) = .device) :
    WriteConclusion 0x802003bc 3 env states actions entry ∧
      decode ⟨0x00008067, by decide⟩ = some .ret := by
  exact ⟨write_projection ⟨0x00358593, by decide⟩ 3 0x802003bc env states actions entry
    trace entryPC zero stack depth aligned ordinary device (by decide) (by decide) (by decide)
    decode_word_246, decode_word_252⟩

theorem write_f9 (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) (entry : Word)
    (trace : WritePrefix ⟨0x00158593, by decide⟩ env states actions)
    (entryPC : (states 0).pc = word 0x802003f4)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word (0x10000000 + 1)) = .device) :
    WriteConclusion 0x802003f4 1 env states actions entry ∧
      decode ⟨0x00008067, by decide⟩ = some .ret := by
  exact ⟨write_projection ⟨0x00158593, by decide⟩ 1 0x802003f4 env states actions entry
    trace entryPC zero stack depth aligned ordinary device (by decide) (by decide) (by decide)
    decode_word_260, decode_word_266⟩

theorem write_f10 (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) (entry : Word)
    (trace : WritePrefix ⟨0x00258593, by decide⟩ env states actions)
    (entryPC : (states 0).pc = word 0x8020042c)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word (0x10000000 + 2)) = .device) :
    WriteConclusion 0x8020042c 2 env states actions entry ∧
      decode ⟨0x00008067, by decide⟩ = some .ret := by
  exact ⟨write_projection ⟨0x00258593, by decide⟩ 2 0x8020042c env states actions entry
    trace entryPC zero stack depth aligned ordinary device (by decide) (by decide) (by decide)
    decode_word_274, decode_word_280⟩

theorem write_f11 (env : EEI) (states : Fin 14 → Concrete)
    (actions : Fin 13 → Action) (entry : Word)
    (trace : WritePrefix ⟨0x00458593, by decide⟩ env states actions)
    (entryPC : (states 0).pc = word 0x80200464)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word (0x10000000 + 4)) = .device) :
    WriteConclusion 0x80200464 4 env states actions entry ∧
      decode ⟨0x00008067, by decide⟩ = some .ret := by
  exact ⟨write_projection ⟨0x00458593, by decide⟩ 4 0x80200464 env states actions entry
    trace entryPC zero stack depth aligned ordinary device (by decide) (by decide) (by decide)
    decode_word_288, decode_word_294⟩

theorem write_f12 (env : EEI) (states : Fin 13 → Concrete)
    (actions : Fin 12 → Action) (entry : Word) (trace : WriteZeroPrefix env states actions)
    (entryPC : (states 0).pc = word 0x8020049c)
    (zero : (states 0).registers zeroReg = word 0)
    (stack : (states 0).registers spReg = entry) (depth : 32 ≤ entry.val)
    (aligned : entry.val % 16 = 0)
    (ordinary : env.addressClass (word (entry.val - 17)) = .ordinary)
    (device : env.addressClass (word 0x10000000) = .device) :
    WriteZeroConclusion env states actions entry ∧ decode ⟨0x00008067, by decide⟩ = some .ret := by
  exact ⟨write_zero_projection env states actions entry trace entryPC zero stack depth aligned
    ordinary device, decode_word_307⟩

end NativeUartByteCertificates
