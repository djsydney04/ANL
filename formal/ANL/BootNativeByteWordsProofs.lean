import ANL.BootNativeByteWords

namespace ANL.Boot.NativeByte.Words

open ANL.Boot.NativeFrame ANL.Boot.NativeByte ANL.Boot.NativeByte.Registers
universe u
variable {Origin : Type u}

theorem lift_preserves (valuation : Origin → Byte)
    (lift : Lift op before after) (invariant : State.Inv valuation before) :
    State.Inv valuation after := by
  cases lift with
  | addi _ destination source immediate =>
      exact State.addi_preserves valuation before source destination immediate invariant
  | lui _ destination immediate =>
      exact State.lui_preserves valuation before destination immediate invariant
  | ld _ destination base offset span =>
      exact State.unsigned_load_preserves valuation before destination
        (addW (before.registers base) (wordInt offset)) 8 span (Or.inr (Or.inr (Or.inr rfl))) invariant
  | lbu _ destination base offset span =>
      exact State.unsigned_load_preserves valuation before destination
        (addW (before.registers base) (wordInt offset)) 1 span (Or.inl rfl) invariant
  | sd _ source base offset span =>
      exact State.store_preserves valuation before source
        (addW (before.registers base) (wordInt offset)) 8 span (Or.inr (Or.inr (Or.inr rfl))) invariant
  | sb _ source base offset span =>
      exact State.store_preserves valuation before source
        (addW (before.registers base) (wordInt offset)) 1 span (Or.inl rfl) invariant
  | ret => exact invariant

theorem ordinary_lift (step : OrdinaryStep env op before after)
    (registerFacts : FactRegs Origin) (memoryFacts : Word → Fact Origin) :
    ∃ result, Lift op (paired registerFacts memoryFacts before) result ∧
      result.registers = after.registers ∧ result.memory = after.memory := by
  cases step with
  | addi _ destination source immediate =>
      exact ⟨_, Lift.addi (paired registerFacts memoryFacts before) destination source immediate,
        rfl, rfl⟩
  | lui _ destination immediate =>
      exact ⟨_, Lift.lui (paired registerFacts memoryFacts before) destination immediate, rfl, rfl⟩
  | ld _ destination base offset ready =>
      exact ⟨_, Lift.ld (paired registerFacts memoryFacts before) destination base offset ready.span,
        rfl, rfl⟩
  | lbu _ destination base offset ready =>
      exact ⟨_, Lift.lbu (paired registerFacts memoryFacts before) destination base offset ready.span,
        rfl, rfl⟩
  | sd _ source base offset ready =>
      exact ⟨_, Lift.sd (paired registerFacts memoryFacts before) source base offset ready.span,
        rfl, rfl⟩
  | sb _ source base offset ready =>
      exact ⟨_, Lift.sb (paired registerFacts memoryFacts before) source base offset ready.span,
        rfl, rfl⟩
  | ret _ _ =>
      exact ⟨_, Lift.ret (paired registerFacts memoryFacts before), rfl, rfl⟩

theorem ordinary_preserves (valuation : Origin → Byte)
    (step : OrdinaryStep env op before after)
    (registerFacts : FactRegs Origin) (memoryFacts : Word → Fact Origin)
    (invariant : State.Inv valuation (paired registerFacts memoryFacts before)) :
    ∃ result, Lift op (paired registerFacts memoryFacts before) result ∧
      result.registers = after.registers ∧ result.memory = after.memory ∧
      State.Inv valuation result := by
  obtain ⟨result, lift, registers, memory⟩ := ordinary_lift step registerFacts memoryFacts
  exact ⟨result, lift, registers, memory, lift_preserves valuation lift invariant⟩

theorem normal_silent_preserves (valuation : Origin → Byte)
    (step : NormalStep env raw before .silent after)
    (registerFacts : FactRegs Origin) (memoryFacts : Word → Fact Origin)
    (invariant : State.Inv valuation (paired registerFacts memoryFacts before)) :
    ∃ op result, decode raw = some op ∧
      Lift op (paired registerFacts memoryFacts before) result ∧
      result.registers = after.registers ∧ result.memory = after.memory ∧
      State.Inv valuation result := by
  cases step with
  | ordinary _ decoded ordinary =>
      obtain ⟨result, lift, registers, memory, preserved⟩ :=
        ordinary_preserves valuation ordinary registerFacts memoryFacts invariant
      exact ⟨_, result, decoded, lift, registers, memory, preserved⟩

theorem normal_fetch_ready (step : NormalStep env raw before action after) :
    FetchReady env raw before := by
  cases step <;> assumption

theorem ordinary_zero_preserved (step : OrdinaryStep env op before after)
    (zero : before.registers zeroReg = word 0) :
    after.registers zeroReg = word 0 := by
  cases step <;> first
    | exact writeW_preserves_zero _ _ _ zero
    | exact zero

theorem normal_zero_preserved (step : NormalStep env raw before action after) :
    after.registers zeroReg = word 0 := by
  cases step with
  | ordinary ready _ ordinary => exact ordinary_zero_preserved ordinary ready.zero
  | read _ _ _ _ _ ready _ _ _ _ => exact writeW_preserves_zero _ _ _ ready.zero
  | write _ _ _ _ ready _ _ _ _ => exact ready.zero
  | fence _ ready _ _ => exact ready.zero

theorem ordinary_return_aligned (step : OrdinaryStep env .ret before after) :
    after.pc = returnTarget before ∧ after.pc.val % 4 = 0 := by
  cases step with
  | ret _ aligned => exact ⟨rfl, aligned⟩

theorem normal_return_aligned (step : NormalStep env raw before .silent after)
    (decoded : decode raw = some .ret) :
    after.pc = returnTarget before ∧ after.pc.val % 4 = 0 := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      exact ordinary_return_aligned ordinary

theorem normal_return_projection (step : NormalStep env raw before .silent after)
    (decoded : decode raw = some .ret) :
    after.registers = before.registers ∧ after.memory = before.memory := by
  cases step with
  | ordinary _ actual ordinary =>
      have same := Option.some.inj (actual.symm.trans decoded)
      subst_vars
      cases ordinary
      exact ⟨rfl, rfl⟩

theorem ld_zero_still_access (step : OrdinaryStep env (.ld zeroReg base offset) before after) :
    LoadReady env before (address before base offset) 8 ∧ after.registers = before.registers := by
  cases step
  constructor
  · assumption
  · rfl

theorem lbu_zero_still_access (step : OrdinaryStep env (.lbu zeroReg base offset) before after) :
    LoadReady env before (address before base offset) 1 ∧ after.registers = before.registers := by
  cases step
  constructor
  · assumption
  · rfl

end ANL.Boot.NativeByte.Words
