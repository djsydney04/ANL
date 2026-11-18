import ANL.WordsSimulationReturn

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

/-- Lowering frontiers may move back after a branch while saved runtime frames still fit. -/
theorem KontCode.limits_rebase (code : KontCode offset locals ids k result captures)
    (storage : code.StoreSafe before source target) (limits : code.Limits after)
    (le : SupplyLE before after) : code.Limits before := by
  induction code generalizing before after source target with
  | @nil offset locals ids =>
      exact limits
  | @yield offset locals ids k mk captures value parent ih =>
      exact ih storage.2.2.2 limits le
  | @destination offset locals ids k d tail mk captures parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      exact ⟨storage.2.2.2.2.1, limits.2⟩
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @scopeValue offset locals ids k resultShape captures value parent ih =>
      exact ih storage.2.2.2 limits le
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      exact ⟨Nat.le_trans le.1 limits.1, Nat.le_trans le.2 limits.2.1, limits.2.2⟩
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      exact ih storage.2.2.2 limits le
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @convert offset locals ids k d tail mk captures mode target value parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @logicalRight op prior offset locals ids k resultShape captures logical parent ih =>
      exact ih storage.2.2.2 limits le
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @project offset locals ids k d tail mk captures index value parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      exact ih storage.2.2.2 limits le
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      have fresh : before.nextTemp ≤ d.id := Nat.le_trans le.1 limits.1
      exact ⟨fresh, ih (parent.store_weaken storage.2.2.2 (SupplyLE.to_afterTemp fresh))
        limits.2 le.withTemp⟩
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      exact ih storage.2.2.2 limits le
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      exact limits
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      exact ⟨le.trans limits.1, limits.2⟩

end ANL.Words.Simulation
