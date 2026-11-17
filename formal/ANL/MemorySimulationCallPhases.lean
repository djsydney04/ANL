import ANL.MemorySimulationMatch
import ANL.MemorySimulationCallBindings
import ANL.MemorySimulationSites

namespace ANL.Memory.Simulation
open Lowering

theorem invoke_step (canonical : Canonical p q)
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before after a b)
    (typed : State.Typed p ⟨.invoke functionId sourceLoan reversed, a, k, w⟩ ty)
    (step : Step p responses ⟨.invoke functionId sourceLoan reversed, a, k, w⟩ next) :
    Matched p q responses ⟨.invoke functionId sourceLoan reversed, a, k, w⟩
      ⟨.invoke functionId (sourceLoan.map loan) reversed.reverse, b, mk, w⟩ next := by
  have nextTyped := preservation canonical.1 typed step
  cases step with
  | invoke found mode =>
      obtain ⟨mf, lowered, _⟩ := function_typed_total (canonical.1.function_at found).body
      have lookup := (program_metadata canonical.2).2.2.2.2.2.2 functionId
      rw [found] at lookup
      have targetLookup := lookup.trans lowered
      have targetMode : mf.signature.view = Mir.loanMode (sourceLoan.map loan) := by
        rw [(function_metadata lowered).2.1]
        simpa only [Function.signature, Mir.loanMode, ANL.Memory.loanMode,
          Option.map_map, Function.comp_def, loan] using mode
      exact Matched.positive (.succ (Mir.Step.invokeFound targetLookup targetMode) .zero)
        (by omega) (.grant code placed)
  | invokeMissing => exact False.elim (nextTyped.not_invalid rfl)
  | invokeMode => exact False.elim (nextTyped.not_invalid rfl)

theorem grant_step (canonical : Canonical p q)
    (code : KontCode offset locals ids k (.returned mk) captures)
    (placed : Placed p code before after a b)
    (typed : State.Typed p ⟨.grant functionId sourceLoan reversed, a, k, w⟩ ty)
    (step : Step p responses ⟨.grant functionId sourceLoan reversed, a, k, w⟩ next) :
    Matched p q responses ⟨.grant functionId sourceLoan reversed, a, k, w⟩
      ⟨.grant functionId (sourceLoan.map loan) reversed.reverse, b, mk, w⟩ next := by
  have nextTyped := preservation canonical.1 typed step
  cases step with
  | grant found =>
      rename_i fn
      have fnTyped := canonical.1.function_at found
      have facts := code.store_facts placed.storage
      have modeAndArity : fn.view = ANL.Memory.loanMode sourceLoan ∧ reversed.length = fn.params.length := by
        rcases typed with ⟨_, controlTyped, _, _, _⟩
        dsimp only at controlTyped
        cases controlTyped with
        | grant signatureFound mode paramTypes _ =>
            have signatureEq := Option.some.inj ((signatures_lookup found).symm.trans signatureFound)
            cases signatureEq
            exact ⟨mode, by simpa only [Function.signature, List.length_reverse, List.length_map]
              using (congrArg List.length paramTypes).symm⟩
      obtain ⟨mf, lowered, _⟩ := function_typed_total fnTyped.body
      have lookup := (program_metadata canonical.2).2.2.2.2.2.2 functionId
      rw [found] at lookup
      have targetLookup := lookup.trans lowered
      obtain ⟨callee, calleeBound, represented, bounded⟩ := canonical_callee_related
        (functionId := functionId) lowered modeAndArity.2 modeAndArity.1
      let saved : Suspended := ⟨offset, locals, ids, after, a, b, facts.1,
        facts.2.1.weaken placed.range⟩
      let callerCode := KontCode.caller (sourceLoan := sourceLoan)
        (offset := viewOffset fn.view)
        (locals := (parameters fn.params).reverse.map Local.value)
        (ids := match fn.view with | none => [] | some _ => [0]) saved facts.2.2 code
      have calleePlaced : Placed p callerCode
          ⟨(parameters fn.params).length, 0⟩ ⟨(parameters fn.params).length, 0⟩
          ⟨functionId, reversed, loanResources sourceLoan⟩ callee :=
        ⟨SupplyLE.refl _,
          ⟨represented, bounded, (by intro capture member; cases member),
            code.store_weaken placed.storage placed.range⟩,
          placed.limits, ⟨placed.currentOffset, placed.offsets⟩, placed.sites,
          ⟨fn, found, rfl⟩⟩
      simp only [Lowering.function, bind, Option.bind_eq_some_iff, Option.pure_def] at lowered
      obtain ⟨⟨body, supply⟩, bodyLowered, equality⟩ := lowered
      cases equality
      obtain ⟨last, entered, related⟩ := enter_block (q := q) (responses := responses) (world := w)
        calleePlaced bodyLowered (SupplyLE.refl _) (function_scoped_sites fnTyped)
      exact Matched.positive (.succ (Mir.Step.grantFound targetLookup calleeBound) entered)
        (by omega) related
  | grantMissing => exact False.elim (nextTyped.not_invalid rfl)

theorem return_callReturn
    (code : KontCode offset locals ids (.callReturn sourceCaller sourceLoan :: k)
      (.returned (.callReturn targetCaller (sourceLoan.map loan) :: mk)) captures)
    (placed : Placed p code before after a b)
    (ready : AtResult b value (.returned (.callReturn targetCaller (sourceLoan.map loan) :: mk)) ctrl actualKont) :
    Matched p q responses ⟨.ret value, a, .callReturn sourceCaller sourceLoan :: k, w⟩
      ⟨ctrl, b, actualKont, w⟩ ⟨.revoke value, a, .callReturn sourceCaller sourceLoan :: k, w⟩ := by
  cases ready
  exact Matched.positive (.succ Mir.Step.callReturn .zero) (by omega) (.revoke code placed)

theorem revoke_step
    (code : KontCode offset locals ids (.callReturn sourceCaller sourceLoan :: k)
      (.returned (.callReturn targetCaller (sourceLoan.map loan) :: mk)) captures)
    (placed : Placed p code before after a b)
    (step : Step p responses ⟨.revoke value, a, .callReturn sourceCaller sourceLoan :: k, w⟩ next) :
    Matched p q responses ⟨.revoke value, a, .callReturn sourceCaller sourceLoan :: k, w⟩
      ⟨.revoke value, b, .callReturn targetCaller (sourceLoan.map loan) :: mk, w⟩ next := by
  cases step with
  | revoke => exact Matched.positive (.succ Mir.Step.revoke .zero) (by omega) (.restore code placed)
  | revokeWrong wrong => exact False.elim (wrong _ _ _ rfl)

theorem restore_step
    (code : KontCode offset locals ids (.callReturn sourceCaller sourceLoan :: k)
      (.returned (.callReturn targetCaller (sourceLoan.map loan) :: mk)) captures)
    (placed : Placed p code before after a b)
    (step : Step p responses ⟨.restore value, a, .callReturn sourceCaller sourceLoan :: k, w⟩ next) :
    Matched p q responses ⟨.restore value, a, .callReturn sourceCaller sourceLoan :: k, w⟩
      ⟨.restore value, b, .callReturn targetCaller (sourceLoan.map loan) :: mk, w⟩ next := by
  cases step with
  | restore =>
      cases code with
      | caller saved captured parent =>
          have parentPlaced : Placed p parent saved.bound saved.bound saved.source saved.target :=
            ⟨SupplyLE.refl _, placed.storage.2.2.2, placed.limits,
              placed.offsets.2, placed.sites, placed.offsets.1⟩
          exact Matched.positive (.succ Mir.Step.restore .zero) (by omega)
            (.ret parent parentPlaced .returned)
  | restoreWrong wrong => exact False.elim (wrong _ _ _ rfl)

end ANL.Memory.Simulation
