import ANL.BootRuntimeLaws
import ANL.BootRuntimeResetProofs

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem clear64_testBit (hn : n < wordModulus) (hm : mask < wordModulus) (i : Nat) :
    (clear64 n mask).testBit i = (n.testBit i && (decide (i < 64) && !mask.testBit i)) := by
  have kernel := clear64_kernel hn hm
  have bit := ANL.Word.binary_and_testBit kernel.2 i
  have complement := ANL.Word.complement_testBit kernel.1 i
  rw [complement] at bit
  exact bit

 theorem clear64_preserves_unmasked_bit (hn : n < wordModulus) (hm : mask < wordModulus)
    (inside : i < 64) (unmasked : mask.testBit i = false) :
    (clear64 n mask).testBit i = n.testBit i := by simp [clear64_testBit hn hm, inside, unmasked]
 theorem clear64_clears_masked_bit (hn : n < wordModulus) (hm : mask < wordModulus)
    (masked : mask.testBit i = true) : (clear64 n mask).testBit i = false := by
  simp [clear64_testBit hn hm, masked]

 theorem tick_reject_nonadmitted (phase : s.phase = .ordinary) (nontrap : NonTrap s.machine.control)
    (notPark : ¬ FirstPark p s) (notCaptured : ∀ q, ¬ Captured p s q) (rejected : ¬ Origin.Admitted p s.machine) :
    tickRaw p env s = .invalidState s := by
  have ready : Ready p s .ordinary := .ordinary phase nontrap notPark notCaptured
  simp [tickRaw, ready.compute, execute, Origin.step, Origin.checkAdmitted, rejected]

/-- Reserved primitive, role and synthetic grants never enter a fabricated body through this wrapper. -/
 theorem grant_rejected (phase : s.phase = .ordinary) (controlEq : s.machine.control = .grant ident loan values)
    (rejected : ¬ Origin.Admitted p s.machine) : tickRaw p env s = .invalidState s := by
  apply tick_reject_nonadmitted phase
  · simp [NonTrap, controlEq]
  · intro first
    have impossible := first.1.exact.1
    rw [controlEq] at impossible
    cases impossible
  · intro q captured
    cases captured with | invoke invocation _ _ => rw [controlEq] at invocation; cases invocation
  · exact rejected

 theorem primitive_grant_rejected (phase : s.phase = .ordinary)
    (controlEq : s.machine.control = .grant ident none values)
    (primitive : p.functions[ident]? = some (.primitive row)) : tickRaw p env s = .invalidState s := by
  apply grant_rejected phase controlEq
  simp [Origin.Admitted, controlEq, Origin.DefinedTarget, primitive]

 theorem role_grant_rejected (phase : s.phase = .ordinary)
    (controlEq : s.machine.control = .grant ident none values) (role : ident ∈ p.roleIDs) :
    tickRaw p env s = .invalidState s := by
  apply grant_rejected phase controlEq
  simp [Origin.Admitted, controlEq, Origin.DefinedTarget, role]

 theorem missing_grant_rejected (phase : s.phase = .ordinary)
    (controlEq : s.machine.control = .grant ident none values) (missing : p.functions[ident]? = none) :
    tickRaw p env s = .invalidState s := by
  apply grant_rejected phase controlEq
  simp [Origin.Admitted, controlEq, Origin.DefinedTarget, missing]

 theorem unsupported_language_trap (phase : s.phase = .ordinary) (controlEq : s.machine.control = .trap trap)
    (unsupported : languageTag trap = none) : tickRaw p env s = .invalidState s := by
  simp [tickRaw, command, phase, controlEq, unsupported]

 theorem raw_invalid_rejected (phase : s.phase = .ordinary) (controlEq : s.machine.control = .invalid) :
    tickRaw p env s = .invalidState s := by
  have notFirst : ¬ FirstPark p s := by
    intro first
    have impossible := first.1.exact.1
    rw [controlEq] at impossible
    cases impossible
  simp [tickRaw, command, phase, controlEq, notFirst, capture, execute, Origin.step, Origin.checkAdmitted,
    Origin.Admitted, Words.step]

 theorem park_boot_seen (phase : s.phase = .parkObserved location) (valid : ParkConsumed p s location)
    (boot : s.episode = .boot) : s.bootParkSeen = true ∧ s.episodeParkSeen = true ∧
      tickRaw p env s = .advance (withPhase s .ordinary) :=
  ⟨valid.2.2 boot, valid.2.1, tick_park_resume phase valid⟩

 theorem observed_first_park_false : ¬ FirstPark p (observedPark s location) := by
  intro first
  have seen := first.2.1
  cases seen

 theorem commit_install_eligible (boot : s.episode = .boot)
    (effect : Effect p env s.hardware s.readCursor (.installTrap authority target) args result) :
    Eligible p (commitState s q result) := by
  have policy := effect.operation
  cases policy
  cases effect.effect
  exact ⟨boot, rfl⟩

end ANL.Boot.Runtime
