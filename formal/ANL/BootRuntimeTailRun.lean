import ANL.BootRuntimeRunCompleteness

namespace ANL.Boot.Runtime

/-- Accumulated successful steps. The recursive call is in tail position; host stack behavior is separate. -/
def runAccum (p : Program) (env : Environment) : Nat → State → Nat → RunResult
  | budget, s, used =>
    match observe p s with
    | some kind => (observationResult env s kind).addUsed used
    | none =>
      match budget with
      | 0 => ⟨.exhausted, s, used⟩
      | remaining + 1 =>
        match tickRaw p env s with
        | .advance next => runAccum p env remaining next (used + 1)
        | .blockedRead retained => ⟨.blockedRead, retained, used⟩
        | .ineligibleDelivery retained => ⟨.ineligibleDelivery, retained, used⟩
        | .invalidState retained => ⟨.invalidState, retained, used⟩

def runTailRaw (p : Program) (env : Environment) (budget : Nat) (s : State) : RunResult :=
  runAccum p env budget s 0

/-- Resume takes one actual tick before entering the ordinary observation-first loop. -/
def resumeTailRaw (p : Program) (env : Environment) : Nat → State → RunResult
  | 0, s => ⟨.exhausted, s, 0⟩
  | remaining + 1, s =>
    match tickRaw p env s with
    | .advance next => runAccum p env remaining next 1
    | .blockedRead retained => ⟨.blockedRead, retained, 0⟩
    | .ineligibleDelivery retained => ⟨.ineligibleDelivery, retained, 0⟩
    | .invalidState retained => ⟨.invalidState, retained, 0⟩

theorem runAccum_eq (p : Program) (env : Environment) (budget : Nat) (s : State) (used : Nat) :
    runAccum p env budget s used = (runRaw p env budget s).addUsed used := by
  induction budget generalizing s used with
  | zero =>
    rw [runAccum, runRaw]
    cases observe p s <;> simp [RunResult.addUsed]
  | succ budget ih =>
    rw [runAccum, runRaw]
    cases observe p s with
    | some kind => rfl
    | none =>
      cases tickRaw p env s with
      | advance next =>
        simp only [ih, RunResult.addUsed, RunResult.bump]
        congr 1
        omega
      | blockedRead | ineligibleDelivery | invalidState => simp [RunResult.addUsed]

theorem runTailRaw_eq (p : Program) (env : Environment) (budget : Nat) (s : State) :
    runTailRaw p env budget s = runRaw p env budget s := by
  simp [runTailRaw, runAccum_eq, RunResult.addUsed]

theorem resumeTailRaw_eq (p : Program) (env : Environment) (budget : Nat) (s : State) :
    resumeTailRaw p env budget s = resumeRaw p env budget s := by
  cases budget with
  | zero => rfl
  | succ budget =>
    rw [resumeTailRaw, resumeRaw]
    cases tickRaw p env s <;> simp [runAccum_eq, RunResult.addUsed, RunResult.bump]

end ANL.Boot.Runtime
