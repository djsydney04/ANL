import ANL.BootSessionMeaning

namespace ANL.Boot.Runtime.Session

def blocker : StopReason → Nat
  | .blockedRead | .ineligibleDelivery | .invalidState => 1
  | _ => 0

def ordinary (action : Action) : Nat :=
  match action.kind with | .resume => 0 | _ => 1

/-- Logical calls at the accepted ordinary companion's actual decision sites, not host work. -/
inductive RunCalls (p : Program) (env : Environment) : Nat → State → RunResult → Nat → Nat → Prop where
  | observed : Observation p s kind → ¬ PendingDelivery env s →
      RunCalls p env budget s ⟨.observed kind, s, 0⟩ 1 0
  | unobserved : Observation p s kind → PendingDelivery env s →
      RunCalls p env budget s ⟨.unobserved kind, s, 0⟩ 1 0
  | exhausted : (∀ kind, ¬ Observation p s kind) → RunCalls p env 0 s ⟨.exhausted, s, 0⟩ 1 0
  | blocked : (∀ kind, ¬ Observation p s kind) → BootOutcome p env s (.blockedRead s) →
      RunCalls p env (budget + 1) s ⟨.blockedRead, s, 0⟩ 1 1
  | ineligible : (∀ kind, ¬ Observation p s kind) → BootOutcome p env s (.ineligibleDelivery s) →
      RunCalls p env (budget + 1) s ⟨.ineligibleDelivery, s, 0⟩ 1 1
  | invalid : (∀ kind, ¬ Observation p s kind) → BootOutcome p env s (.invalidState s) →
      RunCalls p env (budget + 1) s ⟨.invalidState, s, 0⟩ 1 1
  | advance : (∀ kind, ¬ Observation p s kind) → BootStep p env s next →
      RunCalls p env budget next result observations ticks →
      RunCalls p env (budget + 1) s result.bump (observations + 1) (ticks + 1)

inductive ResumeCalls (p : Program) (env : Environment) : Nat → State → RunResult → Nat → Nat → Prop where
  | exhausted : ResumeCalls p env 0 s ⟨.exhausted, s, 0⟩ 0 0
  | blocked : BootOutcome p env s (.blockedRead s) →
      ResumeCalls p env (budget + 1) s ⟨.blockedRead, s, 0⟩ 0 1
  | ineligible : BootOutcome p env s (.ineligibleDelivery s) →
      ResumeCalls p env (budget + 1) s ⟨.ineligibleDelivery, s, 0⟩ 0 1
  | invalid : BootOutcome p env s (.invalidState s) →
      ResumeCalls p env (budget + 1) s ⟨.invalidState, s, 0⟩ 0 1
  | advance : BootStep p env s next → RunCalls p env budget next result observations ticks →
      ResumeCalls p env (budget + 1) s result.bump observations (ticks + 1)

theorem RunCalls.meaning (calls : RunCalls p env budget s result observations ticks) :
    RunTo p env budget s result := by
  induction calls with
  | observed obs absent => exact .observed obs absent
  | unobserved obs pending => exact .unobserved obs pending
  | exhausted absent => exact .exhausted absent
  | blocked absent outcome => exact .blocked absent outcome
  | ineligible absent outcome => exact .ineligible absent outcome
  | invalid absent outcome => exact .invalid absent outcome
  | advance absent step _ ih => exact .advance absent step ih

theorem runTo_calls (meaning : RunTo p env budget s result) :
    ∃ observations ticks, RunCalls p env budget s result observations ticks := by
  induction meaning with
  | observed obs absent => exact ⟨1, 0, .observed obs absent⟩
  | unobserved obs pending => exact ⟨1, 0, .unobserved obs pending⟩
  | exhausted absent => exact ⟨1, 0, .exhausted absent⟩
  | blocked absent outcome => exact ⟨1, 1, .blocked absent outcome⟩
  | ineligible absent outcome => exact ⟨1, 1, .ineligible absent outcome⟩
  | invalid absent outcome => exact ⟨1, 1, .invalid absent outcome⟩
  | advance absent step _ ih =>
    obtain ⟨o, t, rest⟩ := ih
    exact ⟨o + 1, t + 1, .advance absent step rest⟩

theorem RunCalls.counts (calls : RunCalls p env budget s result observations ticks) :
    observations = result.used + 1 ∧ ticks = result.used + blocker result.reason := by
  induction calls with
  | advance _ _ _ ih => simp only [RunResult.bump]; omega
  | _ => exact ⟨rfl, rfl⟩

theorem RunCalls.bounds (calls : RunCalls p env budget s result observations ticks) :
    observations ≤ budget + 1 ∧ ticks ≤ budget := by
  induction calls with
  | advance _ _ _ ih => omega
  | _ => omega

theorem ResumeCalls.meaning (calls : ResumeCalls p env budget s result observations ticks) :
    ResumeTo p env budget s result := by
  cases calls with
  | exhausted => exact .exhausted
  | blocked outcome => exact .blocked outcome
  | ineligible outcome => exact .ineligible outcome
  | invalid outcome => exact .invalid outcome
  | advance step rest => exact .advance step rest.meaning

theorem resumeTo_calls (meaning : ResumeTo p env budget s result) :
    ∃ observations ticks, ResumeCalls p env budget s result observations ticks := by
  cases meaning with
  | exhausted => exact ⟨0, 0, .exhausted⟩
  | blocked outcome => exact ⟨0, 1, .blocked outcome⟩
  | ineligible outcome => exact ⟨0, 1, .ineligible outcome⟩
  | invalid outcome => exact ⟨0, 1, .invalid outcome⟩
  | advance step rest =>
    obtain ⟨o, t, work⟩ := runTo_calls rest
    exact ⟨o, t + 1, .advance step work⟩

theorem ResumeCalls.counts (calls : ResumeCalls p env budget s result observations ticks) :
    observations = result.used ∧ ticks = result.used + blocker result.reason := by
  cases calls with
  | advance _ rest => have counts := rest.counts; simp only [RunResult.bump]; omega
  | _ => exact ⟨rfl, rfl⟩

theorem ResumeCalls.bounds (calls : ResumeCalls p env budget s result observations ticks) :
    observations ≤ budget ∧ ticks ≤ budget := by
  cases calls with
  | advance _ rest => have bounds := rest.bounds; omega
  | _ => omega

inductive ActionCalls (p : Program) (env : Environment) : Action → State → RunResult → Nat → Nat → Prop where
  | run : RunCalls p env budget s result observations ticks → ActionCalls p env ⟨.run, budget⟩ s result observations ticks
  | continued : RunCalls p env budget s result observations ticks → ActionCalls p env ⟨.continue, budget⟩ s result observations ticks
  | resumed : ResumeCalls p env budget s result observations ticks → ActionCalls p env ⟨.resume, budget⟩ s result observations ticks

theorem ActionCalls.meaning (calls : ActionCalls p env action s result observations ticks) :
    ActionTo p env action s result := by
  cases calls with
  | run calls => exact .run calls.meaning
  | continued calls => exact .continued calls.meaning
  | resumed calls => exact .resumed calls.meaning

theorem ActionTo.calls (meaning : ActionTo p env action s result) :
    ∃ observations ticks, ActionCalls p env action s result observations ticks := by
  cases meaning with
  | run meaning => obtain ⟨o, t, calls⟩ := runTo_calls meaning; exact ⟨o, t, .run calls⟩
  | continued meaning => obtain ⟨o, t, calls⟩ := runTo_calls meaning; exact ⟨o, t, .continued calls⟩
  | resumed meaning => obtain ⟨o, t, calls⟩ := resumeTo_calls meaning; exact ⟨o, t, .resumed calls⟩

theorem ActionCalls.counts (calls : ActionCalls p env action s result observations ticks) :
    observations = result.used + ordinary action ∧ ticks = result.used + blocker result.reason := by
  cases calls with
  | run calls | continued calls => exact calls.counts
  | resumed calls => simpa only [ordinary, Nat.add_zero] using calls.counts

theorem ActionCalls.bounds (calls : ActionCalls p env action s result observations ticks) :
    observations ≤ action.budget + ordinary action ∧ ticks ≤ action.budget := by
  cases calls with
  | run calls | continued calls => exact calls.bounds
  | resumed calls => simpa only [ordinary, Nat.add_zero] using calls.bounds

theorem action_calls_iff : actionRun p env action s = result ↔
    ∃ observations ticks, ActionCalls p env action s result observations ticks := by
  constructor
  · intro actual; exact (actionRun_iff.mp actual).calls
  · rintro ⟨_, _, calls⟩; exact calls.meaning.compute

end ANL.Boot.Runtime.Session
