import ANL.BootRuntimeHistory
import ANL.BootRuntimeHandlerSteps

namespace ANL.Boot.Runtime
open ANL.Words
variable {p : ANL.Boot.Program} {s : State}

 theorem Start.history (started : Start p env s) : StateHistory p env s := by
  cases started
  exact .initial

 theorem before_delivery_point (valid : BeforeValid p s q) :
    DeliveryPoint p s.revEvents s.nextOrdinal (.beforePrimitive q.ordinal q.declaration) := by
  obtain ⟨values, row, _, found, _, _⟩ := valid.1.invocation
  rw [valid.2]
  exact .before found

 theorem after_delivery_point (old : RuntimeInvariant p env s) (phase : s.phase = .primitiveAfter q value)
    (valid : AfterValid p s q value) :
    DeliveryPoint p s.revEvents s.nextOrdinal (.afterPrimitive q.ordinal q.declaration) := by
  have latest : LatestCommit s q value := by cases old.phase <;> simp_all
  obtain ⟨payload, rest, events, _⟩ := latest
  exact .after events valid.2.1

 theorem park_delivery_point (waiting : ParkWaiting p s location) (boot : s.episode = .boot) :
    DeliveryPoint p s.revEvents s.nextOrdinal (.bootPark location) := by
  have selected := waiting.1.2.2.1
  rw [boot] at selected
  cases selected with | role found tail => exact .park (.park found tail.search)

 theorem HardwareReset.history (input : InputValid p env) (history : StateHistory p env s)
    (present : DeliveryAt env s key d) (eligible : Eligible p s)
    (point : DeliveryPoint p s.revEvents s.nextOrdinal key) (reset : HardwareReset p s d next) :
    StateHistory p env next := by
  have used := present.unused
  have boot := eligible.1
  have installed := eligible.2
  have valid := present.valid input
  have keyEq := present.landmark_eq
  have supplied : env.delivery = some d := by cases present; assumption
  have old : History p env s.revEvents s.hardware s.readCursor s.nextOrdinal .boot false := by
    simpa only [StateHistory, boot, used] using history
  have new := History.hardware old installed supplied valid (keyEq ▸ point)
  cases reset
  exact new

 theorem LanguageReset.history (history : StateHistory p env s) (boot : s.episode = .boot)
    (tagged : LanguageTag kind tag) (reset : LanguageReset p s tag next) : StateHistory p env next := by
  have old : History p env s.revEvents s.hardware s.readCursor s.nextOrdinal .boot s.deliveryUsed := by
    simpa only [StateHistory, boot] using history
  have new := History.language old tagged
  cases reset
  exact new

 theorem commit_history (history : StateHistory p env s) (boot : s.episode = .boot)
    (valid : BeforeValid p s q) (effect : Effect p env s.hardware s.readCursor q.operation q.arguments result) :
    StateHistory p env (commitState s q result) := by
  obtain ⟨values, row, _, found, operation, _⟩ := valid.1.invocation
  have old : History p env s.revEvents s.hardware s.readCursor s.nextOrdinal .boot s.deliveryUsed := by
    simpa only [StateHistory, boot] using history
  have effect' : Effect p env s.hardware s.readCursor row.operation q.arguments result := by rw [operation]; exact effect
  have new := History.primitive old found effect'
  simpa only [StateHistory, commitState, boot, valid.2, operation] using new

 theorem Cut.history (cut : Cut p env s key fallback (.advance next))
    (input : InputValid p env) (history : StateHistory p env s)
    (point : DeliveryPoint p s.revEvents s.nextOrdinal key) (defaultHistory : StateHistory p env fallback) : StateHistory p env next := by
  cases cut with
  | absent => exact defaultHistory
  | deliver present eligible reset => exact reset.history input history present eligible point

 theorem BootStep.history (wf : WellFormedProgram p) (input : InputValid p env)
    (old : LocalSafety p env s) (orbit : HandlerOrbit p s) (history : StateHistory p env s)
    (step : BootStep p env s next) : StateHistory p env next := by
  by_cases boot : s.episode = .boot
  · cases step with | advance ready execution =>
     cases execution with
     | language reset => cases ready with | language _ _ tagged => exact reset.history history boot tagged
     | enterPark | captured | ordinary | finish | parkHandler | parkResume => exact history
     | commit effect => cases ready with | commit _ valid => exact commit_history history boot valid effect
     | before cut => cases ready with | before _ valid =>
       exact cut.history input history (before_delivery_point valid) history
     | after cut => cases ready with | after phase valid =>
       exact cut.history input history (after_delivery_point old.runtime phase valid) history
     | parkBoot _ cut => cases ready with | parkCheck _ waiting =>
       exact cut.history input history (park_delivery_point waiting boot) history
  · rcases handler_retains wf boot orbit step with ⟨episode, events, hardware, cursor, ordinal, used, _⟩
    unfold StateHistory
    rw [episode, events, hardware, cursor, ordinal, used]
    exact history

end ANL.Boot.Runtime
