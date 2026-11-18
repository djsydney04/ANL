import ANL.BootV2RuntimeInput
import ANL.BootRuntimeEntryProofs

namespace ANL.Boot.V2.Runtime
open ANL.Words
open ANL.Boot.Runtime (Delivery wordValue WordAt wordValue_iff)
set_option linter.unusedSimpArgs false

/-- Raw defined-row entry reverses ABI arguments and retains the world.
It does not dynamically check the raw signature or body; Enter.typed needs checked roles. -/
def enter (p : ANL.Boot.V2.Program) (function : Nat) (arguments : List Val) (world : ANL.Memory.World) :
    Option Words.State :=
  match p.functions[function]? with
  | some (.defined d) => some ⟨.eval d.function.body, ⟨function, arguments.reverse, []⟩, [], world⟩
  | _ => none

inductive Enter (p : ANL.Boot.V2.Program) (function : Nat) (arguments : List Val) (world : ANL.Memory.World) :
    Words.State → Prop where
  | defined : p.functions[function]? = some (.defined d) →
      Enter p function arguments world ⟨.eval d.function.body, ⟨function, arguments.reverse, []⟩, [], world⟩

def startState (env : Environment) (machine : Words.State) (function : Nat) : State :=
  ⟨machine, ANL.Boot.Origin.rootMetadata function, .legacy .ordinary, ⟨env.legacy.sstatus, env.legacy.sie, none⟩,
    .boot, .boot, 0, 1, [], false, false, false, false, none⟩

/-- Internal raw construction; the external gateway supplies InputValid without rescanning its reads. -/
def startRaw (p : ANL.Boot.V2.Program) (env : Environment) : Option State := do
  let hart ← wordValue .w64 env.legacy.hart
  let dtb ← wordValue .w64 env.legacy.opaqueDtb
  let machine ← enter p p.entries.boot.function [hart, dtb] .initial
  return startState env machine p.entries.boot.function

def start (p : ANL.Boot.V2.Program) (input : ValidatedInput p) : Option State := startRaw p input.raw

inductive Start (p : ANL.Boot.V2.Program) (env : Environment) : State → Prop where
  | boot : WordAt .w64 env.legacy.hart hart → WordAt .w64 env.legacy.opaqueDtb dtb →
      Enter p p.entries.boot.function [hart, dtb] .initial machine →
      Start p env (startState env machine p.entries.boot.function)

/-- Scheduled delivery D only. Its abstract Hardware retention is not the F forwarding rule. -/
def hardwareResetState (p : ANL.Boot.V2.Program) (s : State) (d : Delivery) (machine : Words.State) : State :=
  { s with
    machine := machine, origins := ANL.Boot.Origin.rootMetadata p.entries.hardware.function,
    phase := .legacy .ordinary, episode := .hardwareHandler, stackRole := .terminal,
    revEvents := .legacy (.hardware d.landmark d.scause d.sepc d.stval) :: s.revEvents,
    deliveryUsed := true,
    bootParkSeen := (match d.landmark with | .bootPark _ => true | _ => s.bootParkSeen),
    episodeParkSeen := false, interrupted := some s.snapshot }

def languageResetState (p : ANL.Boot.V2.Program) (s : State) (tag : Nat) (machine : Words.State) : State :=
  { s with
    machine := machine, origins := ANL.Boot.Origin.rootMetadata p.entries.language.function,
    phase := .legacy .ordinary, episode := .languageHandler, stackRole := .terminal,
    revEvents := .legacy (.language tag) :: s.revEvents, episodeParkSeen := false,
    interrupted := some s.snapshot }

def resetHardware (p : ANL.Boot.V2.Program) (s : State) (d : Delivery) : Option State := do
  let cause ← wordValue .w64 d.scause
  let pc ← wordValue .w64 d.sepc
  let auxiliary ← wordValue .w64 d.stval
  let machine ← enter p p.entries.hardware.function [cause, pc, auxiliary] s.machine.world
  return hardwareResetState p s d machine

def resetLanguage (p : ANL.Boot.V2.Program) (s : State) (tag : Nat) : Option State := do
  let value ← wordValue .w8 tag
  let machine ← enter p p.entries.language.function [value] s.machine.world
  return languageResetState p s tag machine

inductive HardwareReset (p : ANL.Boot.V2.Program) (s : State) (d : Delivery) : State → Prop where
  | handler : WordAt .w64 d.scause cause → WordAt .w64 d.sepc pc → WordAt .w64 d.stval auxiliary →
      Enter p p.entries.hardware.function [cause, pc, auxiliary] s.machine.world machine →
      HardwareReset p s d (hardwareResetState p s d machine)

inductive LanguageReset (p : ANL.Boot.V2.Program) (s : State) (tag : Nat) : State → Prop where
  | handler : WordAt .w8 tag value →
      Enter p p.entries.language.function [value] s.machine.world machine →
      LanguageReset p s tag (languageResetState p s tag machine)


 theorem enter_iff : enter p f args w = some s ↔ Enter p f args w s := by
  constructor
  · intro h
    unfold enter at h
    cases found : p.functions[f]? with
    | none => simp [found] at h
    | some row =>
      cases row with
      | primitive op => simp [found] at h
      | defined d =>
        simp only [found, Option.some.injEq] at h
        subst s
        exact .defined found
  · intro h; cases h with | defined found => simp [enter, found]

 theorem Enter.world (h : Enter p f args w s) : s.world = w := by cases h; rfl
 theorem Enter.arguments (h : Enter p f args w s) : s.current.env = args.reverse := by cases h; rfl
 theorem Enter.empty (h : Enter p f args w s) : s.kont = [] ∧ s.current.resources = [] := by cases h; exact ⟨rfl, rfl⟩
 theorem Enter.aligned (h : Enter p f args w s) : Origin.Aligned p s (ANL.Boot.Origin.rootMetadata f) := by
  cases h with | defined found => exact ⟨rfl, .eval (.root found), .nil⟩

 theorem Enter.typed (wf : WellFormedProgram p) (h : Enter p f args .initial s)
    (role : RoleValid p f types) (arguments : args.map Val.type = types) : State.Typed p.carrier s unitTy := by
  cases h with | defined found =>
   cases role with | intro actual view params result =>
    have same := Option.some.inj (found.symm.trans actual)
    cases same
    have typed := Origin.root_typed wf found (values := args.reverse) (by
      simp [EnvTyped, Function.valueContext, immutable, List.map_reverse, arguments, params, Function.comp_def])
    simpa [ANL.Boot.Origin.rootState, result] using typed

 theorem startRaw_iff : startRaw p env = some s ↔ Start p env s := by
  simp only [startRaw, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  constructor
  · rintro ⟨hart, hh, dtb, hd, machine, hm, rfl⟩
    exact .boot (wordValue_iff.mp hh) (wordValue_iff.mp hd) (enter_iff.mp hm)
  · rintro ⟨hh, hd, hm⟩
    exact ⟨_, wordValue_iff.mpr hh, _, wordValue_iff.mpr hd, _, enter_iff.mpr hm, rfl⟩

 theorem resetHardware_iff : resetHardware p s d = some next ↔ HardwareReset p s d next := by
  simp only [resetHardware, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  constructor
  · rintro ⟨cause, hc, pc, hp, aux, ha, machine, hm, rfl⟩
    exact .handler (wordValue_iff.mp hc) (wordValue_iff.mp hp) (wordValue_iff.mp ha) (enter_iff.mp hm)
  · rintro ⟨hc, hp, ha, hm⟩
    exact ⟨_, wordValue_iff.mpr hc, _, wordValue_iff.mpr hp, _, wordValue_iff.mpr ha, _, enter_iff.mpr hm, rfl⟩

 theorem resetLanguage_iff : resetLanguage p s tag = some next ↔ LanguageReset p s tag next := by
  simp only [resetLanguage, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  constructor
  · rintro ⟨value, hv, machine, hm, rfl⟩
    exact .handler (wordValue_iff.mp hv) (enter_iff.mp hm)
  · rintro ⟨hv, hm⟩
    exact ⟨_, wordValue_iff.mpr hv, _, enter_iff.mpr hm, rfl⟩

 theorem Start.typed (wf : WellFormedProgram p) (h : Start p env s) :
    State.Typed p.carrier s.machine unitTy ∧ Origin.Aligned p s.machine s.origins := by
  cases h with | boot hh hd hm =>
   exact ⟨hm.typed wf wf.roles.boot (by simp [hh.type, hd.type, wordTy]), hm.aligned⟩

 theorem HardwareReset.typed (wf : WellFormedProgram p) (world : s.machine.world = .initial)
    (h : HardwareReset p s d next) :
    State.Typed p.carrier next.machine unitTy ∧ Origin.Aligned p next.machine next.origins := by
  cases h with | handler hc hp ha hm =>
   rw [world] at hm
   exact ⟨hm.typed wf wf.roles.hardware (by simp [hc.type, hp.type, ha.type, wordTy]), hm.aligned⟩

 theorem LanguageReset.typed (wf : WellFormedProgram p) (world : s.machine.world = .initial)
    (h : LanguageReset p s tag next) :
    State.Typed p.carrier next.machine unitTy ∧ Origin.Aligned p next.machine next.origins := by
  cases h with | handler hv hm =>
   rw [world] at hm
   exact ⟨hm.typed wf wf.roles.language (by simp [hv.type, byteTy]), hm.aligned⟩

 theorem HardwareReset.retains (h : HardwareReset p s d next) :
    next.hardware = s.hardware ∧ next.readCursor = s.readCursor ∧ next.nextOrdinal = s.nextOrdinal ∧
    next.machine.world = s.machine.world ∧ next.interrupted = some s.snapshot ∧
    next.revEvents = .legacy (.hardware d.landmark d.scause d.sepc d.stval) :: s.revEvents ∧
    next.deliveryUsed = true ∧ next.forwardingUsed = s.forwardingUsed ∧ next.episode = .hardwareHandler ∧ next.stackRole = .terminal := by
  cases h with | handler _ _ _ hm => exact ⟨rfl, rfl, rfl, hm.world, rfl, rfl, rfl, rfl, rfl, rfl⟩

 theorem LanguageReset.retains (h : LanguageReset p s tag next) :
    next.hardware = s.hardware ∧ next.readCursor = s.readCursor ∧ next.nextOrdinal = s.nextOrdinal ∧
    next.machine.world = s.machine.world ∧ next.interrupted = some s.snapshot ∧
    next.revEvents = .legacy (.language tag) :: s.revEvents ∧ next.deliveryUsed = s.deliveryUsed ∧ next.forwardingUsed = s.forwardingUsed ∧
    next.episode = .languageHandler ∧ next.stackRole = .terminal := by
  cases h with | handler _ hm => exact ⟨rfl, rfl, rfl, hm.world, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Raw lookup checks row kind, not the parameter signature or body typing. -/
theorem enter_missing (found : p.functions[f]? = none) : enter p f args w = none := by
  simp [enter, found]

theorem enter_primitive (found : p.functions[f]? = some (.primitive row)) :
    enter p f args w = none := by simp [enter, found]

theorem role_enter_exists (role : RoleValid p f types) (args : List Val) (w : ANL.Memory.World) :
    ∃ machine, Enter p f args w machine := by
  cases role with
  | intro found view params result => exact ⟨_, .defined found⟩

theorem word_value_exists {width : ANL.Word.Width} {n : Nat}
    (bound : n < width.modulus) : ∃ value, WordAt width n value :=
  ⟨_, .value bound⟩

theorem startRaw_exists (wf : WellFormedProgram p) (input : InputValid p env) :
    ∃ state, startRaw p env = some state := by
  obtain ⟨hart, hh⟩ := word_value_exists (width := .w64) input.hart
  obtain ⟨dtb, hd⟩ := word_value_exists (width := .w64) input.opaqueDtb
  obtain ⟨machine, hm⟩ := role_enter_exists wf.roles.boot [hart, dtb] .initial
  exact ⟨_, startRaw_iff.mpr (.boot hh hd hm)⟩

theorem start_checked (wf : WellFormedProgram p) (input : ValidatedInput p) :
    ∃ state, start p input = some state ∧
      ANL.Words.State.Typed p.carrier state.machine unitTy ∧
      Origin.Aligned p state.machine state.origins := by
  obtain ⟨state, found⟩ := startRaw_exists wf input.valid
  exact ⟨state, found, (startRaw_iff.mp found).typed wf⟩

theorem resetHardware_exists (wf : WellFormedProgram p) (valid : DeliveryValid p d) :
    ∃ next, resetHardware p s d = some next := by
  obtain ⟨cause, hc⟩ := word_value_exists (width := .w64) valid.cause
  obtain ⟨pc, hp⟩ := word_value_exists (width := .w64) valid.pc
  obtain ⟨aux, ha⟩ := word_value_exists (width := .w64) valid.auxiliary
  obtain ⟨machine, hm⟩ := role_enter_exists wf.roles.hardware [cause, pc, aux] s.machine.world
  exact ⟨_, resetHardware_iff.mpr (.handler hc hp ha hm)⟩

theorem resetLanguage_exists (wf : WellFormedProgram p)
    (bound : tag < ANL.Boot.Runtime.byteModulus) :
    ∃ next, resetLanguage p s tag = some next := by
  obtain ⟨value, hv⟩ := word_value_exists (width := .w8) bound
  obtain ⟨machine, hm⟩ := role_enter_exists wf.roles.language [value] s.machine.world
  exact ⟨_, resetLanguage_iff.mpr (.handler hv hm)⟩

end ANL.Boot.V2.Runtime
