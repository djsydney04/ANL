import ANL.BootRuntimeEntry

namespace ANL.Boot.Runtime
open ANL.Words
set_option linter.unusedSimpArgs false

 theorem wordValue_iff : wordValue width n = some v ↔ WordAt width n v := by
  constructor
  · intro h
    unfold wordValue at h
    split at h
    next bound => simp only [Option.some.injEq] at h; subst v; exact .value bound
    next => cases h
  · intro h; cases h with | value bound => simp [wordValue, bound]

 theorem WordAt.type (h : WordAt width n v) : v.type = .scalar (.word width) := by cases h; rfl
 theorem WordAt.bound (h : WordAt width n v) : n < width.modulus := by cases h; assumption
 theorem WordAt.unique (h : WordAt width n v) (h' : WordAt width n v') : v = v' := by
  exact Option.some.inj ((wordValue_iff.mpr h).symm.trans (wordValue_iff.mpr h'))

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
 theorem Enter.aligned (h : Enter p f args w s) : Origin.Aligned p s (Origin.rootMetadata f) := by
  cases h with | defined found => exact ⟨rfl, .eval (.root found), .nil⟩

 theorem Enter.typed (wf : WellFormedProgram p) (h : Enter p f args .initial s)
    (role : RoleValid p f types) (arguments : args.map Val.type = types) : State.Typed p.carrier s unitTy := by
  cases h with | defined found =>
   cases role with | intro actual view params result =>
    have same := Option.some.inj (found.symm.trans actual)
    cases same
    have typed := Origin.root_typed wf found (values := args.reverse) (by
      simp [EnvTyped, Function.valueContext, immutable, List.map_reverse, arguments, params, Function.comp_def])
    simpa [Origin.rootState, result] using typed

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
    next.revEvents = .hardware d.landmark d.scause d.sepc d.stval :: s.revEvents ∧
    next.deliveryUsed = true ∧ next.episode = .hardwareHandler ∧ next.stackRole = .terminal := by
  cases h with | handler _ _ _ hm => exact ⟨rfl, rfl, rfl, hm.world, rfl, rfl, rfl, rfl, rfl⟩

 theorem LanguageReset.retains (h : LanguageReset p s tag next) :
    next.hardware = s.hardware ∧ next.readCursor = s.readCursor ∧ next.nextOrdinal = s.nextOrdinal ∧
    next.machine.world = s.machine.world ∧ next.interrupted = some s.snapshot ∧
    next.revEvents = .language tag :: s.revEvents ∧ next.deliveryUsed = s.deliveryUsed ∧
    next.episode = .languageHandler ∧ next.stackRole = .terminal := by
  cases h with | handler _ hm => exact ⟨rfl, rfl, rfl, hm.world, rfl, rfl, rfl, rfl, rfl⟩

end ANL.Boot.Runtime
