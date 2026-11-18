import ANL.BootRuntimeInputProofs

namespace ANL.Boot.Runtime
open ANL.Words

/-- Converts a validated mathematical word to the existing ordinary runtime scalar. -/
def wordValue (width : ANL.Word.Width) (n : Nat) : Option Val :=
  if h : n < width.modulus then some (.scalar (.word ⟨⟨width, n⟩, h⟩)) else none

inductive WordAt (width : ANL.Word.Width) (n : Nat) : Val → Prop where
  | value (bound : n < width.modulus) : WordAt width n (.scalar (.word ⟨⟨width, n⟩, bound⟩))

/-- Forward ABI arguments become the existing newest-first ordinary environment. World is retained. -/
def enter (p : ANL.Boot.Program) (function : Nat) (arguments : List Val) (world : ANL.Memory.World) :
    Option Words.State :=
  match p.functions[function]? with
  | some (.defined d) => some ⟨.eval d.function.body, ⟨function, arguments.reverse, []⟩, [], world⟩
  | _ => none

inductive Enter (p : ANL.Boot.Program) (function : Nat) (arguments : List Val) (world : ANL.Memory.World) :
    Words.State → Prop where
  | defined : p.functions[function]? = some (.defined d) →
      Enter p function arguments world ⟨.eval d.function.body, ⟨function, arguments.reverse, []⟩, [], world⟩

def startState (env : Environment) (machine : Words.State) (function : Nat) : State :=
  ⟨machine, Origin.rootMetadata function, .ordinary, ⟨env.sstatus, env.sie, none⟩,
    .boot, .boot, 0, 1, [], false, false, false, none⟩

/-- Internal raw construction; the external gateway supplies InputValid without rescanning its reads. -/
def startRaw (p : ANL.Boot.Program) (env : Environment) : Option State := do
  let hart ← wordValue .w64 env.hart
  let dtb ← wordValue .w64 env.opaqueDtb
  let machine ← enter p p.entries.boot.function [hart, dtb] .initial
  return startState env machine p.entries.boot.function

def start (p : ANL.Boot.Program) (input : ValidatedInput p) : Option State := startRaw p input.raw

inductive Start (p : ANL.Boot.Program) (env : Environment) : State → Prop where
  | boot : WordAt .w64 env.hart hart → WordAt .w64 env.opaqueDtb dtb →
      Enter p p.entries.boot.function [hart, dtb] .initial machine →
      Start p env (startState env machine p.entries.boot.function)

def hardwareResetState (p : ANL.Boot.Program) (s : State) (d : Delivery) (machine : Words.State) : State :=
  { s with
    machine := machine, origins := Origin.rootMetadata p.entries.hardware.function,
    phase := .ordinary, episode := .hardwareHandler, stackRole := .terminal,
    revEvents := .hardware d.landmark d.scause d.sepc d.stval :: s.revEvents,
    deliveryUsed := true,
    bootParkSeen := (match d.landmark with | .bootPark _ => true | _ => s.bootParkSeen),
    episodeParkSeen := false, interrupted := some s.snapshot }

def languageResetState (p : ANL.Boot.Program) (s : State) (tag : Nat) (machine : Words.State) : State :=
  { s with
    machine := machine, origins := Origin.rootMetadata p.entries.language.function,
    phase := .ordinary, episode := .languageHandler, stackRole := .terminal,
    revEvents := .language tag :: s.revEvents, episodeParkSeen := false,
    interrupted := some s.snapshot }

def resetHardware (p : ANL.Boot.Program) (s : State) (d : Delivery) : Option State := do
  let cause ← wordValue .w64 d.scause
  let pc ← wordValue .w64 d.sepc
  let auxiliary ← wordValue .w64 d.stval
  let machine ← enter p p.entries.hardware.function [cause, pc, auxiliary] s.machine.world
  return hardwareResetState p s d machine

def resetLanguage (p : ANL.Boot.Program) (s : State) (tag : Nat) : Option State := do
  let value ← wordValue .w8 tag
  let machine ← enter p p.entries.language.function [value] s.machine.world
  return languageResetState p s tag machine

inductive HardwareReset (p : ANL.Boot.Program) (s : State) (d : Delivery) : State → Prop where
  | handler : WordAt .w64 d.scause cause → WordAt .w64 d.sepc pc → WordAt .w64 d.stval auxiliary →
      Enter p p.entries.hardware.function [cause, pc, auxiliary] s.machine.world machine →
      HardwareReset p s d (hardwareResetState p s d machine)

inductive LanguageReset (p : ANL.Boot.Program) (s : State) (tag : Nat) : State → Prop where
  | handler : WordAt .w8 tag value →
      Enter p p.entries.language.function [value] s.machine.world machine →
      LanguageReset p s tag (languageResetState p s tag machine)

end ANL.Boot.Runtime
