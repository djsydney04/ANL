import ANL.BootRuntimeEffectCompletion

namespace ANL.Boot.Runtime

/-- A delivery key's relation to the current event summary, not proof that control reaches it. -/
inductive DeliveryPoint (p : Program) (events : List Event) (ordinal : Nat) : Landmark → Prop where
  | before : p.functions[ident]? = some (.primitive row) → DeliveryPoint p events ordinal (.beforePrimitive ordinal ident)
  | after : events = .primitive k ident op payload :: rest → k + 1 = ordinal →
      DeliveryPoint p events ordinal (.afterPrimitive k ident)
  | park : Scoped p (.bootPark location) → DeliveryPoint p events ordinal (.bootPark location)

/-- Independent current-summary history. No tick, reachable-state, or future-event premise occurs here. -/
inductive History (p : Program) (env : Environment) :
    List Event → Hardware → Nat → Nat → Episode → Bool → Prop where
  | initial : History p env [] ⟨env.sstatus, env.sie, none⟩ 0 1 .boot false
  | primitive : History p env events hardware cursor ordinal .boot used →
      p.functions[ident]? = some (.primitive row) →
      Effect p env hardware cursor row.operation arguments result →
      History p env (.primitive ordinal ident row.operation result.payload :: events)
        result.hardware result.cursor (ordinal + 1) .boot used
  | language : History p env events hardware cursor ordinal .boot used →
      LanguageTag kind tag →
      History p env (.language tag :: events) hardware cursor ordinal .languageHandler used
  | hardware : History p env events hardware cursor ordinal .boot false →
      hardware.installedHandler = some p.entries.hardware.function →
      env.delivery = some d → DeliveryValid p d → DeliveryPoint p events ordinal d.landmark →
      History p env (.hardware d.landmark d.scause d.sepc d.stval :: events)
        hardware cursor ordinal .hardwareHandler true

/-- The projection contains only the current transaction/reset summary. -/
def StateHistory (p : Program) (env : Environment) (s : State) : Prop :=
  History p env s.revEvents s.hardware s.readCursor s.nextOrdinal s.episode s.deliveryUsed

def primitiveOrdinals : List Event → List Nat
  | [] => []
  | .primitive ordinal _ _ _ :: rest => ordinal :: primitiveOrdinals rest
  | _ :: rest => primitiveOrdinals rest

def readPayloads : List Event → List Nat
  | [] => []
  | .primitive _ _ _ (.read n) :: rest => n :: readPayloads rest
  | _ :: rest => readPayloads rest

def resetCount : List Event → Nat
  | [] => 0
  | .primitive .. :: rest => resetCount rest
  | _ :: rest => resetCount rest + 1

/-- Consecutive committed ordinals, stored newest first like the raw event list. -/
inductive Consecutive : Nat → List Nat → Prop where
  | initial : Consecutive 1 []
  | commit : Consecutive ordinal rest → Consecutive (ordinal + 1) (ordinal :: rest)

/-- Exact consumed read prefix in reverse order; unused responses remain unconsumed. -/
inductive ReadPrefix (reads : List Nat) : Nat → List Nat → Prop where
  | initial : ReadPrefix reads 0 []
  | consume : ReadPrefix reads cursor rest → reads[cursor]? = some n → ReadPrefix reads (cursor + 1) (n :: rest)

variable {hardware : Hardware}

 theorem History.ordinals (history : History p env events hardware cursor ordinal episode used) :
    Consecutive ordinal (primitiveOrdinals events) := by
  induction history with
  | initial => exact .initial
  | primitive _ _ _ ih => exact .commit ih
  | language _ _ ih | hardware _ _ _ _ _ ih => exact ih

 theorem OperationEffect.read_prefix (effect : OperationEffect env hardware cursor op args result)
    (consumed : ReadPrefix env.reads cursor (readPayloads events)) :
    ReadPrefix env.reads result.cursor (readPayloads (.primitive ordinal ident op result.payload :: events)) := by
  cases effect with
  | read found _ => exact .consume consumed found
  | write | fence | clear | set | install => exact consumed

 theorem History.reads (history : History p env events hardware cursor ordinal episode used) :
    ReadPrefix env.reads cursor (readPayloads events) := by
  induction history with
  | initial => exact .initial
  | primitive _ _ effect ih => exact effect.effect.read_prefix ih
  | language _ _ ih | hardware _ _ _ _ _ ih => exact ih

 theorem History.reset_count (history : History p env events hardware cursor ordinal episode used) :
    resetCount events = (if episode = .boot then 0 else 1) := by
  induction history with
  | initial => rfl
  | primitive _ _ _ ih => exact ih
  | language _ _ ih | hardware _ _ _ _ _ ih => simp_all [resetCount]

 theorem History.at_most_one_reset (history : History p env events hardware cursor ordinal episode used) :
    resetCount events ≤ 1 := by rw [history.reset_count]; split <;> decide

 theorem Consecutive.positive (sequence : Consecutive ordinal ordinals) : 0 < ordinal := by
  cases sequence <;> omega
 theorem Consecutive.length (sequence : Consecutive ordinal ordinals) : ordinals.length + 1 = ordinal := by
  induction sequence with
  | initial => rfl
  | commit _ ih => simp_all
 theorem ReadPrefix.length (sequence : ReadPrefix reads cursor values) : values.length = cursor := by
  induction sequence with
  | initial => rfl
  | consume _ _ ih => simp_all
 theorem ReadPrefix.bound (sequence : ReadPrefix reads cursor values) : cursor ≤ reads.length := by
  cases sequence with
  | initial => omega
  | consume _ found => have bound := (List.getElem?_eq_some_iff.mp found).1; omega

 theorem ReadPrefix.exact (sequence : ReadPrefix reads cursor values) : values.reverse = reads.take cursor := by
  induction sequence with
  | initial => rfl
  | consume _ found ih => simp [List.reverse_cons, ih, List.take_add_one, found]

 theorem ReadPrefix.unused (sequence : ReadPrefix reads cursor values) : values.reverse ++ reads.drop cursor = reads := by
  rw [sequence.exact]
  exact List.take_append_drop cursor reads

 theorem History.read_count (history : History p env events hardware cursor ordinal episode used) :
    (readPayloads events).length = cursor := history.reads.length
 theorem History.read_prefix (history : History p env events hardware cursor ordinal episode used) :
    (readPayloads events).reverse = env.reads.take cursor := history.reads.exact

end ANL.Boot.Runtime
