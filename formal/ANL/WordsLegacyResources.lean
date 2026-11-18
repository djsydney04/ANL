import ANL.WordsLegacyMachine
import ANL.WordsResourceEntry
import ANL.MemoryResourceEntry

namespace ANL.Words.Tool

open ANL.Memory

set_option linter.unusedSimpArgs false

def embedLimit : ANL.Memory.Tool.Limit → Limit
  | .depth => .depth
  | .expressionFuel => .expressionFuel
  | .slots => .slots
  | .liveCells => .liveCells
  | .fillFuel => .fillFuel
  | .tupleFields => .tupleFields

def embedMeter (m : ANL.Memory.Tool.Meter) : Meter :=
  ⟨m.fuel, m.slots, m.liveCells, m.tupleFields, m.depth, m.parents⟩

def embedConfiguration (c : ANL.Memory.Tool.Configuration) : Configuration :=
  ⟨embedState c.machine, embedMeter c.meter⟩

def embedPreflight : ANL.Memory.Tool.Preflight → Preflight
  | .allowed m => .allowed (embedMeter m)
  | .blocked why m => .blocked (embedLimit why) (embedMeter m)

def embedTick : ANL.Memory.Tool.Tick → Tick
  | .completed c => .completed (embedConfiguration c)
  | .resourceLimit why c => .resourceLimit (embedLimit why) (embedConfiguration c)
  | .advanced c => .advanced (embedConfiguration c)

def embedToolResult : ANL.Memory.Tool.Result → Result
  | .completed c => .completed (embedConfiguration c)
  | .resourceLimit why c => .resourceLimit (embedLimit why) (embedConfiguration c)
  | .exhausted c => .exhausted (embedConfiguration c)

theorem embed_enter : enter (embedMeter m) = embedPreflight (ANL.Memory.Tool.enter m) := by
  by_cases hd : m.depth < 256 <;> by_cases hf : 0 < m.fuel <;>
    simp [enter, ANL.Memory.Tool.enter, embedMeter, embedPreflight, embedLimit, maxDepth,
      ANL.Memory.Tool.maxDepth, hd, hf]

theorem embed_reserveSlots : reserveSlots (embedMeter m) n =
    embedPreflight (ANL.Memory.Tool.reserveSlots m n) := by
  by_cases h : m.slots + n ≤ 65536 <;>
    simp [reserveSlots, ANL.Memory.Tool.reserveSlots, embedMeter, embedPreflight, embedLimit,
      maxSlots, ANL.Memory.Tool.maxSlots, h]

theorem embed_reserveOwner : reserveOwner (embedMeter m) n =
    embedPreflight (ANL.Memory.Tool.reserveOwner m n) := by
  by_cases hc : m.liveCells + n ≤ 1048576 <;> by_cases hs : m.slots + 1 ≤ 65536 <;>
    by_cases hf : n ≤ m.fuel <;>
    simp [reserveOwner, ANL.Memory.Tool.reserveOwner, embedMeter, embedPreflight, embedLimit,
      maxSlots, ANL.Memory.Tool.maxSlots, maxLiveCells, ANL.Memory.Tool.maxLiveCells, hc, hs, hf]

theorem embed_reserveTuple : reserveTuple (embedMeter m) n =
    embedPreflight (ANL.Memory.Tool.reserveTuple m n) := by
  by_cases h : m.tupleFields + n ≤ 1048576 <;>
    simp [reserveTuple, ANL.Memory.Tool.reserveTuple, embedMeter, embedPreflight, embedLimit,
      maxTupleFields, ANL.Memory.Tool.maxTupleFields, h]

theorem embed_preflight : preflight (embedProgram p) (embedState s) (embedMeter m) =
    embedPreflight (ANL.Memory.Tool.preflight p s m) := by
  rcases s with ⟨ctrl, a, k, w⟩
  cases ctrl
  case eval e =>
    cases he : ANL.Memory.Tool.enter m with
    | blocked why retained => simp [preflight, ANL.Memory.Tool.preflight, embedState, embedControl, embed_enter, he, embedPreflight]
    | allowed entered =>
      cases e <;> simp [preflight, ANL.Memory.Tool.preflight, embedState, embedControl, embed_enter, he,
        embedPreflight, embedTerm, embed_reserveSlots]
  case ret v =>
    cases k with
    | nil => rfl
    | cons frame rest =>
      cases frame <;> simp only [preflight, ANL.Memory.Tool.preflight, embedState, embedControl,
        embedFrame, List.map_cons]
      all_goals try rfl
      all_goals try exact embed_reserveSlots
      case fields remaining values =>
        cases remaining <;> cases v <;>
          simp [embedVal, embed_reserveTuple, List.length_map, embedPreflight]
  case allocate site n init yes no =>
    simp only [preflight, ANL.Memory.Tool.preflight, embedState, embedControl, embedProgram]
    by_cases h : n ≤ p.profile.maxCells <;> simp [h, embed_reserveOwner, embedPreflight]
  all_goals rfl

theorem embed_finish : finish (embedState s) (embedState next) (embedMeter m) =
    embedMeter (ANL.Memory.Tool.finish s next m) := by
  rcases s with ⟨ctrl, a, k, w⟩
  rcases next with ⟨nextCtrl, nextA, nextK, nextW⟩
  cases ctrl
  case eval e =>
    cases e
    case tuple t fields => cases fields <;> cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
    case call t f args => cases args <;> cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
    case callView t f i mode args => cases args <;> cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
    all_goals cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
  case ret v =>
    cases k with
    | nil => cases nextCtrl <;> rfl
    | cons frame rest =>
      cases frame
      case arguments f loan remaining values => cases remaining <;> cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
      case fields remaining values => cases remaining <;> cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
      all_goals cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]
  all_goals cases nextCtrl <;> simp [finish, ANL.Memory.Tool.finish, embedState, embedControl, embedActivation, embedFrame,
        embedTerm, List.map_cons, List.map_nil, List.isEmpty_map, embedEnv, List.length_map,
        Meter.pushChild, Meter.pushCall, Meter.pop, Meter.parent, Meter.sibling, Meter.tailChild, Meter.release,
        ANL.Memory.Tool.Meter.pushChild, ANL.Memory.Tool.Meter.pushCall, ANL.Memory.Tool.Meter.pop,
        ANL.Memory.Tool.Meter.parent, ANL.Memory.Tool.Meter.sibling, ANL.Memory.Tool.Meter.tailChild,
        ANL.Memory.Tool.Meter.release, embedMeter]

theorem embed_commit : commit (embedProgram p) responses (embedState s) (embedMeter m) =
    (ANL.Memory.Tool.commit p responses s m).map embedConfiguration := by
  by_cases na : ANL.Memory.Tool.NotAllocation s.control
  · have na2 : NotAllocation (embedState s).control := by
      rcases s with ⟨ctrl, a, k, w⟩
      cases ctrl <;> exact na
    rw [commit_nonallocation na2, ANL.Memory.Tool.commit_nonallocation na, embed_step]
    cases ANL.Memory.step p responses s <;> simp [embedConfiguration, embed_finish]
  · rcases s with ⟨ctrl, a, k, w⟩
    cases ctrl <;> simp only [ANL.Memory.Tool.NotAllocation] at na
    all_goals try contradiction
    case allocate site n init yes no =>
      simp only [commit, ANL.Memory.Tool.commit, embedState, embedControl, embedProgram]
      cases ha : allocate p.profile responses w site n init with
      | mk result after => cases result <;> rfl

theorem embed_tick : tick (embedProgram p) responses (embedConfiguration c) =
    embedTick (ANL.Memory.Tool.tick p responses c) := by
  simp only [tick, ANL.Memory.Tool.tick, embedConfiguration, embed_isStopped, embed_preflight, embed_commit]
  split
  · rfl
  · cases hp : ANL.Memory.Tool.preflight p c.machine c.meter with
    | blocked why retained => rfl
    | allowed charged =>
      simp only [embedPreflight]
      rw [embed_commit]
      cases ANL.Memory.Tool.commit p responses c.machine charged <;> rfl

@[simp] theorem embedToolResult_configuration :
    (embedToolResult r).configuration = embedConfiguration r.configuration := by cases r <;> rfl

/-- Historical Core programs preserve every meter field, limit reason and retained prefix at equal budgets. -/
theorem embed_run : run (embedProgram p) responses budget (embedConfiguration c) =
    embedToolResult (ANL.Memory.Tool.run p responses budget c) := by
  induction budget generalizing c with
  | zero =>
    simp only [run, ANL.Memory.Tool.run, embedConfiguration, embed_isStopped]
    split <;> rfl
  | succ budget ih =>
    simp only [run, ANL.Memory.Tool.run, embed_tick]
    cases ANL.Memory.Tool.tick p responses c with
    | completed done => rfl
    | resourceLimit why done => rfl
    | advanced next => exact ih

@[simp] theorem embed_initial : embedConfiguration (ANL.Memory.Tool.initial p fuel) =
    initial (embedProgram p) fuel := rfl

theorem embed_run_entry : run (embedProgram p) responses budget (initial (embedProgram p) fuel) =
    embedToolResult (ANL.Memory.Tool.run p responses budget (ANL.Memory.Tool.initial p fuel)) := by
  rw [← embed_initial, embed_run]

theorem embed_run_world :
    (run (embedProgram p) responses budget (embedConfiguration c)).configuration.machine.world =
      (ANL.Memory.Tool.run p responses budget c).configuration.machine.world := by
  rw [embed_run, embedToolResult_configuration]
  rfl

theorem embed_unwind : unwind (embedConfiguration c) = embedConfiguration (ANL.Memory.Tool.unwind c) := rfl

end ANL.Words.Tool
