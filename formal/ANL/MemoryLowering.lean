import ANL.MemoryTyping
import ANL.MemoryMirTyping

namespace ANL.Memory.Lowering

inductive Local where
  | value (temp : Mir.Temp)
  | mutable (slot : Mir.Slot)
  deriving DecidableEq, Repr

abbrev Locals := List Local

structure Supply where
  nextTemp : Nat
  nextSlot : Nat
  deriving DecidableEq, Repr

structure Fragment where
  instructions : List Mir.Instruction
  value : Mir.Temp
  deriving DecidableEq, Repr

def Fragment.block (f : Fragment) : Mir.Block := Mir.Block.fromInstructions f.instructions f.value
def Fragment.prefix (before : List Mir.Instruction) (f : Fragment) : Fragment :=
  { f with instructions := before ++ f.instructions }

structure Arguments where
  instructions : List Mir.Instruction
  values : List Mir.Temp
  deriving DecidableEq, Repr

def emit (ty : Ty) (op : Mir.Operation) (before : List Mir.Instruction) (s : Supply) : Fragment × Supply :=
  let value : Mir.Temp := ⟨s.nextTemp, ty⟩
  (⟨before ++ [⟨value, op⟩], value⟩, { s with nextTemp := s.nextTemp + 1 })

mutual
  /-- The binding lists use the core's nearest-binding-first indices. -/
  def term (viewOffset : Nat) (locals : Locals) (resources : List Nat) :
      Term → Supply → Option (Fragment × Supply)
    | .lit ty value, s => some (emit ty (match value with
        | .int n => .integer n | .bool b => .boolean b | .unit => .unit) [] s)
    | .local _ index, s => do
        match ← locals[index]? with
        | .value temp => pure (⟨[], temp⟩, s)
        | .mutable slot => pure (emit slot.ty (.load slot) [] s)
    | .letE _ value body, s => do
        let (initial, s) ← term viewOffset locals resources value s
        let (result, s) ← term viewOffset (.value initial.value :: locals) resources body s
        pure (result.prefix initial.instructions, s)
    | .letMut ty value body, s => do
        let (initial, s) ← term viewOffset locals resources value s
        let slot : Mir.Slot := ⟨s.nextSlot, initial.value.ty⟩
        let s := { s with nextSlot := s.nextSlot + 1 }
        let (body, s) ← term viewOffset (.mutable slot :: locals) resources body s
        pure (emit ty (.mutableScope slot initial.value body.block) initial.instructions s)
    | .assign ty index value, s => do
        let .mutable slot ← locals[index]? | none
        let (value, s) ← term viewOffset locals resources value s
        pure (emit ty (.store slot value.value) value.instructions s)
    | .whileE ty condition body, s => do
        let (condition, s) ← term viewOffset locals resources condition s
        let (body, s) ← term viewOffset locals resources body s
        pure (emit ty (.whileE condition.block body.block) [] s)
    | .ifE ty condition yes no, s => do
        let (condition, s) ← term viewOffset locals resources condition s
        let (yes, s) ← term viewOffset locals resources yes s
        let (no, s) ← term viewOffset locals resources no s
        pure (emit ty (.branch condition.value yes.block no.block) condition.instructions s)
    | .unary ty op operand, s => do
        let (operand, s) ← term viewOffset locals resources operand s
        pure (emit ty (.unary op operand.value) operand.instructions s)
    | .binary ty op left right, s => do
        let (left, s) ← term viewOffset locals resources left s
        if op = .and ∨ op = .or then
          let (right, s) ← term viewOffset locals resources right s
          let short := Mir.Block.yield left.value
          let branches := if op = .and then (right.block, short) else (short, right.block)
          pure (emit ty (.branch left.value branches.1 branches.2) left.instructions s)
        else
          let (right, s) ← term viewOffset locals resources right s
          pure (emit ty (.binary op left.value right.value) (left.instructions ++ right.instructions) s)
    | .call ty function args, s => do
        let (args, s) ← arguments viewOffset locals resources args s
        pure (emit ty (.call function args.values) args.instructions s)
    | .tuple ty fields, s => do
        let (fields, s) ← arguments viewOffset locals resources fields s
        pure (emit ty (.tuple fields.values) fields.instructions s)
    | .project ty value index, s => do
        let (value, s) ← term viewOffset locals resources value s
        pure (emit ty (.project value.value index) value.instructions s)
    | .heap ty site length initial success failure, s => do
        let owner := site + viewOffset
        let (length, s) ← term viewOffset locals resources length s
        let (initial, s) ← term viewOffset locals resources initial s
        let (success, s) ← term viewOffset locals (owner :: resources) success s
        let (failure, s) ← term viewOffset locals resources failure s
        pure (emit ty (.heapScope site owner length.value initial.block success.block failure.block)
          length.instructions s)
    | .bufferLength ty resource, s => do
        let resource ← resources[resource]?
        pure (emit ty (.bufferLength resource) [] s)
    | .bufferRead ty resource index, s => do
        let resource ← resources[resource]?
        let (index, s) ← term viewOffset locals resources index s
        pure (emit ty (.bufferRead resource index.value) index.instructions s)
    | .bufferWrite ty resource index value, s => do
        let resource ← resources[resource]?
        let (index, s) ← term viewOffset locals resources index s
        let (value, s) ← term viewOffset locals resources value s
        pure (emit ty (.bufferWrite resource index.value value.block) index.instructions s)
    | .callView ty function resource mode args, s => do
        let resource ← resources[resource]?
        let (args, s) ← arguments viewOffset locals resources args s
        pure (emit ty (.callView function resource mode args.values) args.instructions s)
  def arguments (viewOffset : Nat) (locals : Locals) (resources : List Nat) :
      List Term → Supply → Option (Arguments × Supply)
    | [], s => some (⟨[], []⟩, s)
    | arg :: args, s => do
        let (value, s) ← term viewOffset locals resources arg s
        let (rest, s) ← arguments viewOffset locals resources args s
        pure (⟨value.instructions ++ rest.instructions, value.value :: rest.values⟩, s)
end

def parameters (types : List Ty) : List Mir.Temp :=
  types.zipIdx.map (fun (ty, index) => ⟨index, ty⟩)

def viewOffset (view : Option ViewMode) : Nat := if view.isSome then 1 else 0

/-- The builder's maximum resource-table extent, independent of visit order. -/
def resourceCount (offset : Nat) (sites : List Nat) : Nat :=
  sites.foldl (fun count site => max count (site + offset + 1)) offset

def function (fn : Function) : Option Mir.Function := do
  let params := parameters fn.params
  let offset := viewOffset fn.view
  let resources := match fn.view with | none => [] | some _ => [0]
  let (body, supply) ← term offset (params.reverse.map Local.value) resources fn.body ⟨params.length, 0⟩
  pure ⟨fn.id, fn.view.map (·, 0), params, fn.result, body.block, supply.nextTemp, supply.nextSlot,
    resourceCount offset fn.body.heapSites⟩

def program (p : Program) : Option Mir.Program := do
  let functions ← p.functions.toList.mapM function
  pure ⟨"anl-memory-mir-v1", p.semanticRevision, p.profile, functions.toArray, p.entry⟩

end ANL.Memory.Lowering
