import ANL.WordsCore
import ANL.WordsValueTyping

namespace ANL.Words.Mir

/-- Raw ordinary references: the type annotation is checked, not trusted. -/
structure Temp where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

structure Slot where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

mutual
  /-- The instruction-list spine and final yield of a structured raw block. -/
  inductive Block where
    | yield (value : Temp)
    | next (destination : Temp) (operation : Operation) (rest : Block)
    deriving DecidableEq, Repr
  inductive Operation where
    | integer (value : APL.I64)
    | word (width value : Nat)
    | convert (mode : ConvertMode) (target : ScalarTy) (operand : Temp)
    | boolean (value : Bool)
    | unit
    | tuple (fields : List Temp)
    | project (value : Temp) (index : Nat)
    | unary (op : UOp) (operand : Temp)
    | binary (op : BOp) (left right : Temp)
    | call (function : Nat) (arguments : List Temp)
    | mutableScope (slot : Slot) (initial : Temp) (body : Block)
    | load (slot : Slot)
    | store (slot : Slot) (value : Temp)
    | whileE (condition body : Block)
    | branch (condition : Temp) (yes no : Block)
    | heapScope (site owner : Nat) (length : Temp) (initial success failure : Block)
    | bufferLength (resource : Nat)
    | bufferRead (resource : Nat) (index : Temp)
    | bufferWrite (resource : Nat) (index : Temp) (value : Block)
    | callView (function resource : Nat) (mode : ViewMode) (arguments : List Temp)
    deriving DecidableEq, Repr
end

structure Instruction where
  destination : Temp
  operation : Operation
  deriving DecidableEq, Repr

/-- Exact conversion from the wire's list-plus-yield block representation. -/
def Block.fromInstructions (instructions : List Instruction) (value : Temp) : Block :=
  instructions.foldr (fun i rest => .next i.destination i.operation rest) (.yield value)

def Block.instructions : Block → List Instruction
  | .yield _ => []
  | .next d op rest => ⟨d, op⟩ :: rest.instructions

def Block.yieldValue : Block → Temp
  | .yield value => value
  | .next _ _ rest => rest.yieldValue

theorem Block.fromInstructions_roundtrip (b : Block) :
    fromInstructions b.instructions b.yieldValue = b := by
  induction b using Block.rec (motive_2 := fun _ => True) <;>
    simp_all [fromInstructions, instructions, yieldValue]

structure Function where
  id : Nat
  view : Option (ViewMode × Nat)
  params : List Temp
  result : Ty
  body : Block
  tempCount : Nat
  slotCount : Nat
  resourceCount : Nat
  deriving DecidableEq, Repr

def Function.signature (f : Function) : Signature :=
  ⟨f.view.map Prod.fst, f.params.map Temp.ty, f.result⟩

structure Program where
  schema : String
  semanticRevision : String
  allocationProfile : Profile
  functions : Array Function
  entry : Nat
  deriving DecidableEq, Repr

def Program.signatures (p : Program) : Signatures := p.functions.map Function.signature

/-- Lexical availability, separate from the whole-function definition inventory. -/
structure Context where
  temps : List Temp := []
  slots : List Slot := []
  resources : List (Nat × Mode) := []
  deriving Repr

def Context.withTemp (c : Context) (v : Temp) : Context := { c with temps := v :: c.temps }
def Context.withSlot (c : Context) (s : Slot) : Context := { c with slots := s :: c.slots }
def Context.withOwner (c : Context) (r : Nat) : Context :=
  { c with resources := (r, .owner) :: c.resources }

def Function.context (f : Function) : Context :=
  ⟨f.params, [], match f.view with | none => [] | some (m, r) => [(r, m.mode)]⟩

def Temp.Typed (c : Context) (v : Temp) (t : Ty) : Prop := v ∈ c.temps ∧ v.ty = t
instance (c : Context) (v : Temp) (t : Ty) : Decidable (v.Typed c t) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Slot.Typed (c : Context) (s : Slot) (t : Ty) : Prop := s ∈ c.slots ∧ s.ty = t
instance (c : Context) (s : Slot) (t : Ty) : Decidable (s.Typed c t) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ArgsTyped (c : Context) (args : List Temp) (types : List Ty) : Prop :=
  (∀ v ∈ args, v ∈ c.temps) ∧ args.map Temp.ty = types
instance (c : Context) (args : List Temp) (types : List Ty) : Decidable (ArgsTyped c args types) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Readable (c : Context) (r : Nat) : Prop := ∃ binding ∈ c.resources, binding.1 = r
def Writable (c : Context) (r : Nat) : Prop :=
  ∃ binding ∈ c.resources, binding.1 = r ∧ binding.2.CanWrite
def Lendable (c : Context) (r : Nat) (mode : ViewMode) : Prop :=
  ∃ binding ∈ c.resources, binding.1 = r ∧ binding.2.CanLend mode
instance (c : Context) (r : Nat) : Decidable (Readable c r) :=
  inferInstanceAs (Decidable (∃ binding ∈ c.resources, binding.1 = r))
instance (c : Context) (r : Nat) : Decidable (Writable c r) :=
  inferInstanceAs (Decidable (∃ binding ∈ c.resources, binding.1 = r ∧ binding.2.CanWrite))
instance (c : Context) (r : Nat) (m : ViewMode) : Decidable (Lendable c r m) :=
  inferInstanceAs (Decidable (∃ binding ∈ c.resources, binding.1 = r ∧ binding.2.CanLend m))

/-- Signature-only call obligations include exact arity through list equality. -/
def CallTyped (sigs : Signatures) (c : Context) (f : Nat) (view : Option ViewMode)
    (args : List Temp) (t : Ty) : Prop :=
  match sigs[f]? with
  | none => False
  | some fn => fn.view = view ∧ ArgsTyped c args fn.params ∧ fn.result = t
instance (sigs : Signatures) (c : Context) (f : Nat) (v : Option ViewMode)
    (args : List Temp) (t : Ty) : Decidable (CallTyped sigs c f v args t) := by
  unfold CallTyped
  cases sigs[f]? <;> infer_instance

def TupleTyped (c : Context) (fields : List Temp) : Ty → Prop
  | .scalar _ => False
  | .tuple shape => ArgsTyped c fields (shape.fields.map Ty.scalar)
instance (c : Context) (fields : List Temp) (t : Ty) : Decidable (TupleTyped c fields t) := by
  cases t <;> unfold TupleTyped <;> infer_instance

def ProjectTyped (c : Context) (v : Temp) (index : Nat) (t : Ty) : Prop :=
  v ∈ c.temps ∧ match v.ty with
    | .scalar _ => False
    | .tuple shape => (shape.fields[index]?).map Ty.scalar = some t
instance (c : Context) (v : Temp) (index : Nat) (t : Ty) : Decidable (ProjectTyped c v index t) := by
  unfold ProjectTyped
  cases v.ty <;> infer_instance

mutual
  /-- Independent syntax-directed judgment. No reference to the checker. -/
  def Block.Typed (sigs : Signatures) (c : Context) : Block → Ty → Prop
    | .yield value, t => value.Typed c t
    | .next d op rest, t => op.Typed sigs c d.ty ∧ rest.Typed sigs (c.withTemp d) t
  def Operation.Typed (sigs : Signatures) (c : Context) : Operation → Ty → Prop
    | .integer _, t => t = .scalar (.legacy .i64)
    | .word width value, t => WordLiteralSig width value t
    | .convert mode target operand, t => operand ∈ c.temps ∧ ConvertSig mode target operand.ty t
    | .boolean _, t => t = .scalar (.legacy .bool)
    | .unit, t => t = .scalar (.legacy .unit)
    | .tuple fields, t => TupleTyped c fields t
    | .project value index, t => ProjectTyped c value index t
    | .unary op value, t => value ∈ c.temps ∧ UnarySig op value.ty t
    | .binary op a b, t => a ∈ c.temps ∧ b ∈ c.temps ∧ op ≠ .legacy .and ∧ op ≠ .legacy .or ∧
        BinarySig op a.ty b.ty t
    | .call f args, t => CallTyped sigs c f none args t
    | .mutableScope slot initial body, t => initial.Typed c slot.ty ∧
        body.Typed sigs (c.withSlot slot) t
    | .load slot, t => slot.Typed c t
    | .store slot value, t => slot ∈ c.slots ∧ value.Typed c slot.ty ∧ t = .scalar (.legacy .unit)
    | .whileE condition body, t => condition.Typed sigs c (.scalar (.legacy .bool)) ∧
        body.Typed sigs c (.scalar (.legacy .unit)) ∧ t = .scalar (.legacy .unit)
    | .branch condition yes no, t => condition.Typed c (.scalar (.legacy .bool)) ∧
        yes.Typed sigs c t ∧ no.Typed sigs c t
    | .heapScope _ owner length initial success failure, t =>
        length.Typed c (.scalar (.legacy .i64)) ∧ initial.Typed sigs c (.scalar (.legacy .i64)) ∧
        success.Typed sigs (c.withOwner owner) t ∧ failure.Typed sigs c t
    | .bufferLength resource, t => Readable c resource ∧ t = .scalar (.legacy .i64)
    | .bufferRead resource index, t => Readable c resource ∧ index.Typed c (.scalar (.legacy .i64)) ∧
        t = .scalar (.legacy .i64)
    | .bufferWrite resource index value, t => Writable c resource ∧
        index.Typed c (.scalar (.legacy .i64)) ∧ value.Typed sigs c (.scalar (.legacy .i64)) ∧ t = .scalar (.legacy .unit)
    | .callView f resource mode args, t => Lendable c resource mode ∧
        CallTyped sigs c f (some mode) args t
end

mutual
  def checkBlock (sigs : Signatures) (c : Context) : Block → Ty → Bool
    | .yield value, t => decide (value.Typed c t)
    | .next d op rest, t => checkOperation sigs c op d.ty && checkBlock sigs (c.withTemp d) rest t
  def checkOperation (sigs : Signatures) (c : Context) : Operation → Ty → Bool
    | .integer _, t => decide (t = .scalar (.legacy .i64))
    | .word width value, t => decide (wordLiteralType width value = some t)
    | .convert mode target operand, t => decide (operand ∈ c.temps ∧ convertType mode target operand.ty = some t)
    | .boolean _, t => decide (t = .scalar (.legacy .bool))
    | .unit, t => decide (t = .scalar (.legacy .unit))
    | .tuple fields, t => decide (TupleTyped c fields t)
    | .project value index, t => decide (ProjectTyped c value index t)
    | .unary op value, t => decide (value ∈ c.temps ∧ unaryType op value.ty = some t)
    | .binary op a b, t => decide (a ∈ c.temps ∧ b ∈ c.temps ∧ op ≠ .legacy .and ∧ op ≠ .legacy .or ∧
        binaryType op a.ty b.ty = some t)
    | .call f args, t => decide (CallTyped sigs c f none args t)
    | .mutableScope slot initial body, t => decide (initial.Typed c slot.ty) &&
        checkBlock sigs (c.withSlot slot) body t
    | .load slot, t => decide (slot.Typed c t)
    | .store slot value, t => decide (slot ∈ c.slots ∧ value.Typed c slot.ty ∧ t = .scalar (.legacy .unit))
    | .whileE condition body, t => checkBlock sigs c condition (.scalar (.legacy .bool)) &&
        checkBlock sigs c body (.scalar (.legacy .unit)) && decide (t = .scalar (.legacy .unit))
    | .branch condition yes no, t => decide (condition.Typed c (.scalar (.legacy .bool))) &&
        checkBlock sigs c yes t && checkBlock sigs c no t
    | .heapScope _ owner length initial success failure, t =>
        decide (length.Typed c (.scalar (.legacy .i64))) && checkBlock sigs c initial (.scalar (.legacy .i64)) &&
        checkBlock sigs (c.withOwner owner) success t && checkBlock sigs c failure t
    | .bufferLength resource, t => decide (Readable c resource ∧ t = .scalar (.legacy .i64))
    | .bufferRead resource index, t => decide (Readable c resource ∧ index.Typed c (.scalar (.legacy .i64)) ∧
        t = .scalar (.legacy .i64))
    | .bufferWrite resource index value, t => decide (Writable c resource ∧
        index.Typed c (.scalar (.legacy .i64))) && checkBlock sigs c value (.scalar (.legacy .i64)) &&
        decide (t = .scalar (.legacy .unit))
    | .callView f resource mode args, t => decide (Lendable c resource mode ∧
        CallTyped sigs c f (some mode) args t)
end

/-- Only syntactic definitions contribute; runtime loop iterations never do. -/
structure Inventory where
  temps : List Nat := []
  slots : List Nat := []
  resources : List Nat := []
  deriving Repr

mutual
  /-- Accumulation is linear in the raw structure and never uses declared counts. -/
  def Block.collect : Block → Inventory → Inventory
    | .yield _, acc => acc
    | .next d op rest, acc => rest.collect (op.collect { acc with temps := d.id :: acc.temps })
  def Operation.collect : Operation → Inventory → Inventory
    | .mutableScope slot _ body, acc => body.collect { acc with slots := slot.id :: acc.slots }
    | .whileE condition body, acc => body.collect (condition.collect acc)
    | .branch _ yes no, acc => no.collect (yes.collect acc)
    | .heapScope _ owner _ initial success failure, acc =>
        failure.collect (success.collect (initial.collect { acc with resources := owner :: acc.resources }))
    | .bufferWrite _ _ value, acc => value.collect acc
    | _, acc => acc
end

def Function.inventory (f : Function) : Inventory :=
  f.body.collect ⟨f.params.map Temp.id, [], match f.view with | none => [] | some (_, r) => [r]⟩

/-- Global uniqueness, density, and exact declared count, independent of traversal order. -/
def Dense (ids : List Nat) (declared : Nat) : Prop := ids.Perm (List.range declared)

/-- Sort only observed IDs and construct a range of their observed length. -/
def checkDense (ids : List Nat) (declared : Nat) : Bool :=
  decide (ids.length = declared) && decide (ids.mergeSort (· ≤ ·) = List.range ids.length)

def Function.WellFormed (sigs : Signatures) (f : Function) : Prop :=
  Dense f.inventory.temps f.tempCount ∧ Dense f.inventory.slots f.slotCount ∧
  Dense f.inventory.resources f.resourceCount ∧ f.body.Typed sigs f.context f.result

def checkFunction (sigs : Signatures) (f : Function) : Bool :=
  let defs := f.inventory
  checkDense defs.temps f.tempCount && checkDense defs.slots f.slotCount &&
  checkDense defs.resources f.resourceCount && checkBlock sigs f.context f.body f.result

def Program.PositionalIDs (p : Program) : Prop :=
  ∀ i ∈ List.range p.functions.size, (p.functions[i]?).map Function.id = some i
instance (p : Program) : Decidable p.PositionalIDs :=
  inferInstanceAs (Decidable (∀ i ∈ List.range p.functions.size, _))

def Program.EntryValid (p : Program) : Prop :=
  match p.functions[p.entry]? with
  | none => False
  | some f => f.view = none ∧ f.params = [] ∧ f.result = .scalar (.legacy .i64)
instance (p : Program) : Decidable p.EntryValid := by
  unfold Program.EntryValid
  cases p.functions[p.entry]? <;> infer_instance

def Program.WellFormed (p : Program) : Prop :=
  p.schema = "anl-words-mir-v1" ∧ p.semanticRevision = "anl-words-v1" ∧
  p.allocationProfile.Admissible ∧ p.PositionalIDs ∧ p.EntryValid ∧
  ∀ f ∈ p.functions.toList, f.WellFormed p.signatures

def checkProgram (p : Program) : Bool :=
  decide (p.schema = "anl-words-mir-v1" ∧ p.semanticRevision = "anl-words-v1" ∧
    p.allocationProfile.Admissible ∧ p.PositionalIDs ∧ p.EntryValid) &&
  p.functions.toList.all (checkFunction p.signatures)

end ANL.Words.Mir
