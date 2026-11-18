import ANL.BootCheckProofs
import ANL.BootTail

namespace ANL.Boot.Origin
open ANL.Words

inductive Edge where
  | letValue | letBody | whileCondition | whileBody | ifCondition | ifThen | ifElse
  | unaryOperand | binaryLeft | binaryRight | callArgument (index : Nat)
  | convertOperand | tupleField (index : Nat) | projectOperand | assignValue
  deriving DecidableEq, Repr

abbrev Path := List Edge

structure Location where
  function : Nat
  path : Path
  deriving DecidableEq, Repr

def Location.root (function : Nat) : Location := ⟨function, []⟩
def Location.child (location : Location) (edge : Edge) : Location :=
  ⟨location.function, location.path ++ [edge]⟩

/-- Only ordinary source children have origins in the boot fragment. -/
def childTerm : Term → Edge → Option Term
  | .letE _ a _, .letValue | .letMut _ a _, .letValue => some a
  | .letE _ _ b, .letBody | .letMut _ _ b, .letBody => some b
  | .whileE _ c _, .whileCondition => some c
  | .whileE _ _ b, .whileBody => some b
  | .ifE _ c _ _, .ifCondition => some c
  | .ifE _ _ y _, .ifThen => some y
  | .ifE _ _ _ n, .ifElse => some n
  | .unary _ _ a, .unaryOperand => some a
  | .binary _ _ a _, .binaryLeft => some a
  | .binary _ _ _ b, .binaryRight => some b
  | .call _ _ args, .callArgument i => args[i]?
  | .convert _ _ _ a, .convertOperand => some a
  | .tuple _ args, .tupleField i => args[i]?
  | .project _ a _, .projectOperand => some a
  | .assign _ _ a, .assignValue => some a
  | _, _ => none

inductive Child : Term → Edge → Term → Prop where
  | letValue : Child (.letE t a b) .letValue a
  | letBody : Child (.letE t a b) .letBody b
  | mutValue : Child (.letMut t a b) .letValue a
  | mutBody : Child (.letMut t a b) .letBody b
  | condition : Child (.whileE t c b) .whileCondition c
  | body : Child (.whileE t c b) .whileBody b
  | ifCondition : Child (.ifE t c y n) .ifCondition c
  | ifThen : Child (.ifE t c y n) .ifThen y
  | ifElse : Child (.ifE t c y n) .ifElse n
  | unary : Child (.unary t op a) .unaryOperand a
  | left : Child (.binary t op a b) .binaryLeft a
  | right : Child (.binary t op a b) .binaryRight b
  | argument : args[i]? = some a → Child (.call t f args) (.callArgument i) a
  | convert : Child (.convert t mode target a) .convertOperand a
  | field : args[i]? = some a → Child (.tuple t args) (.tupleField i) a
  | project : Child (.project t a i) .projectOperand a
  | assign : Child (.assign t i a) .assignValue a

theorem childTerm_iff : childTerm e edge = some a ↔ Child e edge a := by
  constructor
  · intro h
    cases e <;> cases edge <;> simp only [childTerm] at h
    all_goals first | exact .argument h | exact .field h | (cases h <;> constructor)
  · intro h
    cases h <;> simp_all [childTerm]

def lookupTerm : Term → Path → Option Term
  | e, [] => some e
  | e, edge :: path => (childTerm e edge).bind (fun child => lookupTerm child path)

inductive At : Term → Path → Term → Prop where
  | root : At e [] e
  | child : Child e edge next → At next path last → At e (edge :: path) last

theorem lookupTerm_iff : lookupTerm e path = some a ↔ At e path a := by
  constructor
  · intro h
    induction path generalizing e with
    | nil => cases h; exact .root
    | cons edge path ih =>
      simp only [lookupTerm] at h
      cases found : childTerm e edge with
      | none => simp [found] at h
      | some next =>
        simp only [found, Option.bind_some] at h
        exact .child (childTerm_iff.mp found) (ih h)
  · intro h
    induction h with
    | root => rfl
    | child child _ ih => simp [lookupTerm, childTerm_iff.mpr child, ih]

theorem At.unique (left : At e path a) (right : At e path b) : a = b :=
  Option.some.inj ((lookupTerm_iff.mpr left).symm.trans (lookupTerm_iff.mpr right))

theorem At.append (first : At e before middle) (second : At middle after last) :
    At e (before ++ after) last := by
  induction first with
  | root => exact second
  | child h _ ih => exact .child h (ih second)

def lookup (p : Program) (location : Location) : Option Term := do
  let .defined d ← p.functions[location.function]? | none
  lookupTerm d.function.body location.path

inductive Located (p : Program) : Location → Term → Prop where
  | intro : p.functions[function]? = some (.defined d) → At d.function.body path term →
      Located p ⟨function, path⟩ term

theorem lookup_iff : lookup p location = some e ↔ Located p location e := by
  rcases location with ⟨function, path⟩
  constructor
  · intro h
    simp only [lookup] at h
    cases found : p.functions[function]? with
    | none => simp [found] at h
    | some row =>
      cases row with
      | primitive d => simp [found] at h
      | defined d =>
        simp only [found] at h
        exact .intro found (lookupTerm_iff.mp h)
  · intro h
    cases h with
    | intro found occurrence => simp [lookup, found, lookupTerm_iff.mpr occurrence]

theorem Located.root (found : p.functions[f]? = some (.defined d)) :
    Located p (Location.root f) d.function.body := .intro found .root

theorem Located.child (h : Located p location e) (child : Child e edge a) :
    Located p (location.child edge) a := by
  cases h with
  | intro found occurrence => exact .intro found (occurrence.append (.child child .root))

theorem Located.function_defined (h : Located p location e) :
    ∃ d, p.functions[location.function]? = some (.defined d) := by
  cases h with | intro found _ => exact ⟨_, found⟩

def tailPath (path : TailPath) : Path :=
  path.map (fun edge => match edge with | .value => .letValue | .body => .letBody)

theorem SelectedTail.at (selected : SelectedTail e path) : At e (tailPath path) park := by
  induction selected with
  | park => exact .root
  | letValue _ ih => exact .child .letValue ih
  | letBody _ _ ih => exact .child .letBody ih
  | mutValue _ ih => exact .child .mutValue ih
  | mutBody _ _ ih => exact .child .mutBody ih

theorem designatedTail_located (found : p.functions[f]? = some (.defined d))
    (selected : designatedTail d.function.body = some path) :
    Located p ⟨f, tailPath path⟩ park :=
  .intro found (SelectedTail.at (designatedTail_iff.mp selected))


theorem Child.memoryFree (child : Child e edge a) (free : MemoryFree e) : MemoryFree a := by
  cases child <;> simp only [MemoryFree] at free
  all_goals first | exact free | exact free.1 | exact free.2 | exact free.2.1 | exact free.2.2 | exact free _ (List.mem_of_getElem? (by assumption))

theorem At.memoryFree (occurrence : At e path a) (free : MemoryFree e) : MemoryFree a := by
  induction occurrence with
  | root => exact free
  | child child _ ih => exact ih (child.memoryFree free)

theorem Located.memoryFree (wellFormed : WellFormedProgram p) (h : Located p origin e) : MemoryFree e := by
  cases h with
  | intro found occurrence => exact occurrence.memoryFree (wellFormed.memoryFree found)

theorem Child.calls (child : Child e edge a) (mem : f ∈ ANL.Boot.calls a) : f ∈ ANL.Boot.calls e := by
  cases child <;> simp_all only [ANL.Boot.calls, List.mem_append, List.mem_cons, or_true, true_or]
  all_goals first | exact Or.inr (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? (by assumption), mem⟩) | exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? (by assumption), mem⟩

theorem At.calls (occurrence : At e path a) (mem : f ∈ ANL.Boot.calls a) : f ∈ ANL.Boot.calls e := by
  induction occurrence with
  | root => exact mem
  | child child _ ih => exact child.calls (ih mem)

theorem Located.call_target (wellFormed : WellFormedProgram p)
    (h : Located p origin (.call t f args)) : f < p.functions.length ∧ f ∉ p.roleIDs := by
  cases h with
  | intro found occurrence =>
    exact wellFormed.call_target found (occurrence.calls (by simp [ANL.Boot.calls]))

end ANL.Boot.Origin
