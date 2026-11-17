import APL.LocalStateTyping
import APL.VCGContracts

namespace APL.LoopAnnotations

/-- Pure mathematical assertions over the current local environment, newest binding first.
There is no function-result or entry-parameter reference in this syntax. -/
inductive Assertion where
  | lit (v : VCG.MVal)
  | local (index : Nat)
  | unary (op : UOp) (a : Assertion)
  | binary (op : BOp) (a b : Assertion)
  deriving Repr

/-- Reuse specification arithmetic; the internal `param` slot denotes a current local. -/
def Assertion.toSpec : Assertion → VCG.Spec
  | .lit v => .lit v
  | .local i => .param i
  | .unary op a => .unary op a.toSpec
  | .binary op a b => .binary op a.toSpec b.toSpec

def Assertion.eval (locals : List VCG.MVal) : Assertion → Option VCG.MVal
  | .lit v => some v
  | .local i => locals[i]?
  | .unary op a => do VCG.mUnary op (← a.eval locals)
  | .binary op a b => do
      let va ← a.eval locals
      if VCG.mShort op va then some va else VCG.mBinary op va (← b.eval locals)

def Assertion.instantiate (locals : List VCG.SymTerm) (a : Assertion) : Option VCG.SymTerm :=
  a.toSpec.instantiate locals none

theorem Assertion.eval_toSpec (a : Assertion) (locals : List VCG.MVal)
    (result : Option VCG.MVal) : a.eval locals = a.toSpec.eval locals result := by
  induction a with
  | lit v => rfl
  | «local» i => rfl
  | unary op a ih => simp only [eval, toSpec, VCG.Spec.eval, ih]
  | binary op a b ia ib => simp only [eval, toSpec, VCG.Spec.eval, ia, ib]

/-- Instantiation uses current local order, without reversing entry parameters. -/
theorem Assertion.instantiate_sound {a : Assertion} {s : VCG.SymTerm}
    (h : a.instantiate syms = some s) (hp : VCG.EnvRep model syms locals) :
    s.eval model = a.eval (locals.map VCG.embed) := by
  rw [a.eval_toSpec _ none]
  exact VCG.instantiate_sound (value := none) h hp (by trivial)

/-- Static assertion typing does not establish arithmetic definedness or truth. -/
inductive Assertion.HasType : LocalState.Ctx → Assertion → Ty → Prop where
  | lit : HasType Γ (.lit v) v.type
  | local : Γ[i]? = some (t, permission) → HasType Γ (.local i) t
  | unary : HasType Γ a op.input → HasType Γ (.unary op a) op.output
  | binary : HasType Γ a u → HasType Γ b v → binaryType op u v = some t →
      HasType Γ (.binary op a b) t

/-- Runtime terms with invariant lists attached only to loop heads. -/
inductive Term where
  | lit (v : Val)
  | local (index : Nat)
  | letE (value body : Term)
  | letMut (value body : Term)
  | assign (index : Nat) (value : Term)
  | whileE (invariants : List Assertion) (condition body : Term)
  | ifE (condition yes no : Term)
  | unary (op : UOp) (operand : Term)
  | binary (op : BOp) (left right : Term)
  | call (function : Nat) (arguments : List Term)
  deriving Repr

def Term.erase : Term → LocalState.Term
  | .lit v => .lit v
  | .local i => .local i
  | .letE a b => .letE a.erase b.erase
  | .letMut a b => .letMut a.erase b.erase
  | .assign i a => .assign i a.erase
  | .whileE _ c b => .whileE c.erase b.erase
  | .ifE c a b => .ifE c.erase a.erase b.erase
  | .unary op a => .unary op a.erase
  | .binary op a b => .binary op a.erase b.erase
  | .call f args => .call f (args.map erase)

mutual
  /-- Verification-ready annotated typing, which requires a nonempty invariant list
  at every loop. Ordinary source typing still accepts loops without annotations. -/
  inductive HasType (sigs : LocalState.Signatures) : LocalState.Ctx → Term → Ty → Prop where
    | lit : HasType sigs Γ (.lit v) v.type
    | local : Γ[index]? = some (t, permission) → HasType sigs Γ (.local index) t
    | letE : HasType sigs Γ a u → HasType sigs ((u, false) :: Γ) b t →
        HasType sigs Γ (.letE a b) t
    | letMut : HasType sigs Γ a u → HasType sigs ((u, true) :: Γ) b t →
        HasType sigs Γ (.letMut a b) t
    | assign : Γ[i]? = some (t, true) → HasType sigs Γ a t →
        HasType sigs Γ (.assign i a) .unit
    | whileE : invariants ≠ [] →
        (∀ a ∈ invariants, Assertion.HasType Γ a .bool) →
        HasType sigs Γ c .bool → HasType sigs Γ b .unit →
        HasType sigs Γ (.whileE invariants c b) .unit
    | ifE : HasType sigs Γ c .bool → HasType sigs Γ a t → HasType sigs Γ b t →
        HasType sigs Γ (.ifE c a b) t
    | unary : HasType sigs Γ a op.input → HasType sigs Γ (.unary op a) op.output
    | binary : HasType sigs Γ a u → HasType sigs Γ b v → binaryType op u v = some t →
        HasType sigs Γ (.binary op a b) t
    | call : sigs[f]? = some (params, result) → ArgsTyped sigs Γ args params →
        HasType sigs Γ (.call f args) result
  inductive ArgsTyped (sigs : LocalState.Signatures) : LocalState.Ctx → List Term → List Ty → Prop where
    | nil : ArgsTyped sigs Γ [] []
    | cons : HasType sigs Γ e t → ArgsTyped sigs Γ es ts → ArgsTyped sigs Γ (e :: es) (t :: ts)
end

theorem erase_typed (h : HasType sigs Γ e t) : LocalState.HasType sigs Γ e.erase t := by
  induction h using HasType.rec
    (motive_2 := fun Γ es ts _ => LocalState.ArgsTyped sigs Γ (es.map Term.erase) ts) with
  | lit => simp only [Term.erase]; exact .lit
  | «local» hi => simpa only [Term.erase] using LocalState.HasType.local hi
  | letE _ _ ha hb => simpa only [Term.erase] using LocalState.HasType.letE ha hb
  | letMut _ _ ha hb => simpa only [Term.erase] using LocalState.HasType.letMut ha hb
  | assign hi _ ha => simpa only [Term.erase] using LocalState.HasType.assign hi ha
  | whileE _ _ _ _ hc hb => simpa only [Term.erase] using LocalState.HasType.whileE hc hb
  | ifE _ _ _ hc ha hb => simpa only [Term.erase] using LocalState.HasType.ifE hc ha hb
  | unary _ ha => simpa only [Term.erase] using LocalState.HasType.unary ha
  | binary _ _ hop ha hb => simpa only [Term.erase] using LocalState.HasType.binary ha hb hop
  | call hf _ ha => simpa only [Term.erase] using LocalState.HasType.call hf ha
  | nil => exact .nil
  | cons _ _ ha hb => exact .cons ha hb

structure Function where
  name : String
  params : List Ty
  result : Ty
  body : Term
  deriving Repr

abbrev Functions := Array Function

def signatures (fs : Functions) : LocalState.Signatures := fs.map fun fn => (fn.params, fn.result)

def Function.erase (fn : Function) : LocalState.Function :=
  { name := fn.name, params := fn.params, result := fn.result, body := fn.body.erase }

def eraseFunctions (fs : Functions) : LocalState.Functions := fs.map Function.erase

/-- Function parameters remain in declaration order; body locals reverse that order. -/
def WellTyped (fs : Functions) : Prop :=
  ∀ (f : Nat) (fn : Function), fs[f]? = some fn →
    HasType (signatures fs) (LocalState.immutable fn.params.reverse) fn.body fn.result

theorem erase_signatures : LocalState.signatures (eraseFunctions fs) = signatures fs := by
  simp [LocalState.signatures, signatures, eraseFunctions, Function.erase, Array.map_map]

theorem erase_wellTyped (h : WellTyped fs) : LocalState.WellTyped (eraseFunctions fs) := by
  intro f fn hf
  simp only [eraseFunctions, Array.getElem?_map, Option.map_eq_some_iff] at hf
  obtain ⟨old, ho, rfl⟩ := hf
  simpa only [erase_signatures, Function.erase] using erase_typed (h f old ho)

/-- Changes metadata at every loop, including loops in call arguments. -/
def Term.mapAnnotations (f : List Assertion → List Assertion) : Term → Term
  | .lit v => .lit v
  | .local i => .local i
  | .letE a b => .letE (a.mapAnnotations f) (b.mapAnnotations f)
  | .letMut a b => .letMut (a.mapAnnotations f) (b.mapAnnotations f)
  | .assign i a => .assign i (a.mapAnnotations f)
  | .whileE inv c b => .whileE (f inv) (c.mapAnnotations f) (b.mapAnnotations f)
  | .ifE c a b => .ifE (c.mapAnnotations f) (a.mapAnnotations f) (b.mapAnnotations f)
  | .unary op a => .unary op (a.mapAnnotations f)
  | .binary op a b => .binary op (a.mapAnnotations f) (b.mapAnnotations f)
  | .call function args => .call function (args.map (mapAnnotations f))

def Function.mapAnnotations (f : List Assertion → List Assertion) (fn : Function) : Function :=
  { fn with body := fn.body.mapAnnotations f }

def mapFunctions (f : List Assertion → List Assertion) (fs : Functions) : Functions :=
  fs.map (Function.mapAnnotations f)

theorem Term.erase_mapAnnotations (f : List Assertion → List Assertion) (e : Term) :
    (e.mapAnnotations f).erase = e.erase := by
  induction e using Term.rec
    (motive_2 := fun es => (es.map (Term.mapAnnotations f)).map Term.erase = es.map Term.erase) with
  | lit v => simp only [mapAnnotations, erase]
  | «local» i => simp only [mapAnnotations, erase]
  | letE a b ia ib => simp only [mapAnnotations, erase, ia, ib]
  | letMut a b ia ib => simp only [mapAnnotations, erase, ia, ib]
  | assign i a ia => simp only [mapAnnotations, erase, ia]
  | whileE inv c b ic ib => simp only [mapAnnotations, erase, ic, ib]
  | ifE c a b ic ia ib => simp only [mapAnnotations, erase, ic, ia, ib]
  | unary op a ia => simp only [mapAnnotations, erase, ia]
  | binary op a b ia ib => simp only [mapAnnotations, erase, ia, ib]
  | call function args ih => simp only [mapAnnotations, erase, ih]
  | nil => rfl
  | cons a args ia ih => simp only [List.map_cons, ia, ih]

theorem Function.erase_mapAnnotations (f : List Assertion → List Assertion) (fn : Function) :
    (fn.mapAnnotations f).erase = fn.erase := by
  simp only [mapAnnotations, erase, Term.erase_mapAnnotations]

theorem eraseFunctions_mapAnnotations (f : List Assertion → List Assertion) (fs : Functions) :
    eraseFunctions (mapFunctions f fs) = eraseFunctions fs := by
  simp only [eraseFunctions, mapFunctions, Array.map_map]
  congr 1
  funext fn
  exact fn.erase_mapAnnotations f

/-- Annotation changes preserve the actual value machine at every identical budget.
This theorem is about erasure into the Lean model, not source parsing or emitted code. -/
theorem run_mapAnnotations (f : List Assertion → List Assertion) (fs : Functions)
    (e : Term) (budget : Nat) (env : Env) (kont : List LocalState.Frame) :
    LocalState.run (eraseFunctions (mapFunctions f fs)) budget
      (.eval (e.mapAnnotations f).erase env kont) =
    LocalState.run (eraseFunctions fs) budget (.eval e.erase env kont) := by
  rw [eraseFunctions_mapAnnotations, Term.erase_mapAnnotations]

end APL.LoopAnnotations
