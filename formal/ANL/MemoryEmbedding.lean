import ANL.MemoryExecute
import APL.FlatProductsEmbedding

namespace ANL.Memory.Embedding

abbrev OldTerm := APL.FlatProducts.Term
abbrev OldFunction := APL.FlatProducts.Function
abbrev OldFunctions := APL.FlatProducts.Functions
abbrev OldSignatures := APL.FlatProducts.Signatures
abbrev OldFrame := APL.FlatProducts.Frame
abbrev OldState := APL.FlatProducts.State

def scalarLiteral (value : APL.Val) : Term := .lit (.scalar value.type) value

def literal : Val → Term
  | .scalar value => scalarLiteral value
  | .tuple fields => .tuple (.tuple (fields.map APL.Val.type)) (fields.fields.map scalarLiteral)

def inferred (sigs : OldSignatures) (context : VCtx) (e : OldTerm) : Ty :=
  (APL.FlatProducts.infer sigs context e).getD (.scalar .unit)

def term (sigs : OldSignatures) (context : VCtx) (e : OldTerm) : Term :=
  let ty := inferred sigs context e
  match e with
  | .lit value => literal value
  | .local index => .local ty index
  | .letE value body => .letE ty (term sigs context value)
      (term sigs ((inferred sigs context value, false) :: context) body)
  | .letMut value body => .letMut ty (term sigs context value)
      (term sigs ((inferred sigs context value, true) :: context) body)
  | .assign index value => .assign ty index (term sigs context value)
  | .whileE condition body => .whileE ty (term sigs context condition) (term sigs context body)
  | .ifE condition yes no => .ifE ty (term sigs context condition) (term sigs context yes) (term sigs context no)
  | .unary op operand => .unary ty op (term sigs context operand)
  | .binary op left right => .binary ty op (term sigs context left) (term sigs context right)
  | .call function args => .call ty function (args.map (term sigs context))
  | .tuple fields => .tuple ty (fields.map (term sigs context))
  | .project base index => .project ty (term sigs context base) index

def signatures (sigs : OldSignatures) : Signatures :=
  sigs.map (fun (params, result) => ⟨none, params, result⟩)

def function (sigs : OldSignatures) (id : Nat) (fn : OldFunction) : Function :=
  ⟨id, fn.name, none, fn.params, fn.result,
    term sigs (APL.FlatProducts.immutable fn.params.reverse) fn.body⟩

def functions (fs : OldFunctions) : Array Function :=
  fs.mapIdx (function (APL.FlatProducts.signatures fs))

def program (fs : OldFunctions) (profile : Profile) (entry : Nat) : Program :=
  ⟨"anl-core-v3", "anl-owned-buffers-v1", profile, functions fs, entry⟩

mutual
  inductive TermRel : OldTerm → Term → Prop where
    | lit : TermRel (.lit value) (literal value)
    | local : TermRel (.local index) (.local ty index)
    | letE : TermRel value value' → TermRel body body' →
        TermRel (.letE value body) (.letE ty value' body')
    | letMut : TermRel value value' → TermRel body body' →
        TermRel (.letMut value body) (.letMut ty value' body')
    | assign : TermRel value value' → TermRel (.assign index value) (.assign ty index value')
    | whileE : TermRel condition condition' → TermRel body body' →
        TermRel (.whileE condition body) (.whileE ty condition' body')
    | ifE : TermRel condition condition' → TermRel yes yes' → TermRel no no' →
        TermRel (.ifE condition yes no) (.ifE ty condition' yes' no')
    | unary : TermRel operand operand' → TermRel (.unary op operand) (.unary ty op operand')
    | binary : TermRel left left' → TermRel right right' →
        TermRel (.binary op left right) (.binary ty op left' right')
    | call : TermsRel args args' → TermRel (.call f args) (.call ty f args')
    | tuple : TermsRel fields fields' → TermRel (.tuple fields) (.tuple ty fields')
    | project : TermRel base base' → TermRel (.project base index) (.project ty base' index)
  inductive TermsRel : List OldTerm → List Term → Prop where
    | nil : TermsRel [] []
    | cons : TermRel head head' → TermsRel tail tail' → TermsRel (head :: tail) (head' :: tail')
end

inductive FrameRel : OldFrame → Frame → Prop where
  | bind : TermRel body body' → FrameRel (.bind permission body) (.bind permission body')
  | scope : FrameRel .scope .scope
  | assign : FrameRel (.assign index) (.assign index)
  | ifF : TermRel yes yes' → TermRel no no' → FrameRel (.ifF yes no) (.ifF yes' no')
  | unary : FrameRel (.unary op) (.unary op)
  | left : TermRel right right' → FrameRel (.left op right) (.left op right')
  | right : FrameRel (.right op left) (.right op left)
  | arguments : TermsRel remaining remaining' →
      FrameRel (.arguments callee remaining reversed) (.arguments callee none remaining' reversed)
  | callReturn : FrameRel (.callReturn caller) (.callReturn ⟨functionId, caller, []⟩ none)
  | condition : TermRel condition condition' → TermRel body body' →
      FrameRel (.condition condition body) (.condition condition' body')
  | body : TermRel condition condition' → TermRel body body' →
      FrameRel (.body condition body) (.body condition' body')
  | fields : TermsRel remaining remaining' →
      FrameRel (.fields remaining reversed) (.fields remaining' reversed)
  | project : FrameRel (.project index) (.project index)

inductive KontRel : List OldFrame → List Frame → Prop where
  | nil : KontRel [] []
  | cons : FrameRel head head' → KontRel tail tail' → KontRel (head :: tail) (head' :: tail')

inductive StateRel (world : World) : OldState → State → Prop where
  | eval : TermRel e e' → KontRel k k' →
      StateRel world (.eval e env k) ⟨.eval e', ⟨functionId, env, []⟩, k', world⟩
  | ret : KontRel k k' →
      StateRel world (.ret value env k) ⟨.ret value, ⟨functionId, env, []⟩, k', world⟩
  | invoke : KontRel k k' →
      StateRel world (.invoke callee reversed env k)
        ⟨.invoke callee none reversed, ⟨functionId, env, []⟩, k', world⟩
  | trap : StateRel world (.trap kind) ⟨.trap (.scalar kind), ⟨functionId, env, []⟩, k, world⟩
  | invalid : StateRel world .invalid ⟨.invalid, ⟨functionId, env, []⟩, k, world⟩

structure FunctionsRel (old : OldFunctions) (p : Program) : Prop where
  found : ∀ (f : Nat) (fn : OldFunction), old[f]? = some fn →
    ∃ translated : Function, p.functions[f]? = some translated ∧ translated.view = none ∧ TermRel fn.body translated.body
  missing : ∀ (f : Nat), old[f]? = none → p.functions[f]? = none

end ANL.Memory.Embedding
