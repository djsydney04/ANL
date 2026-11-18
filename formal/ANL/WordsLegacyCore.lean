import ANL.WordsCore

namespace ANL.Words

def embedSignature (s : ANL.Memory.Signature) : Signature :=
  ⟨s.view, s.params.map embedTy, embedTy s.result⟩
def embedSignatures (sigs : ANL.Memory.Signatures) : Signatures := sigs.map embedSignature
def embedContext (Γ : ANL.Memory.VCtx) : VCtx := Γ.map fun (t, permission) => (embedTy t, permission)
def embedEnv (env : APL.FlatProducts.Env) : Env := env.map embedVal

def embedResult : APL.FlatProducts.Result → Result
  | .value v => .value (embedVal v)
  | .trap t => .trap (legacyTrap t)
  | .invalid => .invalid

def embedTerm : ANL.Memory.Term → Term
  | .lit t v => .lit (embedTy t) v
  | .local t i => .local (embedTy t) i
  | .letE t a b => .letE (embedTy t) (embedTerm a) (embedTerm b)
  | .letMut t a b => .letMut (embedTy t) (embedTerm a) (embedTerm b)
  | .assign t i a => .assign (embedTy t) i (embedTerm a)
  | .whileE t a b => .whileE (embedTy t) (embedTerm a) (embedTerm b)
  | .ifE t c a b => .ifE (embedTy t) (embedTerm c) (embedTerm a) (embedTerm b)
  | .unary t op a => .unary (embedTy t) (.legacy op) (embedTerm a)
  | .binary t op a b => .binary (embedTy t) (.legacy op) (embedTerm a) (embedTerm b)
  | .call t f args => .call (embedTy t) f (args.map embedTerm)
  | .tuple t fields => .tuple (embedTy t) (fields.map embedTerm)
  | .project t base i => .project (embedTy t) (embedTerm base) i
  | .heap t site len initial yes no =>
      .heap (embedTy t) site (embedTerm len) (embedTerm initial) (embedTerm yes) (embedTerm no)
  | .bufferLength t r => .bufferLength (embedTy t) r
  | .bufferRead t r i => .bufferRead (embedTy t) r (embedTerm i)
  | .bufferWrite t r i v => .bufferWrite (embedTy t) r (embedTerm i) (embedTerm v)
  | .callView t f r mode args => .callView (embedTy t) f r mode (args.map embedTerm)

def embedFunction (fn : ANL.Memory.Function) : Function :=
  ⟨fn.id, fn.name, fn.view, fn.params.map embedTy, embedTy fn.result, embedTerm fn.body⟩

/-- The schema/revision change explicitly; profile, ids, names and entry do not. -/
def embedProgram (p : ANL.Memory.Program) : Program :=
  ⟨"anl-core-v4", "anl-words-v1", p.profile, p.functions.map embedFunction, p.entry⟩

end ANL.Words
