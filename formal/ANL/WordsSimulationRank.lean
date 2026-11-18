import ANL.WordsSimulationAdmin

namespace ANL.Words.Simulation

open ANL.Memory

/-- Remaining source syntax, including argument-list spine nodes. -/
def termWeight : Term → Nat
  | .word _ _ _ | .lit _ _ | .local _ _ | .bufferLength _ _ => 3
  | .letE _ a b | .letMut _ a b | .whileE _ a b | .binary _ _ a b | .bufferWrite _ _ a b =>
      3 + termWeight a + termWeight b
  | .convert _ _ _ a | .assign _ _ a | .unary _ _ a | .project _ a _ | .bufferRead _ _ a => 3 + termWeight a
  | .ifE _ c a b => 3 + termWeight c + termWeight a + termWeight b
  | .call _ _ args | .tuple _ args | .callView _ _ _ _ args =>
      3 + (args.map termWeight).sum + args.length
  | .heap _ _ len init yes no => 3 + termWeight len + termWeight init + termWeight yes + termWeight no

def frameWeight : ANL.Words.Frame → Nat
  | .bind _ body => termWeight body + 2
  | .scope | .assign _ | .unary _ | .right _ _ | .project _ | .readIndex _ => 1
  | .ifF yes no => termWeight yes + termWeight no + 2
  | .left _ right => termWeight right + 2
  | .arguments _ _ rest _ | .fields rest _ => (rest.map termWeight).sum + rest.length + 1
  | .heapLength _ init yes no => termWeight init + termWeight yes + termWeight no + 2
  | .writeIndex _ value => termWeight value + 2
  | _ => 1

def coreRank (s : ANL.Words.State) : Nat :=
  (match s.control with | .eval e => termWeight e | _ => 0) + (s.kont.map frameWeight).sum

/-- Source steps that may disappear during flattening. Semantic operations need not be silent. -/
inductive CoreSilent (p : Program) (responses : Responses) : ANL.Words.State → ANL.Words.State → Prop where
  | localFound : a.env[index]? = some v →
      CoreSilent p responses ⟨.eval (.local t index), a, k, w⟩ ⟨.ret v, a, k, w⟩
  | letEval : CoreSilent p responses ⟨.eval (.letE t e b), a, k, w⟩ ⟨.eval e, a, .bind false b :: k, w⟩
  | letMutEval : CoreSilent p responses ⟨.eval (.letMut t e b), a, k, w⟩ ⟨.eval e, a, .bind true b :: k, w⟩
  | assignEval : CoreSilent p responses ⟨.eval (.assign t index e), a, k, w⟩ ⟨.eval e, a, .assign index :: k, w⟩
  | ifEval : CoreSilent p responses ⟨.eval (.ifE t c y n), a, k, w⟩ ⟨.eval c, a, .ifF y n :: k, w⟩
  | convertEval : CoreSilent p responses ⟨.eval (.convert t mode target e), a, k, w⟩ ⟨.eval e, a, .convert mode target :: k, w⟩
  | unaryEval : CoreSilent p responses ⟨.eval (.unary t op e), a, k, w⟩ ⟨.eval e, a, .unary op :: k, w⟩
  | binaryEval : CoreSilent p responses ⟨.eval (.binary t op e b), a, k, w⟩ ⟨.eval e, a, .left op b :: k, w⟩
  | call : CoreSilent p responses ⟨.eval (.call t f args), a, k, w⟩ (beginArguments f none args [] a k w)
  | tupleFirst : CoreSilent p responses ⟨.eval (.tuple t (e :: rest)), a, k, w⟩
      ⟨.eval e, a, .fields rest [] :: k, w⟩
  | projectEval : CoreSilent p responses ⟨.eval (.project t e index), a, k, w⟩ ⟨.eval e, a, .project index :: k, w⟩
  | heapEval : CoreSilent p responses ⟨.eval (.heap t h len init yes no), a, k, w⟩
      ⟨.eval len, a, .heapLength ⟨a.function, h⟩ init yes no :: k, w⟩
  | readEval : a.resources[index]? = some b →
      CoreSilent p responses ⟨.eval (.bufferRead t index e), a, k, w⟩
        ⟨.eval e, a, .readIndex b :: k, w⟩
  | writeEval : a.resources[index]? = some b → b.mode.CanWrite →
      CoreSilent p responses ⟨.eval (.bufferWrite t index e v), a, k, w⟩
        ⟨.eval e, a, .writeIndex b v :: k, w⟩
  | callView : a.resources[index]? = some b → b.mode.CanLend mode →
      CoreSilent p responses ⟨.eval (.callView t f index mode args), a, k, w⟩
        (beginArguments f (some ⟨b, mode⟩) args [] a k w)
  | bindValue : CoreSilent p responses ⟨.ret v, a, .bind false b :: k, w⟩
      ⟨.eval b, {a with env := v :: a.env}, .scope :: k, w⟩
  | scopeReturn : a.env = cell :: rest → CoreSilent p responses ⟨.ret v, a, .scope :: k, w⟩
      ⟨.ret v, {a with env := rest}, k, w⟩
  | rightEval : ANL.Words.shortCircuit op v = false →
      CoreSilent p responses ⟨.ret v, a, .left op e :: k, w⟩ ⟨.eval e, a, .right op v :: k, w⟩
  | argumentReturn {capturedLoan : Option ANL.Memory.Loan} : CoreSilent p responses ⟨.ret v, a, .arguments f capturedLoan rest values :: k, w⟩
      (beginArguments f capturedLoan rest (v :: values) a k w)
  | fieldNext : CoreSilent p responses ⟨.ret (.scalar v), a, .fields (e :: rest) values :: k, w⟩
      ⟨.eval e, a, .fields rest (v :: values) :: k, w⟩
  | logicalReturn : ANL.Words.binary op left v = .value result → (op = (.legacy .and) ∨ op = (.legacy .or)) →
      CoreSilent p responses ⟨.ret v, a, .right op left :: k, w⟩ ⟨.ret result, a, k, w⟩

theorem CoreSilent.step (h : CoreSilent p responses s t) : ANL.Words.Step p responses s t := by
  cases h with
  | localFound h => exact .localFound h
  | letEval => exact .letEval
  | letMutEval => exact .letMutEval
  | assignEval => exact .assignEval
  | ifEval => exact .ifEval
  | convertEval => exact .convertEval
  | unaryEval => exact .unaryEval
  | binaryEval => exact .binaryEval
  | call => exact .call
  | tupleFirst => exact .tupleFirst
  | projectEval => exact .projectEval
  | heapEval => exact .heapEval
  | readEval h => exact .readEval h
  | writeEval h hp => exact .writeEval h hp
  | callView h hp => exact .callView h hp
  | bindValue => exact .bindReturn
  | scopeReturn h => exact .scopeReturn h
  | rightEval h => exact .rightEval h
  | argumentReturn => exact .argumentReturn
  | fieldNext => exact .fieldNext
  | @logicalReturn op left v result a k w h _ =>
      change Step p responses _ (resume (.value result) a k w)
      rw [← h]
      exact .binaryReturn

theorem CoreSilent.rank (h : CoreSilent p responses s t) : coreRank t < coreRank s := by
  cases h <;> simp only [coreRank, termWeight, frameWeight, List.map_cons, List.sum_cons]
  all_goals try omega
  all_goals cases ‹List Term› <;> simp [beginArguments, frameWeight] <;> omega

end ANL.Words.Simulation
