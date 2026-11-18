import ANL.WordsSimulationKontInvariant
import ANL.WordsSimulationFinite

namespace ANL.Words.Simulation

open ANL.Memory
open Lowering

structure Placed (p : Program) (code : KontCode offset locals ids k target captures)
    (before after : Supply) (source : ANL.Words.Activation) (destination : Mir.Activation) : Prop where
  range : SupplyLE before after
  storage : code.StoreSafe before source destination
  limits : code.Limits after
  offsets : code.Offsets p
  sites : code.Sites
  currentOffset : FunctionOffset p source.function offset

inductive AtResult (a : Mir.Activation) (v : Val) : ResultTarget → Mir.Control → List Mir.Frame → Prop where
  | captured : a.temp temp = some v → AtResult a v (.captured temp tail k) (.sequence tail) k
  | returned : AtResult a v (.returned k) (.ret v) k

/-- Relates actual machine states using compiled syntax and concrete storage, never an execution-equivalence premise. -/
inductive Related (p : Program) : ANL.Words.State → Mir.State → Prop where
  | eval (code : KontCode offset locals ids k (.captured fragment.value tail mk) captures) :
      term offset locals ids e start = some (fragment, next) →
      ScopedSites offset ids e → Placed p code start next a b →
      Related p ⟨.eval e, a, k, w⟩ ⟨.sequence (plug fragment.instructions tail), b, mk, w⟩
  | ret (code : KontCode offset locals ids k target captures) :
      Placed p code before after a b → AtResult b v target targetControl mk →
      Related p ⟨.ret v, a, k, w⟩ ⟨targetControl, b, mk, w⟩
  | lengthReady (code : KontCode offset locals ids k (.returned mk) captures) :
      term offset locals ids initializer start = some (initialCode, second) →
      term offset locals ((site.heap + offset) :: ids) yes second = some (yesCode, third) →
      term offset locals ids no third = some (noCode, next) →
      SupplyLE before start → site.heap + offset ∉ ids →
      ScopedSites offset ids initializer → ScopedSites offset ((site.heap + offset) :: ids) yes →
      ScopedSites offset ids no → Placed p code before next a b →
      Related p ⟨.lengthReady site value initializer yes no, a, k, w⟩
        ⟨.lengthReady site (site.heap + offset) value initialCode.block yesCode.block noCode.block, b, mk, w⟩
  | allocate (code : KontCode offset locals ids k (.returned mk) captures) :
      term offset locals ((site.heap + offset) :: ids) yes start = some (yesCode, middle) →
      term offset locals ids no middle = some (noCode, next) →
      SupplyLE before start → site.heap + offset ∉ ids →
      ScopedSites offset ((site.heap + offset) :: ids) yes → ScopedSites offset ids no →
      Placed p code before next a b →
      Related p ⟨.allocate site length value yes no, a, k, w⟩
        ⟨.allocate site (site.heap + offset) length value yesCode.block noCode.block, b, mk, w⟩
  | readCheck (code : KontCode offset locals ids k (.returned mk) captures) :
      Placed p code before after a b →
      Related p ⟨.readCheck resource value, a, k, w⟩ ⟨.readCheck (binding resource) value, b, mk, w⟩
  | readCell (code : KontCode offset locals ids k (.returned mk) captures) :
      Placed p code before after a b →
      Related p ⟨.readCell resource index, a, k, w⟩ ⟨.readCell (binding resource) index, b, mk, w⟩
  | writeCheck (code : KontCode offset locals ids k (.returned mk) captures) :
      term offset locals ids value start = some (fragment, next) →
      SupplyLE before start → ScopedSites offset ids value → Placed p code before next a b →
      Related p ⟨.writeCheck resource index value, a, k, w⟩
        ⟨.writeCheck (binding resource) index fragment.block, b, mk, w⟩
  | store (code : KontCode offset locals ids k (.returned mk) captures) :
      Placed p code before after a b →
      Related p ⟨.store resource index value, a, k, w⟩ ⟨.store (binding resource) index value, b, mk, w⟩
  | invoke (code : KontCode offset locals ids k (.returned mk) captures) :
      Placed p code before after a b →
      Related p ⟨.invoke functionId sourceLoan reversed, a, k, w⟩
        ⟨.invoke functionId (sourceLoan.map loan) reversed.reverse, b, mk, w⟩
  | grant (code : KontCode offset locals ids k (.returned mk) captures) :
      Placed p code before after a b →
      Related p ⟨.grant functionId sourceLoan reversed, a, k, w⟩
        ⟨.grant functionId (sourceLoan.map loan) reversed.reverse, b, mk, w⟩
  | close (code : KontCode offset locals ids (.owner resource site :: k)
      (.returned (.owner rid (binding resource) site :: mk)) captures) :
      Placed p code before after a b →
      Related p ⟨.close resource site value, a, .owner resource site :: k, w⟩
        ⟨.close rid (binding resource) site value, b, .owner rid (binding resource) site :: mk, w⟩
  | revoke (code : KontCode offset locals ids (.callReturn sourceCaller sourceLoan :: k)
      (.returned (.callReturn targetCaller (sourceLoan.map loan) :: mk)) captures) :
      Placed p code before after a b →
      Related p ⟨.revoke value, a, .callReturn sourceCaller sourceLoan :: k, w⟩
        ⟨.revoke value, b, .callReturn targetCaller (sourceLoan.map loan) :: mk, w⟩
  | restore (code : KontCode offset locals ids (.callReturn sourceCaller sourceLoan :: k)
      (.returned (.callReturn targetCaller (sourceLoan.map loan) :: mk)) captures) :
      Placed p code before after a b →
      Related p ⟨.restore value, a, .callReturn sourceCaller sourceLoan :: k, w⟩
        ⟨.restore value, b, .callReturn targetCaller (sourceLoan.map loan) :: mk, w⟩
  | trap (code : KontCode offset locals ids k (.returned mk) captures) :
      Placed p code before after a b →
      Related p ⟨.trap kind, a, k, w⟩ ⟨.trap (Simulation.trap kind), b, mk, w⟩

/-- Exact final value/trap plus the concrete current/suspended-state relation. -/
def FinalRelated (p : Program) (source : ANL.Words.State) (target : Mir.State) : Prop :=
  Related p source target ∧ Mir.Terminal target ∧
  ((∃ value, source.control = .ret value ∧ source.kont = [] ∧
      target.control = .ret value ∧ target.kont = []) ∨
   (∃ kind, source.control = .trap kind ∧ target.control = .trap (trap kind)))

def Canonical (p : Program) (q : Mir.Program) : Prop :=
  WellFormedProgram p ∧ Lowering.program p = some q

end ANL.Words.Simulation
