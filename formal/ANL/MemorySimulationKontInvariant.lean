import ANL.MemorySimulationContinuation

namespace ANL.Memory.Simulation
open Lowering

set_option linter.unusedVariables false

def SupplyLE (a b : Supply) : Prop := a.nextTemp ≤ b.nextTemp ∧ a.nextSlot ≤ b.nextSlot

def afterTemp (supply : Supply) (destination : Mir.Temp) : Supply :=
  {supply with nextTemp := destination.id + 1}

/-- Static frontiers for pending code; block return and caller return restore their own frontiers. -/
def KontCode.Limits (code : KontCode offset locals ids k result captures) : Supply → Prop := by
  induction code with
  | @nil offset locals ids =>
      exact fun supply => True
  | @yield offset locals ids k mk captures value parent ih =>
      exact fun supply => ih supply
  | @destination offset locals ids k d tail mk captures parent ih =>
      exact fun supply => supply.nextTemp ≤ d.id ∧ ih (afterTemp supply d)
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      exact fun supply => SupplyLE snapshot.bound supply ∧ ih snapshot.bound
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ ih next
  | @scopeValue offset locals ids k target captures value parent ih =>
      exact fun supply => ih supply
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      exact fun supply => supply.nextTemp ≤ start.nextTemp ∧ supply.nextSlot ≤ slot.id ∧ start.nextSlot = slot.id + 1 ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      exact fun supply => ih supply
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      exact fun supply => supply.nextTemp ≤ d.id ∧ ih (afterTemp supply d)
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      exact fun supply => supply.nextTemp ≤ d.id ∧ ih (afterTemp supply d)
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      exact fun supply => supply.nextTemp ≤ d.id ∧ ih (afterTemp supply d)
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @logicalRight op prior offset locals ids k target captures logical parent ih =>
      exact fun supply => ih supply
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ ih next
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ ih next
  | @project offset locals ids k d tail mk captures index value parent ih =>
      exact fun supply => supply.nextTemp ≤ d.id ∧ ih (afterTemp supply d)
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ ih next
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      exact fun supply => ih supply
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      exact fun supply => supply.nextTemp ≤ d.id ∧ ih (afterTemp supply d)
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      exact fun supply => ih supply
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      exact fun supply => ih saved.bound
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      exact fun supply => SupplyLE supply start ∧ next.nextTemp ≤ d.id ∧ ih (afterTemp next d)

/-- Concrete storage obligations for each current or suspended continuation context. -/
def KontCode.StoreSafe (code : KontCode offset locals ids k result captures) :
    Supply → ANL.Memory.Activation → Mir.Activation → Prop := by
  induction code with
  | @nil offset locals ids =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target [] ∧ (True)
  | @yield offset locals ids k mk captures value parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @destination offset locals ids k d tail mk captures parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @blockEnd locals offset ids k mk captures snapshot parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (TempAgreement snapshot.bound.nextTemp target.temps snapshot.values ∧ SupplyLE snapshot.bound bound ∧ ih snapshot.bound source {target with temps := snapshot.values})
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @scopeValue offset locals ids k target captures value parent ih =>
      exact fun bound source target =>
        ActivationRel (.value value :: locals) ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound {source with env := source.env.tail} target)
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @scopeMutable offset locals ids k mk captures slot parent ih =>
      exact fun bound source target =>
        ActivationRel (.mutable slot :: locals) ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound {source with env := source.env.tail} {target with slots := target.slots.tail})
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @unary offset locals ids k d tail mk captures op value parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target (.value left prior :: captures) ∧ (ih bound source target)
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @logicalRight op prior offset locals ids k target captures logical parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @project offset locals ids k d tail mk captures index value parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @owner offset locals ids k mk captures rid resource site parent ih =>
      exact fun bound source target =>
        ActivationRel locals (rid :: ids) source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound {source with resources := source.resources.tail} {target with resources := target.resources.tail})
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target (.resource rid resource :: captures) ∧ (ih bound source target)
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target (.resource rid resource :: captures) ∧ (ih bound source target)
  | @writeValue offset locals ids k mk captures resource index parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target captures ∧ (ih bound source target)
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target (.resource rid sourceLoan.source :: .arguments done prior :: captures) ∧ (ih bound source target)
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target (.arguments done (prior.map APL.FlatProducts.Val.scalar) :: captures) ∧ (ih bound source target)
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target [] ∧ (ih saved.bound saved.source saved.target)
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih =>
      exact fun bound source target =>
        ActivationRel locals ids source target ∧ Below bound target ∧
        CapturesHold target (.arguments done prior :: captures) ∧ (ih bound source target)

def FunctionOffset (p : Program) (function offset : Nat) : Prop :=
  ∃ fn, p.functions[function]? = some fn ∧ offset = Lowering.viewOffset fn.view

def ScopedSites (offset : Nat) (ids : List Nat) (e : Term) : Prop :=
  e.heapSites.Nodup ∧ ∀ site ∈ e.heapSites, site + offset ∉ ids

/-- Function offsets of suspended callers are retained through callee execution. -/
def KontCode.Offsets (code : KontCode offset locals ids k result captures) (p : Program) : Prop := by
  induction code with
  | @nil offset locals ids => exact True
  | @yield offset locals ids k mk captures value parent ih => exact ih
  | @destination offset locals ids k d tail mk captures parent ih => exact ih
  | @blockEnd locals offset ids k mk captures snapshot parent ih => exact ih
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih => exact ih
  | @scopeValue offset locals ids k target captures value parent ih => exact ih
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih => exact ih
  | @scopeMutable offset locals ids k mk captures slot parent ih => exact ih
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih => exact ih
  | @unary offset locals ids k d tail mk captures op value parent ih => exact ih
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih => exact ih
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih => exact ih
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih => exact ih
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih => exact ih
  | @logicalRight op prior offset locals ids k target captures logical parent ih => exact ih
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih => exact ih
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih => exact ih
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih => exact ih
  | @project offset locals ids k d tail mk captures index value parent ih => exact ih
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih => exact ih
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih => exact ih
  | @owner offset locals ids k mk captures rid resource site parent ih => exact ih
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih => exact ih
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih => exact ih
  | @writeValue offset locals ids k mk captures resource index parent ih => exact ih
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih => exact ih
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih => exact ih
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih => exact FunctionOffset p saved.source.function saved.offset ∧ ih
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih => exact ih

/-- Only live resource-name clashes matter here; repeated descriptors in distinct activations remain allowed. -/
def KontCode.Sites (code : KontCode offset locals ids k result captures) : Prop := by
  induction code with
  | @nil offset locals ids => exact True
  | @yield offset locals ids k mk captures value parent ih => exact ih
  | @destination offset locals ids k d tail mk captures parent ih => exact ih
  | @blockEnd locals offset ids k mk captures snapshot parent ih => exact ih
  | @bindValue offset value locals ids body start fragment next k tail mk captures lowered parent ih => exact ScopedSites offset ids body ∧ ih
  | @scopeValue offset locals ids k target captures value parent ih => exact ih
  | @bindMutable offset slot locals ids body start fragment next k d tail mk captures value lowered parent ih => exact ScopedSites offset ids body ∧ ih
  | @scopeMutable offset locals ids k mk captures slot parent ih => exact ih
  | @assign locals index offset ids k d tail mk captures value slot lookup parent ih => exact ih
  | @unary offset locals ids k d tail mk captures op value parent ih => exact ih
  | @binaryLeft op offset locals ids right start fragment next k d tail mk captures left notAnd notOr lowered parent ih => exact ScopedSites offset ids right ∧ ih
  | @binaryRight op offset locals ids k d tail mk captures prior value left notAnd notOr parent ih => exact ih
  | @andLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih => exact ScopedSites offset ids right ∧ ih
  | @orLeft offset locals ids right start fragment next k d tail mk captures left lowered parent ih => exact ScopedSites offset ids right ∧ ih
  | @logicalRight op prior offset locals ids k target captures logical parent ih => exact ih
  | @branch offset locals ids yes start left middle no right next k d tail mk captures condition leftLowered rightLowered parent ih => exact ScopedSites offset ids yes ∧ ScopedSites offset ids no ∧ ih
  | @condition offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih => exact ScopedSites offset ids condition ∧ ScopedSites offset ids body ∧ ih
  | @body offset locals ids condition start cf middle body bf next k mk captures conditionLowered bodyLowered parent ih => exact ScopedSites offset ids condition ∧ ScopedSites offset ids body ∧ ih
  | @project offset locals ids k d tail mk captures index value parent ih => exact ih
  | @heapLength offset locals ids initializer start initialCode second yes yesCode third no noCode next k d tail mk captures site length initialLowered yesLowered noLowered parent ih => exact site.heap + offset ∉ ids ∧ ScopedSites offset ids initializer ∧ ScopedSites offset ((site.heap + offset) :: ids) yes ∧ ScopedSites offset ids no ∧ ih
  | @heapInitial offset locals ids yes start yesCode middle no noCode next k mk captures site length yesLowered noLowered parent ih => exact site.heap + offset ∉ ids ∧ ScopedSites offset ((site.heap + offset) :: ids) yes ∧ ScopedSites offset ids no ∧ ih
  | @owner offset locals ids k mk captures rid resource site parent ih => exact ih
  | @readIndex offset locals ids k d tail mk captures resource index rid parent ih => exact ih
  | @writeIndex offset locals ids value start fragment next k d tail mk captures resource index rid lowered parent ih => exact ScopedSites offset ids value ∧ ih
  | @writeValue offset locals ids k mk captures resource index parent ih => exact ih
  | @viewArguments offset locals ids remaining start rest next k d tail mk captures f sourceLoan prior current rid done lowered parent ih => exact (∀ e ∈ remaining, ScopedSites offset ids e) ∧ ih
  | @fields offset locals ids remaining start rest next k d tail mk captures prior current done lowered parent ih => exact (∀ e ∈ remaining, ScopedSites offset ids e) ∧ ih
  | @caller captures k mk offset locals ids sourceLoan saved captured parent ih => exact ih
  | @arguments offset locals ids remaining start rest next k d tail mk captures f prior current done lowered parent ih => exact (∀ e ∈ remaining, ScopedSites offset ids e) ∧ ih

end ANL.Memory.Simulation
