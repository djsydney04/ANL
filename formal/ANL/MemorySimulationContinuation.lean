import ANL.MemorySimulationRank

namespace ANL.Memory.Simulation
open Lowering

/-- Splice only the straight instruction spine, leaving nested blocks untouched. -/
def plug (instructions : List Mir.Instruction) (tail : Mir.Block) : Mir.Block :=
  instructions.foldr (fun instruction rest => .next instruction.destination instruction.operation rest) tail

inductive ResultTarget where
  | captured (value : Mir.Temp) (tail : Mir.Block) (kont : List Mir.Frame)
  | returned (kont : List Mir.Frame)

inductive Capture where
  | value (temp : Mir.Temp) (value : Val)
  | arguments (temps : List Mir.Temp) (reversed : List Val)
  | resource (rid : Nat) (value : ANL.Memory.Binding)

def Capture.Holds (a : Mir.Activation) : Capture → Prop
  | .value temp captured => a.temp temp = some captured
  | .arguments temps reversed => Captured a temps reversed
  | .resource rid captured => a.resource rid = some (binding captured)

def CapturesHold (a : Mir.Activation) (captures : List Capture) : Prop :=
  ∀ capture ∈ captures, capture.Holds a

/-- A syntax-level compiled continuation graph. No node asserts execution equivalence. -/
inductive KontCode : Nat → Locals → List Nat → List ANL.Memory.Frame → ResultTarget → List Capture → Type where
  | nil : KontCode offset locals ids [] (.returned []) []
  | yield : KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals ids k (.captured value (.yield value) mk) captures
  | destination : KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids k (.returned (.instruction d tail :: mk)) captures
  | blockEnd (snapshot : SavedTemps locals) : KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals ids k (.returned (.blockEnd snapshot.values :: mk)) captures
  | bindValue : term offset (.value value :: locals) ids body start = some (fragment, next) →
      KontCode offset locals ids k (.captured fragment.value tail mk) captures →
      KontCode offset locals ids (.bind false body :: k)
        (.captured value (plug fragment.instructions tail) mk) captures
  | scopeValue : KontCode offset locals ids k target captures →
      KontCode offset (.value value :: locals) ids (.scope :: k) target captures
  | bindMutable : term offset (.mutable slot :: locals) ids body start = some (fragment, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.bind true body :: k)
        (.captured value (.next d (.mutableScope slot value fragment.block) tail) mk) captures
  | scopeMutable : KontCode offset locals ids k (.returned mk) captures →
      KontCode offset (.mutable slot :: locals) ids (.scope :: k)
        (.returned (.slotScope slot.id :: mk)) captures
  | assign : locals[index]? = some (.mutable slot) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.assign index :: k)
        (.captured value (.next d (.store slot value) tail) mk) captures
  | unary : KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.unary op :: k)
        (.captured value (.next d (.unary op value) tail) mk) captures
  | binaryLeft : op ≠ .and → op ≠ .or →
      term offset locals ids right start = some (fragment, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.left op right :: k)
        (.captured left (plug fragment.instructions (.next d (.binary op left fragment.value) tail)) mk) captures
  | binaryRight : op ≠ .and → op ≠ .or →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.right op prior :: k)
        (.captured value (.next d (.binary op left value) tail) mk) (.value left prior :: captures)
  | andLeft : term offset locals ids right start = some (fragment, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.left .and right :: k)
        (.captured left (.next d (.branch left fragment.block (.yield left)) tail) mk) captures
  | orLeft : term offset locals ids right start = some (fragment, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.left .or right :: k)
        (.captured left (.next d (.branch left (.yield left) fragment.block) tail) mk) captures
  | logicalRight : (op = .and ∧ prior = .scalar (.bool true)) ∨ (op = .or ∧ prior = .scalar (.bool false)) →
      KontCode offset locals ids k target captures →
      KontCode offset locals ids (.right op prior :: k) target captures
  | branch : term offset locals ids yes start = some (left, middle) →
      term offset locals ids no middle = some (right, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.ifF yes no :: k)
        (.captured condition (.next d (.branch condition left.block right.block) tail) mk) captures
  | condition : term offset locals ids condition start = some (cf, middle) →
      term offset locals ids body middle = some (bf, next) →
      KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals ids (.condition condition body :: k)
        (.returned (.condition cf.block bf.block :: mk)) captures
  | body : term offset locals ids condition start = some (cf, middle) →
      term offset locals ids body middle = some (bf, next) →
      KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals ids (.body condition body :: k)
        (.returned (.body cf.block bf.block :: mk)) captures
  | project : KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.project index :: k)
        (.captured value (.next d (.project value index) tail) mk) captures
  | heapLength : term offset locals ids initializer start = some (initialCode, second) →
      term offset locals ((site.heap + offset) :: ids) yes second = some (yesCode, third) →
      term offset locals ids no third = some (noCode, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.heapLength site initializer yes no :: k)
        (.captured length (.next d (.heapScope site.heap (site.heap + offset) length
          initialCode.block yesCode.block noCode.block) tail) mk) captures
  | heapInitial : term offset locals ((site.heap + offset) :: ids) yes start = some (yesCode, middle) →
      term offset locals ids no middle = some (noCode, next) →
      KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals ids (.heapInitial site length yes no :: k)
        (.returned (.heapInitial site (site.heap + offset) length yesCode.block noCode.block :: mk)) captures
  | owner : KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals (rid :: ids) (.owner resource site :: k)
        (.returned (.owner rid (binding resource) site :: mk)) captures
  | readIndex : KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.readIndex resource :: k)
        (.captured index (.next d (.bufferRead rid index) tail) mk) (.resource rid resource :: captures)
  | writeIndex : term offset locals ids value start = some (fragment, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.writeIndex resource value :: k)
        (.captured index (.next d (.bufferWrite rid index fragment.block) tail) mk) (.resource rid resource :: captures)
  | writeValue : KontCode offset locals ids k (.returned mk) captures →
      KontCode offset locals ids (.writeValue resource index :: k)
        (.returned (.writeValue (binding resource) index :: mk)) captures
  | arguments : arguments offset locals ids remaining start = some (rest, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.arguments f none remaining prior :: k)
        (.captured current (plug rest.instructions (.next d (.call f (done ++ current :: rest.values)) tail)) mk)
        (.arguments done prior :: captures)
  | viewArguments : arguments offset locals ids remaining start = some (rest, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.arguments f (some sourceLoan) remaining prior :: k)
        (.captured current (plug rest.instructions
          (.next d (.callView f rid sourceLoan.mode (done ++ current :: rest.values)) tail)) mk)
        (.resource rid sourceLoan.source :: .arguments done prior :: captures)
  | fields : arguments offset locals ids remaining start = some (rest, next) →
      KontCode offset locals ids k (.captured d tail mk) captures →
      KontCode offset locals ids (.fields remaining prior :: k)
        (.captured current (plug rest.instructions (.next d (.tuple (done ++ current :: rest.values)) tail)) mk)
        (.arguments done (prior.map APL.FlatProducts.Val.scalar) :: captures)
  | caller (saved : Suspended) : CapturesHold saved.target captures →
      KontCode saved.offset saved.locals saved.ids k (.returned mk) captures →
      KontCode offset locals ids (.callReturn saved.source sourceLoan :: k)
        (.returned (.callReturn saved.target (sourceLoan.map loan) :: mk)) []

end ANL.Memory.Simulation
