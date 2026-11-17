import ANL.MemoryMachine

namespace ANL.Memory

def resourceModes (resources : Resources) : RCtx := resources.map Binding.mode

def Frame.Plain : Frame → Prop
  | .owner _ _ | .callReturn _ _ => False
  | _ => True

/-- Accounts for every live owner and links suspended callers without requiring their references disjoint. -/
inductive Layout : List Shape → Resources → List Frame → Prop where
  | nil : Layout [] [] []
  | plain : frame.Plain → Layout owners resources k → Layout owners resources (frame :: k)
  | owner : binding.mode = .owner → Layout owners resources k →
      Layout (⟨binding.ref, site, binding.length⟩ :: owners) (binding :: resources) (.owner binding site :: k)
  | callReturn : LoanOption.Valid loan caller.resources → Layout owners caller.resources k →
      Layout owners (loanResources loan) (.callReturn caller loan :: k)

inductive Frame.Typed (sigs : Signatures) :
    Frame → VCtx → Resources → Nat → Ty → VCtx → Resources → Nat → Ty → Prop where
  | bind : HasType sigs ((a, permission) :: Γ) (resourceModes resources) e b →
      Frame.Typed sigs (.bind permission e) Γ resources f a Γ resources f b
  | scope : Frame.Typed sigs .scope (binding :: Γ) resources f t Γ resources f t
  | assign : Γ[i]? = some (t, true) →
      Frame.Typed sigs (.assign i) Γ resources f t Γ resources f (.scalar .unit)
  | ifF : HasType sigs Γ (resourceModes resources) yes t → HasType sigs Γ (resourceModes resources) no t →
      Frame.Typed sigs (.ifF yes no) Γ resources f (.scalar .bool) Γ resources f t
  | unary : Frame.Typed sigs (.unary op) Γ resources f (.scalar op.input) Γ resources f (.scalar op.output)
  | left : HasType sigs Γ (resourceModes resources) e b → APL.FlatProducts.binaryType op a b = some t →
      Frame.Typed sigs (.left op e) Γ resources f a Γ resources f t
  | right : APL.FlatProducts.binaryType op v.type b = some t →
      Frame.Typed sigs (.right op v) Γ resources f b Γ resources f t
  | arguments : ArgsTyped sigs Γ (resourceModes resources) remaining rest →
      sigs[callee]? = some fn → fn.view = loanMode loan →
      fn.params = (values.map APL.FlatProducts.Val.type).reverse ++ a :: rest →
      LoanOption.Valid loan resources →
      Frame.Typed sigs (.arguments callee loan remaining values) Γ resources f a Γ resources f fn.result
  | callReturn : APL.FlatProducts.EnvTyped caller.env Δ → LoanOption.Valid loan caller.resources →
      Frame.Typed sigs (.callReturn caller loan) Γ (loanResources loan) f t Δ caller.resources caller.function t
  | condition : HasType sigs Γ (resourceModes resources) c (.scalar .bool) →
      HasType sigs Γ (resourceModes resources) b (.scalar .unit) →
      Frame.Typed sigs (.condition c b) Γ resources f (.scalar .bool) Γ resources f (.scalar .unit)
  | body : HasType sigs Γ (resourceModes resources) c (.scalar .bool) →
      HasType sigs Γ (resourceModes resources) b (.scalar .unit) →
      Frame.Typed sigs (.body c b) Γ resources f (.scalar .unit) Γ resources f (.scalar .unit)
  | fields {a : APL.Ty} {rest : List APL.Ty} {shape : APL.FlatProducts.Flat APL.Ty}
      {values : List APL.Val} :
      ArgsTyped sigs Γ (resourceModes resources) remaining (rest.map APL.FlatProducts.Ty.scalar) →
      (values.map APL.Val.type).reverse ++ a :: rest = shape.fields →
      Frame.Typed sigs (.fields remaining values) Γ resources f (.scalar a) Γ resources f (.tuple shape)
  | project : shape.fields[index]? = some t →
      Frame.Typed sigs (.project index) Γ resources f (.tuple shape) Γ resources f (.scalar t)
  | heapLength : site.function = f →
      HasType sigs Γ (resourceModes resources) init (.scalar .i64) →
      HasType sigs Γ (.owner :: resourceModes resources) yes t →
      HasType sigs Γ (resourceModes resources) no t →
      Frame.Typed sigs (.heapLength site init yes no) Γ resources f (.scalar .i64) Γ resources f t
  | heapInitial : site.function = f →
      HasType sigs Γ (.owner :: resourceModes resources) yes t →
      HasType sigs Γ (resourceModes resources) no t →
      Frame.Typed sigs (.heapInitial site n yes no) Γ resources f (.scalar .i64) Γ resources f t
  | owner : binding.mode = .owner → site.function = f →
      Frame.Typed sigs (.owner binding site) Γ (binding :: resources) f t Γ resources f t
  | readIndex : binding ∈ resources →
      Frame.Typed sigs (.readIndex binding) Γ resources f (.scalar .i64) Γ resources f (.scalar .i64)
  | writeIndex : binding ∈ resources → binding.mode.CanWrite →
      HasType sigs Γ (resourceModes resources) value (.scalar .i64) →
      Frame.Typed sigs (.writeIndex binding value) Γ resources f (.scalar .i64) Γ resources f (.scalar .unit)
  | writeValue : binding ∈ resources → binding.mode.CanWrite → index < binding.length →
      Frame.Typed sigs (.writeValue binding index) Γ resources f (.scalar .i64) Γ resources f (.scalar .unit)

inductive KontTyped (sigs : Signatures) : VCtx → Resources → Nat → List Frame → Ty → Ty → Prop where
  | nil : KontTyped sigs Γ resources f [] t t
  | cons : Frame.Typed sigs frame Γ resources f a Δ nextResources nextFunction b →
      KontTyped sigs Δ nextResources nextFunction rest b t →
      KontTyped sigs Γ resources f (frame :: rest) a t

inductive Control.Typed (sigs : Signatures) (Γ : VCtx) (resources : Resources) (f : Nat)
    (k : List Frame) : Control → Ty → Prop where
  | eval : HasType sigs Γ (resourceModes resources) e t → Control.Typed sigs Γ resources f k (.eval e) t
  | ret : Control.Typed sigs Γ resources f k (.ret value) value.type
  | lengthReady : site.function = f → value.type = .scalar .i64 →
      HasType sigs Γ (resourceModes resources) init (.scalar .i64) →
      HasType sigs Γ (.owner :: resourceModes resources) yes t →
      HasType sigs Γ (resourceModes resources) no t →
      Control.Typed sigs Γ resources f k (.lengthReady site value init yes no) t
  | allocate : site.function = f →
      HasType sigs Γ (.owner :: resourceModes resources) yes t →
      HasType sigs Γ (resourceModes resources) no t →
      Control.Typed sigs Γ resources f k (.allocate site n init yes no) t
  | readCheck : binding ∈ resources → value.type = .scalar .i64 →
      Control.Typed sigs Γ resources f k (.readCheck binding value) (.scalar .i64)
  | readCell : binding ∈ resources → index < binding.length →
      Control.Typed sigs Γ resources f k (.readCell binding index) (.scalar .i64)
  | writeCheck : binding ∈ resources → binding.mode.CanWrite → index.type = .scalar .i64 →
      HasType sigs Γ (resourceModes resources) value (.scalar .i64) →
      Control.Typed sigs Γ resources f k (.writeCheck binding index value) (.scalar .unit)
  | store : binding ∈ resources → binding.mode.CanWrite → index < binding.length →
      Control.Typed sigs Γ resources f k (.store binding index value) (.scalar .unit)
  | invoke : sigs[callee]? = some fn → fn.view = loanMode loan →
      fn.params = (values.map APL.FlatProducts.Val.type).reverse → LoanOption.Valid loan resources →
      Control.Typed sigs Γ resources f k (.invoke callee loan values) fn.result
  | grant : sigs[callee]? = some fn → fn.view = loanMode loan →
      fn.params = (values.map APL.FlatProducts.Val.type).reverse → LoanOption.Valid loan resources →
      Control.Typed sigs Γ resources f k (.grant callee loan values) fn.result
  | close : k = .owner binding site :: rest →
      Control.Typed sigs Γ resources f k (.close binding site value) value.type
  | revoke : k = .callReturn caller loan :: rest →
      Control.Typed sigs Γ resources f k (.revoke value) value.type
  | restore : k = .callReturn caller loan :: rest →
      Control.Typed sigs Γ resources f k (.restore value) value.type
  | trap : Control.Typed sigs Γ resources f k (.trap kind) t

/-- Static continuation typing and concrete ownership layout are independent of execution. -/
inductive State.Typed (p : Program) : State → Ty → Prop where
  | intro : APL.FlatProducts.EnvTyped s.current.env Γ →
      Control.Typed p.signatures Γ s.current.resources s.current.function s.kont s.control a →
      KontTyped p.signatures Γ s.current.resources s.current.function s.kont a t →
      Layout (s.world.owners.map Owner.shape) s.current.resources s.kont → s.world.Valid p.profile →
      State.Typed p s t

end ANL.Memory
