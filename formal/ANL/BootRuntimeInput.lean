import ANL.BootRuntimeCore

namespace ANL.Boot.Runtime
open ANL.Words

inductive Scoped (p : ANL.Boot.Program) : Landmark → Prop where
  | before : 0 < k → p.functions[ident]? = some (.primitive row) → Scoped p (.beforePrimitive k ident)
  | after : 0 < k → p.functions[ident]? = some (.primitive row) → Scoped p (.afterPrimitive k ident)
  | park : p.functions[p.entries.boot.function]? = some (.defined d) →
      designatedTail d.function.body = some path →
      Scoped p (.bootPark ⟨p.entries.boot.function, Origin.tailPath path⟩)

def checkScoped (p : ANL.Boot.Program) : Landmark → Bool
  | .beforePrimitive k ident | .afterPrimitive k ident =>
      decide (0 < k) && match p.functions[ident]? with | some (.primitive _) => true | _ => false
  | .bootPark origin => match p.functions[p.entries.boot.function]? with
      | some (.defined d) => match designatedTail d.function.body with
          | some path => decide (origin = ⟨p.entries.boot.function, Origin.tailPath path⟩)
          | none => false
      | _ => false

structure DeliveryValid (p : ANL.Boot.Program) (d : Delivery) : Prop where
  scope : Scoped p d.landmark
  cause : d.scause < wordModulus
  pc : d.sepc < wordModulus
  auxiliary : d.stval < wordModulus

structure InputValid (p : ANL.Boot.Program) (env : Environment) : Prop where
  status : env.sstatus < wordModulus
  interrupts : env.sie < wordModulus
  hart : env.hart < wordModulus
  opaqueDtb : env.opaqueDtb < wordModulus
  reads : ∀ value ∈ env.reads, value < byteModulus
  delivery : ∀ d, env.delivery = some d → DeliveryValid p d

def checkDelivery (p : ANL.Boot.Program) (d : Delivery) : Bool :=
  checkScoped p d.landmark && decide (d.scause < wordModulus ∧ d.sepc < wordModulus ∧ d.stval < wordModulus)

def checkInput (p : ANL.Boot.Program) (env : Environment) : Bool :=
  decide (env.sstatus < wordModulus ∧ env.sie < wordModulus ∧ env.hart < wordModulus ∧ env.opaqueDtb < wordModulus) &&
  env.reads.all (fun value => decide (value < byteModulus)) &&
  match env.delivery with | none => true | some d => checkDelivery p d

/-- Explicit post-validation API handle; raw environment and machine states stay proof-free. -/
structure ValidatedInput (p : ANL.Boot.Program) where
  raw : Environment
  valid : InputValid p raw

end ANL.Boot.Runtime
