import APL.ProductRuntime

namespace APL.ProductFlow
open ProductLogic
open ProductAnnotations (Instantiated)
open VCG (Model)

inductive CheckKey where
  | body
  | invariant (site : List Nat) (preservation : Bool) (clause : Nat)
  | precondition (clause : Nat)
  | postcondition (clause : Nat)
  deriving DecidableEq, Repr

structure Check where
  key : CheckKey
  guard : Formula
  required : Formula
  deriving Repr

structure Analysis (α : Type) where
  value : α
  env : List SymValue
  normal : Formula
  checks : List Check
  next : Nat
  deriving Repr

def single (value : α) (env : List SymValue) (normal : Formula) (next : Nat) : Analysis α :=
  ⟨value, env, normal, [], next⟩

def sequence (first : Analysis α) (later : Analysis β) : Analysis β :=
  { later with checks := first.checks ++ later.checks }

def addCheck (key : CheckKey) (guard required : Formula) (flow : Analysis α) : Analysis α :=
  { flow with checks := flow.checks ++ [⟨key, guard, required⟩] }

def disjunction (left right : Formula) : Formula := .not (.and (.not left) (.not right))

def mergeFlow (condition : SymTerm) (yes no : Analysis SymValue) : Option (Analysis SymValue) := do
  let value ← merge condition yes.value no.value
  let env ← mergeEnv condition yes.env no.env
  return ⟨value, env, disjunction yes.normal no.normal, yes.checks ++ no.checks, no.next⟩

def asScalar : SymValue → Option SymScalar
  | .scalar value => some value
  | .tuple _ => none

def asBoolean : SymValue → Option SymTerm
  | .scalar value => if value.type = .bool then some value.term else none
  | .tuple _ => none

def tupleSymbol (values : List SymValue) : Option SymValue := do
  construct (← values.mapM asScalar)

def updateSymbols : List SymValue → Nat → SymValue → Option (List SymValue)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value => (updateSymbols rest index value).map (head :: ·)

def invariantChecks (site : List Nat) (preservation : Bool) (path : Formula)
    (clauses : List ProductAnnotations.Clause) : List Check :=
  clauses.zipIdx.map fun (clause, index) =>
    ⟨.invariant site preservation index, path, clause.truth⟩

def arguments
    (generate : ProductAnnotations.Term → List SymValue → Formula → Nat → List Nat → Option (Analysis SymValue)) :
    List ProductAnnotations.Term → List SymValue → Formula → Nat → List Nat → Nat →
      Option (Analysis (List SymValue))
  | [], env, path, next, _, _ => some (single [] env path next)
  | arg :: args, env, path, next, site, index => do
      let first ← generate arg env path next (site ++ [index])
      let rest ← arguments generate args first.env first.normal first.next site (index + 1)
      return ⟨first.value :: rest.value, rest.env, rest.normal, first.checks ++ rest.checks, rest.next⟩

def analyze (fs : ProductAnnotations.Functions) :
    Nat → FlatProducts.Ctx → ProductAnnotations.Term → List SymValue → Formula → Nat → List Nat →
      Option (Analysis SymValue)
  | 0, _, _, _, _, _, _ => none
  | height + 1, context, term, env, path, next, site => do
      let _ ← FlatProducts.infer (ProductAnnotations.signatures fs) context term.erase
      match term with
      | .lit value => return single (runtimeLiteral value) env path next
      | .local index => return single (← env[index]?) env path next
      | .letE value body =>
          let type ← FlatProducts.infer (ProductAnnotations.signatures fs) context value.erase
          let first ← analyze fs height context value env path next (site ++ [0])
          let body ← analyze fs height ((type, false) :: context) body (first.value :: first.env)
            first.normal first.next (site ++ [1])
          let _ ← body.env.head?
          return sequence first { body with env := body.env.tail }
      | .letMut value body =>
          let type ← FlatProducts.infer (ProductAnnotations.signatures fs) context value.erase
          let first ← analyze fs height context value env path next (site ++ [0])
          let body ← analyze fs height ((type, true) :: context) body (first.value :: first.env)
            first.normal first.next (site ++ [1])
          let _ ← body.env.head?
          return sequence first { body with env := body.env.tail }
      | .assign index value =>
          let first ← analyze fs height context value env path next (site ++ [0])
          let final ← updateSymbols first.env index first.value
          return { first with value := runtimeLiteral (.scalar .unit), env := final }
      | .ifE condition yes no =>
          let test ← analyze fs height context condition env path next (site ++ [0])
          let condition ← asBoolean test.value
          let yes ← analyze fs height context yes test.env (.and test.normal (.holds condition))
            test.next (site ++ [1])
          let no ← analyze fs height context no test.env (.and test.normal (.holds (.unary .not condition)))
            yes.next (site ++ [2])
          return sequence test (← mergeFlow condition yes no)
      | .unary op arg =>
          let first ← analyze fs height context arg env path next (site ++ [0])
          let value ← runtimeUnary op first.value
          return addCheck .body first.normal value.defined { first with value := value.value }
      | .binary op left right =>
          let left ← analyze fs height context left env path next (site ++ [0])
          if op = .and ∨ op = .or then
            let condition ← asBoolean left.value
            let execute := if op = .and then Formula.holds condition else .holds (.unary .not condition)
            let skip := if op = .and then Formula.holds (.unary .not condition) else .holds condition
            let right ← analyze fs height context right left.env (.and left.normal execute)
              left.next (site ++ [1])
            let skipped := single left.value left.env (.and left.normal skip) right.next
            let merged ← (if op = .and then mergeFlow condition right skipped else mergeFlow condition skipped right)
            return sequence left merged
          else
            let right ← analyze fs height context right left.env left.normal left.next (site ++ [1])
            let value ← runtimeBinary op left.value right.value
            return sequence left (addCheck .body right.normal value.defined { right with value := value.value })
      | .call function args =>
          let actuals ← arguments (analyze fs height context) args env path next site 0
          let fn ← fs[function]?
          if actuals.value.map SymValue.type = fn.params then
            let required ← ProductAnnotations.requiresVC actuals.value fn.requires
            let body ← analyze fs height (FlatProducts.immutable fn.params.reverse) fn.body
              actuals.value.reverse actuals.normal actuals.next (site ++ [args.length])
            return sequence actuals (addCheck .body actuals.normal (.and required.defined required.truth)
              { body with env := actuals.env })
          else none
      | .tuple fields =>
          let captured ← arguments (analyze fs height context) fields env path next site 0
          let value ← tupleSymbol captured.value
          return { captured with value := value }
      | .project base index =>
          let base ← analyze fs height context base env path next (site ++ [0])
          let field ← project base.value index
          return { base with value := .scalar field }
      | .whileE clauses condition body =>
          if clauses.isEmpty then none else do
            let initial ← ProductAnnotations.assertionsVC [] none env clauses
            let head ← freshHead context env next
            let invariant ← ProductAnnotations.assertionsVC [] none head.symbols clauses
            let headPath := Formula.and path (.and head.domain (ProductAnnotations.clauseConjunction invariant))
            let conditionResult ← analyze fs height context condition head.symbols headPath head.next (site ++ [0])
            let condition ← asBoolean conditionResult.value
            let body ← analyze fs height context body conditionResult.env
              (.and conditionResult.normal (.holds condition)) conditionResult.next (site ++ [1])
            let preservation ← ProductAnnotations.assertionsVC [] none body.env clauses
            return ⟨runtimeLiteral (.scalar .unit), conditionResult.env,
              .and conditionResult.normal (.holds (.unary .not condition)),
              invariantChecks site false path initial ++ conditionResult.checks ++ body.checks ++
                invariantChecks site true body.normal preservation, body.next⟩

def group (checks : List Check) : Formula :=
  checks.foldr (fun check rest => .and (.imp check.guard check.required) rest) (.truth true)

theorem group_exact : (group checks).Holds model ↔
    ∀ check ∈ checks, check.guard.Holds model → check.required.Holds model := by
  induction checks with
  | nil => simp [group, Formula.Holds]
  | cons check checks ih =>
    change ((check.guard.Holds model → check.required.Holds model) ∧ (group checks).Holds model) ↔ _
    rw [ih]
    simp

def ValidFrom (bound : Nat) (model : Model) (checks : List Check) : Prop :=
  ∀ extended, AgreeBelow bound model extended → (group checks).Holds extended

def Covered (bound : Nat) (model : Model) (analysis : Analysis SymValue)
    (value : FlatProducts.Val) (env : FlatProducts.Env) : Prop :=
  ∃ extended, AgreeBelow bound model extended ∧ analysis.normal.Holds extended ∧
    RuntimeDenotes extended analysis.value value ∧ RuntimeEnvRep extended analysis.env env

def ArgsCovered (bound : Nat) (model : Model) (analysis : Analysis (List SymValue))
    (values : FlatProducts.Env) (env : FlatProducts.Env) : Prop :=
  ∃ extended, AgreeBelow bound model extended ∧ analysis.normal.Holds extended ∧
    RuntimeEnvRep extended analysis.value values ∧ RuntimeEnvRep extended analysis.env env

end APL.ProductFlow
