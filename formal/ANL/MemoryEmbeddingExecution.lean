import ANL.MemoryEmbeddingTyping

namespace ANL.Memory.Embedding

variable {p : Program} {responses : Responses} {world : World}

theorem steps_trans (first : Steps p responses start middle) (last : Steps p responses middle finish) :
    Steps p responses start finish := by
  induction first with
  | refl => exact last
  | head step _ ih => exact .head step (ih last)

theorem scalar_fields_steps (head : APL.Val) (rest reversed : List APL.Val)
    (a : Activation) (k : List Frame) (world : World) :
    Steps p responses
      ⟨.eval (scalarLiteral head), a, .fields (rest.map scalarLiteral) reversed :: k, world⟩
      (resume (APL.FlatProducts.construct (reversed.reverse ++ head :: rest)) a k world) := by
  induction rest generalizing head reversed with
  | nil =>
      simpa only [List.reverse_cons, List.map_nil, scalarLiteral] using
        (Steps.head (Step.lit (t := .scalar head.type))
          (Steps.head (Step.fieldsDone (v := head) (values := reversed)) Steps.refl))
  | cons next rest ih =>
      apply Steps.head Step.lit
      apply Steps.head Step.fieldNext
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih next (head :: reversed)

theorem literal_steps (value : Val) (a : Activation) (k : List Frame) (world : World) :
    Steps p responses ⟨.eval (literal value), a, k, world⟩ ⟨.ret value, a, k, world⟩ := by
  cases value with
  | scalar value => exact .head .lit .refl
  | tuple fields =>
      cases hs : fields.fields with
      | nil => have positive := fields.nonempty; simp [hs] at positive
      | cons head rest =>
          simp only [literal, hs, List.map_cons]
          apply Steps.head Step.tupleFirst
          have finish := scalar_fields_steps (p := p) (responses := responses) head rest [] a k world
          simpa only [List.reverse_nil, List.nil_append, ← hs,
            APL.FlatProducts.construct, APL.FlatProducts.Flat.make_fields, resume] using finish

theorem resume_related (result : APL.FlatProducts.Result) (related : KontRel oldKont newKont) :
    StateRel world (APL.FlatProducts.resume result env oldKont)
      (resume result ⟨functionId, env, []⟩ newKont world) := by
  cases result with
  | value value => exact .ret related
  | trap kind => exact .trap
  | invalid => exact .invalid

theorem step_simulation (functions : FunctionsRel fs p)
    (transition : APL.FlatProducts.Step fs old next) (related : StateRel world old start) :
    ∃ finish, Steps p responses start finish ∧ StateRel world next finish := by
  cases transition with
  | lit =>
      cases related with
      | eval expression kont =>
          cases expression
          exact ⟨_, literal_steps _ _ _ _, .ret kont⟩
  | localFound lookup =>
      cases related with
      | eval expression kont =>
          cases expression
          exact ⟨_, .head (.localFound lookup) .refl, .ret kont⟩
  | localMissing lookup =>
      cases related with
      | eval expression kont =>
          cases expression
          exact ⟨_, .head (.localMissing lookup) .refl, .invalid⟩
  | letEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | letE value body => exact ⟨_, .head .letEval .refl, .eval value (.cons (.bind body) kont)⟩
  | letMutEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | letMut value body => exact ⟨_, .head .letMutEval .refl, .eval value (.cons (.bind body) kont)⟩
  | bindReturn =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | bind body => exact ⟨_, .head .bindReturn .refl, .eval body (.cons .scope tail)⟩
  | scopeReturn =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head (.scopeReturn rfl) .refl, .ret tail⟩
  | scopeMissing =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame _ =>
              cases frame
              exact ⟨_, .head (.scopeMissing rfl) .refl, .invalid⟩
  | assignEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | assign value => exact ⟨_, .head .assignEval .refl, .eval value (.cons .assign kont)⟩
  | assignReturn updated =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head (.assignReturn updated) .refl, .ret tail⟩
  | assignMissing missing =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame _ =>
              cases frame
              exact ⟨_, .head (.assignMissing missing) .refl, .invalid⟩
  | ifEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | ifE condition yes no => exact ⟨_, .head .ifEval .refl, .eval condition (.cons (.ifF yes no) kont)⟩
  | ifTrue =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | ifF yes _ => exact ⟨_, .head .ifTrue .refl, .eval yes tail⟩
  | ifFalse =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | ifF _ no => exact ⟨_, .head .ifFalse .refl, .eval no tail⟩
  | ifInt | ifUnit | ifTuple =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame _ =>
              cases frame
              exact ⟨_, .head (.ifWrong (by simp [APL.FlatProducts.Val.type, APL.Val.type])) .refl, .invalid⟩
  | unaryEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | unary operand => exact ⟨_, .head .unaryEval .refl, .eval operand (.cons .unary kont)⟩
  | unaryReturn =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head .unaryReturn .refl, resume_related _ tail⟩
  | binaryEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | binary left right => exact ⟨_, .head .binaryEval .refl, .eval left (.cons (.left right) kont)⟩
  | short short =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head (.short short) .refl, .ret tail⟩
  | rightEval next =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | left right => exact ⟨_, .head (.rightEval next) .refl, .eval right (.cons .right tail)⟩
  | binaryReturn =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head .binaryReturn .refl, resume_related _ tail⟩
  | callEmpty =>
      cases related with
      | eval expression kont =>
          cases expression with
          | call args =>
              cases args
              exact ⟨_, .head .call .refl, .invoke kont⟩
  | callFirst =>
      cases related with
      | eval expression kont =>
          cases expression with
          | call args =>
              cases args with
              | cons head tail => exact ⟨_, .head .call .refl, .eval head (.cons (.arguments tail) kont)⟩
  | argumentNext =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | arguments args =>
                  cases args with
                  | cons head rest => exact ⟨_, .head .argumentReturn .refl, .eval head (.cons (.arguments rest) tail)⟩
  | argumentsDone =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | arguments args =>
                  cases args
                  exact ⟨_, .head .argumentReturn .refl, .invoke tail⟩
  | invoke lookup =>
      cases related with
      | invoke kont =>
          obtain ⟨translated, lookup', mode, expression⟩ := functions.found _ _ lookup
          exact ⟨_, .head (.invoke lookup' mode) (.head (.grant lookup') .refl),
            .eval expression (.cons .callReturn kont)⟩
  | invalidFunction missing =>
      cases related with
      | invoke _ => exact ⟨_, .head (.invokeMissing (functions.missing _ missing)) .refl, .invalid⟩
  | callReturn =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head .callResult (.head .revoke (.head .restore .refl)), .ret tail⟩
  | whileEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | whileE condition body =>
              exact ⟨_, .head .whileEval .refl, .eval condition (.cons (.condition condition body) kont)⟩
  | whileTrue =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | condition condition body =>
                  exact ⟨_, .head .whileTrue .refl, .eval body (.cons (.body condition body) tail)⟩
  | whileFalse =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head .whileFalse .refl, .ret tail⟩
  | whileInt | whileUnit | whileTuple =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame _ =>
              cases frame
              exact ⟨_, .head (.whileWrong (by simp [APL.FlatProducts.Val.type, APL.Val.type])) .refl, .invalid⟩
  | whileAgain =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | body condition body =>
                  exact ⟨_, .head .whileAgain .refl, .eval condition (.cons (.condition condition body) tail)⟩
  | bodyInt | bodyBool | bodyTuple =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame _ =>
              cases frame
              exact ⟨_, .head (.bodyWrong (by simp [APL.FlatProducts.Val.type, APL.Val.type])) .refl, .invalid⟩
  | tupleEmpty =>
      cases related with
      | eval expression kont =>
          cases expression with
          | tuple fields =>
              cases fields
              exact ⟨_, .head .tupleEmpty .refl, .invalid⟩
  | tupleFirst =>
      cases related with
      | eval expression kont =>
          cases expression with
          | tuple fields =>
              cases fields with
              | cons head tail => exact ⟨_, .head .tupleFirst .refl, .eval head (.cons (.fields tail) kont)⟩
  | fieldNext =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | fields fields =>
                  cases fields with
                  | cons head rest => exact ⟨_, .head .fieldNext .refl, .eval head (.cons (.fields rest) tail)⟩
  | fieldsDone =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame with
              | fields fields =>
                  cases fields
                  exact ⟨_, .head .fieldsDone .refl, resume_related _ tail⟩
  | fieldTuple =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame _ =>
              cases frame
              exact ⟨_, .head .fieldTuple .refl, .invalid⟩
  | projectEval =>
      cases related with
      | eval expression kont =>
          cases expression with
          | project base => exact ⟨_, .head .projectEval .refl, .eval base (.cons .project kont)⟩
  | projectReturn =>
      cases related with
      | ret kont =>
          cases kont with
          | cons frame tail =>
              cases frame
              exact ⟨_, .head .projectReturn .refl, resume_related _ tail⟩

theorem StateRel.world_eq (related : StateRel world old translated) : translated.world = world := by
  cases related <;> rfl

theorem StateRel.terminal (related : StateRel world old translated)
    (terminal : APL.FlatProducts.Terminal old) : Terminal translated := by
  cases terminal with
  | value =>
      cases related with
      | ret kont => cases kont; exact .value
  | trap => cases related; exact .trap

theorem steps_simulation (functions : FunctionsRel fs p)
    (execution : APL.FlatProducts.Steps fs old last) (related : StateRel world old start) :
    ∃ finish, Steps p responses start finish ∧ StateRel world last finish := by
  induction execution generalizing start with
  | refl => exact ⟨start, .refl, related⟩
  | head transition _ ih =>
      obtain ⟨middle, first, related⟩ := step_simulation functions transition related
      obtain ⟨finish, rest, last⟩ := ih related
      exact ⟨finish, steps_trans first rest, last⟩

theorem finite_value (functions : FunctionsRel fs p)
    (execution : APL.FlatProducts.Steps fs old (.ret value env []))
    (related : StateRel world old start) :
    ∃ functionId, Steps p responses start ⟨.ret value, ⟨functionId, env, []⟩, [], world⟩ := by
  obtain ⟨finish, execution, related⟩ := steps_simulation functions execution related
  cases related with
  | ret kont => cases kont; exact ⟨_, execution⟩

theorem finite_trap (functions : FunctionsRel fs p)
    (execution : APL.FlatProducts.Steps fs old (.trap kind))
    (related : StateRel world old start) :
    ∃ functionId env kont,
      Steps p responses start ⟨.trap (.scalar kind), ⟨functionId, env, []⟩, kont, world⟩ := by
  obtain ⟨finish, execution, related⟩ := steps_simulation functions execution related
  cases related
  exact ⟨_, _, _, execution⟩

theorem run_embedding (functions : FunctionsRel fs p)
    (completed : APL.FlatProducts.run fs oldBudget old = some last)
    (terminal : APL.FlatProducts.Terminal last) (related : StateRel world old start) :
    ∃ newBudget finish, execute p responses newBudget start = .completed finish ∧
      StateRel world last finish ∧ Terminal finish ∧ finish.world = world := by
  obtain ⟨finish, execution, lastRelated⟩ :=
    steps_simulation functions (APL.FlatProducts.run_sound completed).1 related
  have terminal := lastRelated.terminal terminal
  obtain ⟨budget, completed⟩ := execute_completed_complete execution (.inl terminal)
  exact ⟨budget, finish, completed, lastRelated, terminal, lastRelated.world_eq⟩

theorem expression_value (fs : OldFunctions) (profile : Profile) (entry functionId : Nat)
    (context : VCtx) (e : OldTerm)
    (execution : APL.FlatProducts.Steps fs (.eval e env []) (.ret value finalEnv [])) :
    ∃ finalFunctionId, Steps (program fs profile entry) responses
      ⟨.eval (term (APL.FlatProducts.signatures fs) context e), ⟨functionId, env, []⟩, [], world⟩
      ⟨.ret value, ⟨finalFunctionId, finalEnv, []⟩, [], world⟩ := by
  exact finite_value (functions_related fs profile entry) execution (.eval (term_related ..) .nil)

theorem expression_trap (fs : OldFunctions) (profile : Profile) (entry functionId : Nat)
    (context : VCtx) (e : OldTerm)
    (execution : APL.FlatProducts.Steps fs (.eval e env []) (.trap kind)) :
    ∃ finalFunctionId finalEnv kont, Steps (program fs profile entry) responses
      ⟨.eval (term (APL.FlatProducts.signatures fs) context e), ⟨functionId, env, []⟩, [], world⟩
      ⟨.trap (.scalar kind), ⟨finalFunctionId, finalEnv, []⟩, kont, world⟩ := by
  exact finite_trap (functions_related fs profile entry) execution (.eval (term_related ..) .nil)

theorem initial_related (fs : OldFunctions) (profile : Profile) (entry : Nat) :
    StateRel .initial (.invoke entry [] [] []) (initial (program fs profile entry)) := by
  exact .invoke .nil

theorem entry_outcome (fs : OldFunctions) (profile : Profile) (entry : Nat)
    (execution : APL.FlatProducts.Steps fs (.invoke entry [] [] []) last)
    (terminal : APL.FlatProducts.Terminal last) :
    ∃ finish, Steps (program fs profile entry) responses (initial (program fs profile entry)) finish ∧
      StateRel .initial last finish ∧ Terminal finish ∧ finish.world = .initial := by
  obtain ⟨finish, execution, related⟩ :=
    steps_simulation (functions_related fs profile entry) execution (initial_related ..)
  exact ⟨finish, execution, related, related.terminal terminal, related.world_eq⟩

theorem checked_entry_run (fs : OldFunctions) (profile : Profile) (entry : Nat)
    (typed : APL.FlatProducts.WellTyped fs) (lookup : fs[entry]? = some fn)
    (nullary : fn.params = [])
    (completed : APL.FlatProducts.run fs oldBudget (.invoke entry [] [] []) = some last) :
    ∃ newBudget finish, execute (program fs profile entry) responses newBudget
      (initial (program fs profile entry)) = .completed finish ∧
      StateRel .initial last finish ∧ Terminal finish ∧ finish.world = .initial := by
  have safe := APL.FlatProducts.finite_run_safe typed (APL.FlatProducts.entry_typed lookup nullary) completed
  have terminal : APL.FlatProducts.Terminal last := by
    rcases safe with ⟨value, env, rfl, _⟩ | ⟨kind, rfl⟩
    · exact .value
    · exact .trap
  exact run_embedding (functions_related fs profile entry) completed terminal (initial_related ..)

end ANL.Memory.Embedding
