# Checked theorem inventory

Semantic revisions: `m1-2026-11-16`, `local-state-2026-11-17` and `flat-products-2026-11-17`. Proof tool: Lean 4.36.0, official release
commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The checking command is
`formal/check.sh` from the repository root with the pinned Lean tools on `PATH`.
It rebuilds all source, runs `APL/Audit.lean`, and replays the semantic modules
with `leanchecker`. The latter uses the Lean kernel; it is not an independently
implemented proof checker.

The inventory's variables quantify over the formal syntax and states. `Γ` is a
list of scalar types, newest binding first, in the original judgments. State
contexts also record binding permissions; the separate flat-products context
admits bounded scalar tuple types. `e` is untyped expression syntax;
`HasType Γ e t` is a separately defined inductive judgment. `s.Typed t` checks the
expression, captured environments, and every continuation frame in a machine
state. `Step` is an inductive small-step relation without a fuel parameter.
`Steps` is its finite reflexive transitive closure. `run` returns `none` when its
transition budget expires.

`i64` values are mathematical integers paired with a proof of membership in
`[-2^63, 2^63-1]`. Literal bounds are thus a representation invariant; the importer
must establish them when accepting a decimal string. Expressions themselves are
not intrinsically typed. Ill-typed operations and unbound locals can be
constructed and are rejected by the inference function.

## Foundational obligations

| Obligation | Theorem | Quantified statement and assumptions | Coverage |
| --- | --- | --- | --- |
| FM-01 | `APL.type_unique` | `HasType Γ e a` and `HasType Γ e b` imply `a = b`. No production-checker assumption. | Every expression constructor and every scalar operator. |
| FM-02 | `APL.preservation` | `s.Typed t` and `Step s s'` imply `s'.Typed t`. Trap states are explicitly typed at every result type. | Expression evaluation and return states, captured environments, every continuation frame, short-circuit transitions, and arithmetic traps. |
| FM-03 | `APL.relational_progress` | `s.Typed t` implies `Terminal s` or a successor under `Step`. A terminal is a value with an empty continuation or a defined trap. Invalid states have no typing constructor. | The same expression machine, including intermediate configurations. Closed expressions start with an empty environment and continuation. |
| FM-04 | `APL.run_sound` | `run fuel s = some last` implies `Steps s last` and `step last = none`. No typing assumption is needed for correspondence. | Every successful finite machine run, including invalid untyped inputs. |
| FM-04 | `APL.run_complete` | `Steps s last` and `step last = none` imply existence of a fuel budget for which `run fuel s = some last`. | Every finite terminal reduction in the expression relation. No claim for exhausted fuel or infinite reductions. |
| FM-05 | Program typing, safety and evaluator theorems below | Extends FM-01 through FM-04 to well-typed global functions and recursive calls. Finite evaluator completeness quantifies sufficient depth and fuel. | The resolved scalar function model; no termination or fixed-CLI-bound completeness claim. |
| Safety corollary | `APL.closed_safety` | `HasType [] e t` and a successful `run` from `eval e [] []` imply a final value of type `t` with empty continuation, or one of the two defined traps. | The full expression fragment. It does not assert trap freedom or termination. |

## Supporting checked theorems

All names below are also checked by the axiom audit. Their hypotheses are the
formal judgments or equations stated here, with no hypothesis about external
code or assumed compiler correctness.

| Theorem | Statement and assumptions |
| --- | --- |
| `APL.infer_complete` | `HasType Γ e t` implies `infer Γ e = some t`. |
| `APL.infer_sound` | `infer Γ e = some t` implies `HasType Γ e t`. This certifies the Lean expression checker, not the Rust checker or JSON reader. |
| `APL.checked_typed` | Checked mathematical-integer conversion returns an `i64` value or arithmetic-overflow trap. |
| `APL.division_typed` | For bounded operands, division/remainder returns an `i64` value or a defined trap. This theorem is type safety, not a separate proof of the quotient's mathematical identities. |
| `APL.unary_typed` | An operand of the operator's input type produces its output type or a trap. |
| `APL.binary_typed` | If the binary operator table accepts the operand types with result `t`, the primitive result has type `t` or is a trap. |
| `APL.lookup_typed` | Successful context lookup in the mapped environment implies a corresponding environment value of that type. |
| `APL.resume_typed` | A typed primitive result and typed continuation produce a typed machine state. |
| `APL.shortCircuit_typed` | For an accepted binary operator, taking the short-circuit case returns a value of the operator's result type. |
| `APL.step_preserves` | The executable single-step function preserves state typing whenever it returns a successor. |
| `APL.progress` | Every typed state is terminal or the executable single-step function returns a successor. |
| `APL.step_complete` | Every inductive `Step s s'` is implemented by `step s = some s'`. |
| `APL.step_sound` | Every `step s = some s'` has an inductive `Step s s'` derivation. |
| `APL.steps_preserve` | A finite sequence of relation steps preserves the initial state type. |
| `APL.run_safety` | A successful run from a typed state returns a typed terminal state. |

## Recursive program guarantees

`Program.HasType sigs Γ e t` and `Program.ArgsTyped sigs Γ es ts` are mutually
inductive declarative judgments over untyped program syntax. `signatures fs`
projects the parameter and result types from the actual function table.
`WellTyped fs` requires every function body to have its declared result type
under its reversed parameter context and the complete signature table. It does
not assume safe execution, termination, or any property of the Rust checker.

Program state typing includes evaluation, value return, invocation and trap
states. Every continuation frame is typed. An argument frame checks the saved
caller environment, remaining expressions, the reverse prefix of evaluated
arguments, and the selected function signature. Invocation passes only the
reversed argument values into the callee; caller environments remain in their
continuation frames. The result type of every frame matches the next frame.

The following theorems extend FM-01 through FM-03 and the checker guarantees to
forward and mutually recursive functions. All operators, short circuits, traps,
locals, lets, conditionals, argument transitions and call transitions are covered.
No proof assumes termination. The actual bounded evaluator's finite-result
soundness and the existence of sufficient depth and fuel for finite reductions
are also checked below. Together these discharge FM-05 for this resolved scalar
function model.

| Theorem | Quantified statement and assumptions |
| --- | --- |
| `APL.Program.infer_complete` | `HasType sigs Γ e t` implies `infer sigs Γ e = some t`, including ordered argument checking. |
| `APL.Program.infer_sound` | `infer sigs Γ e = some t` implies `HasType sigs Γ e t`. This proves the total Lean program checker, not the JSON reader or Rust checker. |
| `APL.Program.type_unique` | Two declarative typings of the same term under the same signatures and local context have equal result types. |
| `APL.Program.signatures_lookup` | Looking up a function in `fs` successfully finds its parameter/result pair in `signatures fs`. |
| `APL.Program.signatures_lookup_inv` | A successful signature lookup identifies an actual function at the same index with exactly those parameter/result types. |
| `APL.Program.checked_functions` | If `Program.infer` accepts every body with its declared result under the actual table's signatures and reversed parameters, then `WellTyped fs`. This is the precise checker-to-table bridge; the wire reader's construction of that table is not proved. |
| `APL.Program.resume_typed` | A typed primitive outcome and typed continuation yield a typed program state; arithmetic traps remain permitted. |
| `APL.Program.preservation` | `WellTyped fs`, `s.Typed (signatures fs) t`, and `Step fs s s'` imply `s'.Typed (signatures fs) t`. Covers all 22 transition constructors. |
| `APL.Program.progress` | `s.Typed (signatures fs) t` implies `Terminal s` or a successor under `Step fs`. Body typing is not needed for this single-step theorem; preservation requires it. |
| `APL.Program.steps_preserve` | `WellTyped fs`, a typed initial state and any finite `Program.Steps fs` derivation imply a final state of the same type. |
| `APL.Program.safety` | Under those same assumptions, the reached state has the initial type and is terminal or has a successor. Applies to every finite prefix even when execution diverges. |
| `APL.Program.no_invalid` | No finite reduction from a typed state under `WellTyped fs` reaches `Program.State.invalid`. |
| `APL.Program.closed_safety` | A closed declaratively typed term under `WellTyped fs`, any finite reduction from empty environment/continuation, and absence of a next step imply a value of the declared type with empty continuation or one of the defined traps. Does not assert that a finite terminal reduction exists. |
| `APL.Program.entry_typed` | An actual zero-parameter function gives a typed initial invocation state with its declared result type. |
| `APL.Program.entry_safety` | `WellTyped fs`, a zero-parameter entry lookup and any finite reduction from that invocation imply a typed terminal state or a next step. |

## Finite program evaluator soundness

These theorems refer to the actual `APL.Program.eval` used by the program CLI.
They quantify over any depth and fuel budgets, actual functions, untyped program
terms and value environments. The soundness proofs require no typing hypothesis.
Every successful argument evaluation follows source order and accumulates reversed
callee values while preserving the caller's environment and continuation.

The private trace-composition predicate imposes no condition for `resourceLimit`;
none of the public soundness theorems accepts that result as its premise. A resource
limit establishes neither divergence nor a finite terminal reduction. The
completeness theorems below establish the existence of sufficient model budgets;
the fixed CLI depth of 256 is not a completeness promise.

| Theorem | Quantified statement and assumptions |
| --- | --- |
| `APL.Program.eval_value_sound` | `eval fs depth env e fuel = .ok (v, remaining)` implies `Steps fs (.eval e env k) (.ret v k)` for every continuation `k`. No typing assumption. |
| `APL.Program.eval_trap_sound` | `eval fs depth env e fuel = .error (.trap kind)` implies `Steps fs (.eval e env k) (.trap kind)` for every continuation. No typing assumption. |
| `APL.Program.eval_invalid_sound` | `eval fs depth env e fuel = .error .invalid` implies `Steps fs (.eval e env k) .invalid` for every continuation. Covers invalid untyped inputs as well. |
| `APL.Program.eval_value_typed` | Under `WellTyped fs` and `HasType (signatures fs) (env.map Val.type) e t`, a successful actual evaluation returning `v` implies `v.type = t`. |
| `APL.Program.eval_ne_invalid` | Under those same function-table and term-typing assumptions, actual evaluation cannot return `.error .invalid`. Values, defined arithmetic traps and resource exhaustion remain possible. |

## Finite program evaluator completeness

These theorems concern the same actual `Program.eval`, with no typing hypothesis.
Their premises are finite `Program.Steps` reductions from an evaluation state with
an empty continuation. The environment may be any list of values. Their
conclusions quantify over both depth and fuel; they do not assume or prove that
an arbitrary recursive program terminates.

The proof counts relation steps and establishes determinism of all 22 transition
constructors. Successful evaluator results cannot increase remaining fuel, and
their traces bound consumed fuel. Resource exhaustion yields a trace prefix at
least as long as the smaller initial depth/fuel budget. A known terminal trace of
length `n` cannot have a longer prefix. Choosing depth and fuel `n + 1` therefore
excludes resource exhaustion, and deterministic terminal-result uniqueness forces
the exact value, trap or invalid outcome. This argument does not change any
execution rule, fuel charge, or CLI limit.

| Theorem | Quantified statement and assumptions |
| --- | --- |
| `APL.Program.eval_value_complete` | `Steps fs (.eval e env []) (.ret v [])` implies existence of `depth`, `fuel` and `remaining` with `eval fs depth env e fuel = .ok (v, remaining)`. No typing assumption. |
| `APL.Program.eval_trap_complete` | `Steps fs (.eval e env []) (.trap kind)` implies existence of `depth` and `fuel` with `eval fs depth env e fuel = .error (.trap kind)`. No typing assumption. |
| `APL.Program.eval_invalid_complete` | `Steps fs (.eval e env []) .invalid` implies existence of `depth` and `fuel` with `eval fs depth env e fuel = .error .invalid`. Includes untyped invalid inputs. |

Together with finite soundness, these give correspondence in both directions for
finite program outcomes. The fixed CLI depth bound of 256 can still reject a
terminating computation that needs a larger model depth. Increasing fuel alone
does not establish completeness at that fixed depth.

## Call-free verification-condition foundation

The FM-07 foundation uses the existing untyped `Program.Term` and unchanged
`Program.eval`. `VCG.MVal` holds unbounded mathematical integers, booleans and
unit. `SymTerm` is a concrete symbolic expression syntax; its independently
defined interpreter has partial division/remainder and left-to-right Boolean
short circuit. `Formula` is a concrete syntax for truth, expression truth,
definedness, Boolean type, integer range, conjunction, negation and implication.
Its interpretation does not refer to program execution or the desired safety
conclusion.

`VCG.wp e syms post` recursively constructs an optional formula. It substitutes
locals through a symbolic environment and passes symbolic results to a syntactic
continuation. It preserves obligations for discarded expressions and adds each
checked intermediate range. Runtime division and remainder both reject zero and
the machine minimum divided by `-1`; specification arithmetic is unbounded and
permits the latter mathematical pair. Branch and Boolean operand obligations are
guarded. Calls return `none`, including calls in an unselected branch. The
primitive encoding lemmas prove that valid generated guards produce an actual
runtime value with the represented mathematical result.

`EnvRep model syms env` relates symbolic terms to concrete bounded runtime values.
`PostHolds model post v` witnesses a symbolic term denoting `v` whose exact
continuation formula was generated and holds. `Safe post outcome` requires the
postcondition for a returned value, permits a resource limit, and excludes both
arithmetic traps and invalid outcomes. The generator is a syntax transformation;
none of these soundness theorems defines it as the semantic property to be proved.

`Spec` has distinct parameter and result references with an independent
mathematical interpreter. `instantiate_sound` proves their symbolic substitution.
`requiresVC` generates a Boolean-definedness condition for each clause before
using that clause's truth to guard later clauses; a clause cannot use its own or
a later clause's truth. It also generates the full precondition conjunction.
`generateContract` builds those formulas and the body's postcondition VC with
canonical parameter symbols, reversing only the runtime parameter environment.
A postcondition is checked independently, without assuming another postcondition.

`Accepted types vc` requires three separate mathematical facts: precondition
definedness for all typed parameter values, existence of a typed satisfying
input, and validity of the body formula whenever the preconditions hold. These
are logical-obligation assumptions, not assumed execution safety. They do not
assert that Rust generation or a solver result establishes their truth. A
constant-true postcondition expresses the arithmetic-safety-only case.

| Theorem | Quantified statement and assumptions |
| --- | --- |
| `APL.VCG.EnvRep.lookup` | A symbolic lookup in related environments identifies a corresponding concrete runtime value denoted by that symbol. |
| `APL.VCG.wp_eval_sound` | `wp e syms post = some formula`, `EnvRep model syms env`, and `formula.Holds model` imply `Safe (PostHolds model post)` for the actual `Program.eval fs depth env e fuel`, for any functions, depth and fuel. No execution-safety or termination premise. |
| `APL.VCG.wp_value` | Under those generator, environment and validity assumptions, any returned value has a `PostHolds` witness. |
| `APL.VCG.wp_no_trap` | Under those assumptions, actual evaluation cannot return either defined arithmetic trap. |
| `APL.VCG.wp_no_invalid` | Under those assumptions, actual evaluation cannot return invalid. |
| `APL.VCG.wp_steps_value` | Under those assumptions, any finite `Program.Steps` reduction from `eval e env []` to `ret v []` satisfies `PostHolds`. Uses the checked evaluator-completeness theorem. |
| `APL.VCG.wp_steps_no_trap` | Under those assumptions, no finite reduction from `eval e env []` reaches an arithmetic trap. |
| `APL.VCG.wp_steps_no_invalid` | Under those assumptions, no finite reduction from `eval e env []` reaches invalid. |
| `APL.VCG.instantiate_sound` | Successful specification substitution, related parameter environments and a related optional result imply equality of symbolic evaluation and independent specification evaluation, including undefined outcomes. |
| `APL.VCG.spec_post_sound` | A `PostHolds` witness for the generated specification continuation implies that the concrete returned value makes that specification defined and true under the represented parameters. |
| `APL.VCG.requires_vc_sound` | Successfully generated precondition formulas under related parameters are equivalent to independent ordered definedness and conjunction-of-truth judgments. |
| `APL.VCG.contract_eval_sound` | Successful `generateContract`, `Accepted` logical obligations, typed parameter values and true source preconditions imply that actual evaluation in the reversed parameter environment returns a value satisfying the independent specification, or reaches a resource limit. Trap and invalid outcomes are excluded. |
| `APL.VCG.contract_preconditions_defined` | Successful generation and `Accepted` imply ordered precondition definedness for every typed parameter environment. |
| `APL.VCG.contract_nonvacuous` | Successful generation and `Accepted` imply a typed parameter environment satisfying the source preconditions. Contradictory preconditions cannot yield accepted verification. |
| `APL.VCG.contract_steps_value` | Under the contract theorem's generation, acceptance, typing and precondition assumptions, any finite returned value satisfies the independent specification. |
| `APL.VCG.contract_steps_no_trap` | Under those contract assumptions, no finite relation reduction reaches an arithmetic trap. |
| `APL.VCG.contract_steps_no_invalid` | Under those contract assumptions, no finite relation reduction reaches invalid. |

These theorems cover all call-free scalar term constructors and the specified
mathematical contract grammar. The call-aware extension below reuses their
primitive and specification proofs. All original 61 theorem statements and the
runtime semantic revision are unchanged.

## Finite call-expansion verification conditions

`wpCalls fs calleePreconditions height e syms post` generates formulas by expanding
actual function bodies. `height` bounds the expanded syntax tree and decreases
at each term constructor. It is neither evaluator depth nor execution fuel.
Successful generation is an explicit theorem premise. The generator returns
`none` when the bound is exhausted, a function is missing, argument arity differs,
a symbolic local is missing, or a specification reference cannot be instantiated.
Both branches and short-circuit operands must generate successfully, even when
one is not executed. Formula truth still guards their runtime obligations.

`wpArguments` threads argument continuations in source order under the caller's
symbolic environment. `invokeWP` binds the resulting symbols to the declared
callee parameters, inserts ordered precondition definedness and full truth, and
expands the callee body under the reversed symbols. The caller's lexical locals
do not enter that callee environment. Body expansion proves safety directly and
does not assume a callee postcondition or any prior execution-safety theorem.
The ordered `requiresVC` rules apply unchanged, so a clause cannot justify its
own definedness or use a later clause to justify it.

`generateCallsContract` uses the same independent `Spec` interpretation and
`Accepted` predicate as the call-free wrapper. Its body formula comes from
`wpCalls`. Every theorem below quantifies over the actual function and precondition
tables used during generation. Resource exhaustion remains allowed, and the
finite-reduction conclusions use the existing evaluator completeness theorems.

| Theorem | Quantified statement and assumptions |
| --- | --- |
| `APL.VCG.short_guard` | A symbol denoting a runtime value satisfies the generated short-circuit guard exactly when the runtime operator short-circuits. |
| `APL.VCG.not_shortable` | An operator outside Boolean conjunction and disjunction never short-circuits. |
| `APL.VCG.unary_wp_sound` | Successful primitive unary VC generation, formula validity and an operand denotation imply a safe actual primitive result with a postcondition witness. |
| `APL.VCG.binary_wp_sound` | The corresponding binary statement, additionally assuming the runtime operator does not short-circuit. |
| `APL.VCG.env_reverse` | Reversing related symbolic and concrete environments preserves `EnvRep`. |
| `APL.VCG.typed_parameters_rep` | Typed concrete parameter values are represented by the canonical parameter symbols under their own model. |
| `APL.VCG.invokeWP_preconditions` | Successful invocation-formula generation, related argument symbols and values, and formula validity imply ordered callee precondition definedness and full truth under those concrete arguments. |
| `APL.VCG.wpCalls_eval_sound` | Successful finite-height generation, related input environments and formula validity imply `Safe (PostHolds model post)` for actual `Program.eval fs depth env e fuel` at every execution depth and fuel. No assumed program safety or termination. |
| `APL.VCG.wpCalls_value` | Under those generation, representation and validity premises, any actual returned value satisfies `PostHolds`. |
| `APL.VCG.wpCalls_no_trap` | Under those premises, actual evaluation cannot return an arithmetic trap. |
| `APL.VCG.wpCalls_no_invalid` | Under those premises, actual evaluation cannot return invalid. |
| `APL.VCG.wpCalls_steps_value` | Under those premises, any finite `Program.Steps` reduction to `ret v []` satisfies `PostHolds`. |
| `APL.VCG.wpCalls_steps_no_trap` | Under those premises, no finite relation reduction reaches an arithmetic trap. |
| `APL.VCG.wpCalls_steps_no_invalid` | Under those premises, no finite relation reduction reaches invalid. |
| `APL.VCG.calls_contract_eval_sound` | Successful call-aware contract generation, `Accepted`, typed parameters and true entry preconditions imply that actual evaluation returns a value satisfying the independent specification or reaches a resource limit. |
| `APL.VCG.calls_contract_preconditions_defined` | Successful call-aware generation and `Accepted` imply ordered entry precondition definedness for every typed parameter environment. |
| `APL.VCG.calls_contract_nonvacuous` | Successful call-aware generation and `Accepted` imply a typed environment satisfying entry preconditions. |
| `APL.VCG.calls_contract_steps_value` | Under the call-aware contract theorem's premises, every finite returned value satisfies the independent postcondition specification. |
| `APL.VCG.calls_contract_steps_no_trap` | Under those contract premises, no finite reduction reaches an arithmetic trap. |
| `APL.VCG.calls_contract_steps_no_invalid` | Under those contract premises, no finite reduction reaches invalid. |

The first six entries expose existing supporting lemmas without changing their
statements. Kernel-checked examples cover nested calls, declared `bool`, `i64` and
`unit` argument order and reversed runtime locals, accepted nonvacuous entry contracts,
left-to-right argument traps even when the callee ignores those arguments, false
and undefined callee preconditions in both clause orders, missing functions in
unselected branches, wrong arity, forbidden result references in preconditions,
recursive expansion exhaustion, and a zero expansion bound.

This establishes soundness of the finite symbolic expansion generator. It does
not certify a source call-graph checker, prove that every acyclic source program
has a sufficient expansion bound, or establish equivalence with a separate
syntax-inlining transformation. Named-condition decomposition, Rust generation,
source-contract erasure, SMT translation and solver evidence remain unproved.
Full FM-07 remains partial.

## Local state extension

The following 37 theorems belong to `APL.LocalState`, a separate model for
`local-state-2026-11-17`. The preceding 81 theorem statements remain v0 artifacts.
Here `Γ` contains `(type, mutable)` bindings; an `Env` contains initialized scalar
values only. `EnvTyped env Γ` equates their ordered type lists. `HasType` and
`ArgsTyped` are independent inductive judgments. `WellTyped fs` requires every
function body to type check under immutable parameters and the complete signature
table, allowing recursion without assuming termination.

Both evaluation and value-return states carry the current environment.
`Frame.Typed` relates an input context and value type to an output context and
value type. Scope frames remove one binding; call-return frames carry a typed
saved caller environment. Every other frame passes through the current context.
`KontTyped` composes these judgments. The state-typing judgment is structural and
does not assume evaluation safety. Trap states have every result type; invalid
states have no typing constructor.

| Theorem in `APL.LocalState` | Quantified statement and assumptions |
| --- | --- |
| `infer_complete`, `infer_sound` | Declarative typing and successful inference imply one another, including permissions, assignment, loops and calls. |
| `type_unique` | Two typings of the same term under one signature table and context have equal result types. |
| `signatures_lookup`, `signatures_lookup_inv` | Function-table lookup and the corresponding signature-table lookup agree. |
| `checked_functions` | Successful inference of every declared function body establishes `WellTyped`. |
| `env_cons`, `env_tail` | Introducing a value of its declared type and removing the newest cell preserve ordered environment typing. |
| `env_lookup` | A context lookup and `EnvTyped` identify an initialized runtime value of that type. |
| `update_typed` | An existing context cell of the replacement value's type guarantees a successful update with the same environment typing. This lemma permits either static permission; the assignment typing rule separately requires mutability. |
| `update_other` | A successful update leaves each differently indexed cell unchanged. |
| `immutable_unchanged` | If the selected context cell is mutable and another is immutable, successful update leaves the immutable cell unchanged. |
| `step_complete`, `step_sound`, `step_iff` | The executable transition and the independently enumerated `Step` relation agree in both directions, including invalid untyped states. |
| `deterministic` | Any two one-step successors of one state are equal. |
| `stopped_iff` | The executable transition is absent exactly at a terminal value/trap or an invalid state. |
| `run_sound`, `run_complete`, `run_iff` | A successful finite run is a finite reduction to a stopped state, and every such reduction has a sufficient transition budget. No typing or termination assumption. |
| `resume_typed` | A typed primitive result, initialized environment and continuation yield a typed resumed configuration. |
| `preservation` | `WellTyped fs`, structural state typing and any `Step` imply typing of the successor. Covers all 37 transition constructors, including argument effects, scope removal, call isolation and loop back edges. |
| `progress` | A typed state is a terminal value/trap or has a `Step` successor. |
| `steps_preserve`, `safety` | Under `WellTyped fs`, finite reductions preserve typing and end in a terminal state or one with a successor. |
| `no_invalid` | A typed state in a well-typed function table cannot reduce to invalid. |
| `finite_run_safe` | Under those typing premises, any completed run returns a value of the requested type with empty continuation, or one of the defined arithmetic traps. The final value environment is existentially quantified. |
| `entry_typed`, `entry_safety` | A zero-parameter entry has a typed invocation state; under `WellTyped fs`, its finite reductions satisfy safety. |
| `embed_typed`, `embed_signatures`, `embed_wellTyped` | Embedding a v0 term/function table preserves signatures and declarative typing, making all old bindings immutable. |
| `embed_value_steps`, `embed_trap_steps`, `embed_invalid_steps` | Every finite old `Program.eval` value, trap or invalid result has a reduction of the embedded term/functions to the same outcome. Value evaluation restores the original environment even through nested scopes and calls. |
| `embed_value_run`, `embed_trap_run` | Every finite old evaluator value/trap has a sufficient new transition budget returning the same value/trap. No equality of budgets or fixed-limit completeness is asserted. |

The v0 embedding result is forward outcome preservation, including recursive
calls whenever they have a finite old evaluation. Reverse termination/divergence
correspondence has not been proved. The new machine's `run` theorem itself is
bidirectional for finite reductions. Neither result proves correspondence with
Rust or C.

Kernel-checked examples include surviving outer mutation, final false condition
effects, ordered argument mutation, isolated callee changes, recursive functions,
immutable/shadowed/mistyped assignment rejection, malformed loop types, exact
machine budget boundaries, short circuit, and loop-body trap propagation. V1
resource exhaustion is not a terminal language result and proves neither
termination nor divergence. The loop-free VCG results below add conditional
trap freedom. The later invariant generator adds conditional finite-prefix trap
freedom for loops. No variant, abrupt control-flow semantics or native-lowering
theorem is included.

## Loop-free local-state verification

The following 16 theorems belong to `APL.StateVCG`. They preserve the preceding
118 statements. `wp` is a concrete syntax-directed generator with a decreasing
expansion height. `StatePost` receives a symbolic value and a final symbolic
environment. `StatePostHolds` requires those symbols to denote the actual result
and final runtime environment and requires the returned formula to hold.
Formula interpretation reuses `APL.VCG.Formula.Holds`; it is independent of the
program execution relation.

The low-level generator describes the value-only `LocalState` machine. It does
not check assignment permission. Contract run and reduction corollaries add
`LocalState.WellTyped fs`, a typed body under `immutable types.reverse`, and
typed input parameters. These premises establish immutable entry parameters,
legal assignment targets and fixed binding types through the existing static
judgments. The generated conditions do not replace source checking.

| Theorem in `APL.StateVCG` | Quantified statement and assumptions |
| --- | --- |
| `update_rep` | A related symbolic/runtime environment, a denoting replacement value, and successful symbolic update imply a corresponding runtime update and related updated environments. |
| `run_result` | A finite reduction from any state to `.ret v env []` fixes every completed `LocalState.run` from that state to the same result and final environment. |
| `wp_trace` | Successful generation, related input environments, and independently interpreted formula truth imply a finite `LocalState.Steps` prefix from `.eval e env k` to `.ret v finalEnv k` satisfying `StatePostHolds`. The outer continuation is not executed. No execution-safety or termination premise. |
| `wp_run_sound` | Under those generator premises and an empty outer continuation, every transition budget yields `none` or a returned value/environment satisfying `StatePostHolds`. No returned trap, invalid state or unfinished configuration is allowed. |
| `wp_run_complete` | Those premises imply some transition budget returns a value and final environment satisfying `StatePostHolds`. This finite model termination consequence applies only to successfully expanded terms. |
| `wp_steps_value` | Every finite reduction to a value with empty outer continuation satisfies the generated value/environment postcondition. |
| `wp_steps_no_trap`, `wp_steps_no_invalid` | Under the generator premises, no finite reduction from the term with empty outer continuation reaches a trap or invalid state. |
| `invoke_preconditions` | Successful invocation generation, related declaration-order argument values, and formula truth imply ordered callee precondition definedness and truth on the captured actual arguments. |
| `contract_run_sound` | A generated and `Accepted` contract, a well-typed function table/body, typed inputs, and true entry requires imply that every run budget exhausts or returns the specified type and satisfies the requested postcondition on frozen entry parameters and result. |
| `contract_run_complete` | The same typed contract premises imply some sufficient transition budget returns the specified type and satisfies the requested postcondition. |
| `contract_steps_value` | Under those typed contract premises, every finite value reduction has the specified result type and satisfies the requested postcondition. |
| `contract_steps_no_trap`, `contract_steps_no_invalid` | Under those typed contract premises, no finite reduction reaches a trap or invalid state. |
| `contract_preconditions_defined` | A generated and accepted contract establishes ordered precondition definedness for every typed input. |
| `contract_nonvacuous` | A generated and accepted contract has a typed input on which every precondition is true. |

The trace proof follows assignment RHS effects, one-cell scope removal,
condition and operand effects, short circuit, ordered argument capture, and
callee isolation. Argument symbols are collected in declaration order. The
callee body uses reversed arguments as local cells. Returning from the callee
restores the caller environment saved after arguments, discarding callee cells.
Contract postconditions always use the original declaration-order parameter
symbols and the result, even when mutable local copies have changed.

Kernel-checked examples include a generic increment contract with a required
upper bound, RHS mutation of the same target, outer writes across scopes,
shadowing, initializer effects, both conditional branches, skipped state and
traps under short circuit, the independently expected ordered-argument result
2677, and a caller-state isolation result of 992. Negative examples cover
discarded overflow, false or undefined preconditions, missing targets/functions,
wrong arity, loops in unselected branches and short-circuit operands, recursive
expansion exhaustion, and zero expansion height.

Successful finite generation is not a theorem that every acyclic source graph
has sufficient expansion height. The model generator visits the selected root
and its syntactically expanded callees, not every unused function. Production
whole-program missing-annotation/recursion rejection is a separate check. The production
forward analysis, its correspondence to this CPS generator, named-query grouping,
source-contract correspondence, SMT translation, and solver evidence remain
unproved. Production loop-free mutable-code verification reports `smt-trusted`
results separately from these model theorems and retains
`termination_proved: false`. The separate invariant generator below proves
partial correctness of possibly divergent loops in the model. Production
invariant-loop verification is separate and remains solver-trusted.

## Invariant-loop foundations

These 32 additional theorems preserve all preceding 134 statements. They provide
frame, fresh-symbol, and annotation infrastructure used by the separate concrete
loop generator below. The production verifier separately supports annotated
loops with solver trust. Source invariant parsing,
resolution, checking, and erased metadata are implemented separately; these
model results do not prove those frontend or adapter components correct.

`Frozen Γ before after` records equal binding shape and equality of every immutable
cell. `FirstReturn fs suffix start value final` follows actual `LocalState.Step`
transitions and stops before consuming a return to `suffix`. It does not permit
arbitrary traces merely because their initial and final continuations are equal.

| Theorem in `APL.LocalState` | Quantified statement and assumptions |
| --- | --- |
| `frozen_refl` | A typed environment is frozen relative to itself. |
| `frozen_trans` | Immutable agreement and binding shape compose through an intermediate environment. |
| `update_frozen` | A typed environment, a mutable target of the replacement type, and successful update preserve every immutable cell. |
| `evaluation_frame` | A well-typed function table, typed term and entry environment, and finite evaluation from empty continuation to empty-continuation value imply immutable agreement, unchanged environment typing, and the declared result type. No termination or VCG premise. |
| `first_return_steps` | A first-return prefix is an actual finite machine reduction. |
| `first_return_isolated` | A first return from an expression to its outer continuation yields an isolated reduction of that expression with empty continuation and the same result/environment. No typing premise. |
| `first_return_frame` | Under function, term and environment typing, a first-return prefix preserves immutable cells and environment/result types. |

`Below`, `SymbolsBelow`, and `FormulaBelow` bound the variable identities in symbolic
artifacts. `AgreeBelow n M N` requires model equality at every identity below `n`.
`freshEnv` retains immutable cells, emits literal unit for mutable unit cells, and
allocates one distinct identity for every mutable numeric or Boolean cell.

| Theorem in `APL.LoopVCG` | Quantified statement and assumptions |
| --- | --- |
| `eval_agree` | A symbolic term supported below a bound evaluates equally in models agreeing below that bound. |
| `below_mono`, `symbols_below_mono` | Increasing the bound preserves symbolic term/environment support. |
| `denotes_agree`, `env_agree` | Bounded denotations and related symbolic/runtime environments survive model agreement below the bound. |
| `formula_agree` | A bounded formula has equivalent independent truth in models agreeing below its support bound. |
| `overwrite_agrees` | Replacing one model value preserves agreement at every smaller identity. |
| `fresh_covers` | Successful allocation, bounded input symbols representing an entry environment, and any typed actual head frozen relative to that entry imply some model extension representing the fresh head while preserving every earlier identity. |
| `fresh_bounded` | Successful allocation from bounded inputs never decreases the counter and returns symbols below the final counter. |
| `fresh_shape` | Successful allocation advances by exactly the number of mutable nonunit cells and emits exactly the consecutive fresh-identity range. |
| `fresh_distinct` | Fresh identities are unique and lie between the input and output counters. |
| `fresh_disjoint` | Two successful allocations, the second starting at the first's output counter, have disjoint fresh identities. |
| `group_exact` | The generated conjunction of a supplied check list holds exactly when every recorded guard implies its required formula. This does not prove completeness of the list or named-query partition. |
| `represented_type` | A denoting runtime value of the selected scalar type satisfies its symbolic type/range guard. |
| `head_domain_sound` | A generated head-domain formula holds for related symbolic and typed runtime environments. |
| `fresh_head_coverage` | Successful head generation and the coverage premises above yield a nondecreasing counter, bounded output symbols, and an earlier-symbol-preserving model extension representing any such actual head and satisfying its domain. |

The arbitrary-head theorem quantifies every typed actual environment preserving
immutable cells. Different dynamic iterations may use different model extensions;
no chosen abstract head is asserted reachable. The complete generator below
proves artifact support and separation from subsequent heads; it does not record
a global allocation-event manifest across nested loops, branches and calls.

`LoopAnnotations.Assertion` has an independently defined evaluator over current
locals, with index zero denoting the newest binding. It has no entry-parameter or
result binder. Its typing describes scalar types only, not definedness or truth.
`LoopAnnotations.HasType` is verification-ready annotated typing: every loop has
a nonempty list of Boolean assertions. Ordinary source typing still accepts
unannotated loops. `erase` removes only invariant metadata, including in function
bodies and call arguments.

| Theorem in `APL.LoopAnnotations` | Quantified statement and assumptions |
| --- | --- |
| `Assertion.eval_toSpec` | Local-assertion evaluation equals its internal specification translation, independent of the specification result slot. |
| `Assertion.instantiate_sound` | Successful symbolic instantiation and related current-local environments imply equality with the independent local-assertion evaluator. |
| `erase_typed` | Verification-ready annotated typing implies existing local-state typing after erasure. |
| `erase_signatures` | Function erasure preserves the complete signature table and function indices. |
| `erase_wellTyped` | Verification-ready annotated function typing implies a well-typed erased function table. |
| `Term.erase_mapAnnotations`, `Function.erase_mapAnnotations`, `eraseFunctions_mapAnnotations` | Arbitrary invariant-list replacement preserves erased terms, functions, and function tables. |
| `run_mapAnnotations` | Arbitrarily replacing all invariant lists preserves the actual erased `LocalState.run` at every identical transition budget, entry environment, and outer continuation. No annotation typing, truth, or definedness premise. |

The frame examples include a typed 19-step trace that consumes and recreates an
outer continuation while changing an immutable snapshot, demonstrating why the
first-return restriction is necessary. Fresh-head examples check mixed permissions,
unit allocation, and rejected shape mismatch. Annotation erasure is model-only;
source name resolution, attachment, lowering, emitted code, and runtime fuel remain
separate implementation boundaries.

## Invariant-loop generation and partial correctness

The seven modules `LocalStateContinuation`, `LoopVCG`, `LoopVCGBounds`,
`LoopVCGSoundness`, `LoopVCGContracts`, `LoopVCGQueries`, and `LoopVCGExamples`
add 126 audited statements while preserving the preceding 166 statements.
They prove conditional safety of the concrete Lean invariant generator, including
possibly divergent loops. They do not certify production loop verification.

`analyze` takes a verification annotation tree, static binding context, symbolic
locals, incoming path, fresh counter, and expansion height. It returns normal
outcomes with values, environments and paths, a separate list of guarded checks,
and the next counter. The height bounds syntax and callee-body expansion; it is
not a runtime loop-unrolling bound. Generation may fail even for safe programs.
Both branches and expanded callees must generate. The sufficient-height result
below supplies generation success for verification-ready typed syntax with a
supplied complete call rank. Source call-graph completeness and fixed
production-resource completeness remain separate.

Initialization and preservation checks each require independent invariant
definedness and truth under their original incoming path. The established
invariant is assumed only at an arbitrary fresh loop head. Every typed actual
head preserving immutable cells has a representing model extension. The condition
may mutate locals; its returned environment reaches the body or the false-exit
outcome. The false exit need not satisfy the head invariant. Nested loops,
short-circuit operands, and source-order call arguments use these same rules.
Captured argument values survive later argument effects, and callee evaluation
restores the caller environment saved after the final argument. Checks preceding
an infinite loop remain present even if no normal outcome follows it.

### Actual-machine continuation rules

`EvalSpec` is an internal compositional statement about the existing
`LocalState.run`, quantified over every transition budget and outer continuation.
Its continuation premise is discharged by composition and, at the top level, an
empty continuation. It is not an acceptance premise asserting program safety.
The complete generator induction below establishes every child specification.

| Theorem in `APL.LocalState.LoopVerification` | Quantified statement and assumptions |
| --- | --- |
| `spec_mono` | A pointwise weaker result relation preserves a subexpression specification. |
| `literal_rule`, `local_rule` | Literals and successful local lookup satisfy their exact value/environment specifications. |
| `assignment_rule`, `binding_rule` | RHS/initializer and body specifications compose through the actual update and scope frames; scope exit retains outer writes. |
| `conditional_rule`, `unary_rule`, `binary_rule` | Child specifications compose through actual conditional/operator frames, including checked operators and short circuit. |
| `call_rule` | Source-order argument specifications and a specification of the actual selected callee body compose through actual call/return frames and saved caller state. |
| `invariant_loop_rule` | An established entry invariant, a condition specification, a true-guard body specification reestablishing the invariant, and a false-guard result relation imply safety at every actual loop budget. The proof uses induction on transition budget and permits divergence. |
| `closed_run`, `closed_to_spec` | A subexpression specification yields closed-run safety, and safety at every closed-run budget yields the continuation specification via actual transition lifting. |
| `spec_frame` | Well-typed functions, term and entry environment strengthen normal results with immutable-cell agreement, unchanged environment typing and declared result type. |
| `no_finite_trap`, `no_finite_invalid` | A subexpression specification excludes any finite closed trace to trap or invalid. |

### Generator and support

The remaining theorem tables use namespace `APL.LoopVCG`.

| Generator/assertion theorem | Quantified statement and assumptions |
| --- | --- |
| `sequence_counter`, `bind_counter`, `arguments_counter`, `analyze_counter` | Successful concrete composition, argument generation and term generation never decrease the fresh counter. |
| `required_iff` | Conjoining symbolic definedness and truth is equivalent to the symbolic term evaluating to Boolean true. |
| `assertions_truth` | Successful assertion generation has truth formula equivalent to independently interpreted invariant truth, under related environments. |
| `assertions_group_exact` | Generated assertion checks hold exactly when the original incoming path implies the generated invariant truth conjunction. |
| `assertions_guards` | Every generated assertion check retains the supplied incoming path; no clause assumes itself or a sibling conclusion. |
| `assertions_established`, `invariant_defined` | Valid generated checks on a true path establish independent invariant truth, which entails defined evaluation for each clause. |

| Support theorem | Quantified statement and assumptions |
| --- | --- |
| `lookup_bounded`, `assertion_bounded` | Lookup and successful current-local assertion instantiation preserve symbol support. |
| `formula_bound_mono`, `type_guard_bounded`, `domain_bounded`, `fresh_head_bounded` | Formula bounds are monotone, and type guards, head domains and successful fresh heads use only their established symbol bounds. |
| `term_mono`, `symbols_mono`, `outcome_mono`, `checks_mono` | Increasing the support bound preserves term, environment, outcome and guarded-check support. |
| `checks_append`, `combine_supported`, `single_supported`, `add_check_supported` | Concatenation and primitive analysis assembly preserve support of all recorded artifacts. |
| `sequence_supported`, `bind_supported` | Successful concrete sequential composition preserves support, given bounded child artifacts at their own allocation counters. |
| `symbols_mem`, `symbols_of_mem`, `symbols_reverse`, `symbols_tail`, `update_bounded` | Symbol-list support is equivalent to member support and survives reversal, scope removal and successful bounded replacement. |
| `spec_bounded`, `requires_bounded`, `assertions_bounded` | Successfully instantiated specifications, ordered requires formulas and independently guarded invariant clauses preserve the input bound. |
| `unary_guard_bounded`, `division_guard_bounded`, `binary_guard_bounded`, `short_guard_bounded` | Primitive arithmetic, division and short-circuit checks use only operand symbols. |
| `map_outcomes_supported`, `mapM_property`, `scope_supported` | Successful outcome mapping and scope removal preserve required member properties and support. |
| `arguments_supported` | Successful source-order argument analysis preserves support for every captured argument, final environment, path and retained check. |
| `analyze_supported`, `analyze_bounded` | Successful complete generation from bounded locals/path bounds every output value, environment, path and guarded check by the returned counter, for all constructors. |
| `group_bounded` | Grouping supported checks preserves formula support. |
| `subsequent_head_separation` | Every recorded artifact of a supported analysis is bounded below each identity allocated by a subsequent successful fresh head. This is not a global allocation-event manifest theorem. |

### Complete operational soundness

`ValidFrom n M checks` quantifies **every** model extension agreeing with `M`
below `n`; the guarded checks must hold in all of them. It does not select one
convenient fresh head or restrict extensions to reachable states. Head domains
remain inside applicable paths. `Covered n M analysis value final` requires an
actual generated outcome and such an extension representing its value and final
environment with its path true. Input symbol/path bounds are necessary for
preserving prior values when fresh heads vary.

| Soundness theorem | Quantified statement and assumptions |
| --- | --- |
| `agree_refl`, `agree_trans`, `agree_restrict` | Model agreement is reflexive, composes, and restricts to smaller bounds. |
| `valid_member`, `valid_subset`, `valid_extend` | Universal check validity applies to any retained member, passes to subsets, and transports to a later agreeing model/counter. |
| `covered_subset`, `covered_extend` | Outcome coverage transports along outcome inclusion and model agreement. |
| `unary_guard_value`, `binary_guard_value` | Independently valid primitive guards and denoting operands yield the actual checked operator result and its symbolic denotation. |
| `sequence_locate`, `bind_locate`, `bind_input_checks`, `bind_context` | Concrete composition locates the analysis generated for a selected normal outcome, retains all input checks, and transports its bounded context, validity and coverage. |
| `single_covered`, `literal_sound`, `local_sound` | Singleton outcomes, literals and local lookup establish exact normal coverage. |
| `unary_analysis_sound`, `assignment_analysis_sound` | Valid generated operator/update checks and child specifications establish the actual machine specification. Assignment uses the RHS's final environment. |
| `mapM_member`, `scope_covered`, `binding_analysis_sound` | Successful scope mapping relates every actual child outcome and removes only the new binding; typed child framing supplies body input types. |
| `boolean_denotes`, `true_denotes`, `false_denotes` | Boolean checks and path truth recover exact represented condition values. |
| `conditional_counter`, `conditional_analysis_sound` | Both generated branches have ordered counters; the branch selected by the actual condition runs in its returned environment under valid guarded checks. |
| `binary_finish_counter`, `binary_counter`, `binary_analysis_sound` | Binary path composition preserves counter order and soundness. A skipped RHS retains the left operand's value/environment; a taken RHS preserves the captured left value across model extensions. |
| `preserve_counter`, `action_counter`, `action_false`, `false_guard` | Loop action assembly has ordered counters and an exact unit-valued false outcome using the condition's final environment and negated guard. |
| `loop_analysis_sound` | Successful concrete loop generation, supported inputs and condition/body soundness establish the actual invariant rule. Every typed immutable-preserving head is covered by fresh extension; initialization/preservation follow from original guarded checks. No normal return is assumed. |
| `args_spec_mono`, `arguments_analysis_sound` | Source-order argument generation captures values immediately, threads caller state, preserves prior captures under extension, and establishes the actual argument specification. |
| `call_analysis_sound`, `callee_requires_defined_and_true` | Expanded callee bodies use immutable reversed argument locals and restore the caller state saved after arguments; generated precondition obligations establish independent ordered requires definedness and truth. Callee postconditions are not assumed. |
| `analyze_sound` | Well-typed erased functions, successful concrete generation and bounded input symbols/path imply `SoundAt`: related typed actual locals, true input path and `ValidFrom` establish the actual continuation specification with normal coverage. Complete height induction discharges every child soundness premise. |
| `analyze_run_sound` | Under the same represented-input and universally valid-check premises, every actual closed-run budget either exhausts or returns a covered normal result. |
| `analyze_steps_no_trap`, `analyze_steps_no_invalid` | Under those premises, no finite closed transition trace reaches a trap or invalid state. |
| `analyze_steps_value` | Every finite closed normal-return trace has a generated covering outcome, including its final environment. |

All top-level run and finite-trace observations start with an empty outer
continuation; normal observations end with one. No theorem asserts a returning
budget exists. A safe infinite loop can therefore satisfy any postcondition.

### Frozen-entry contracts and exact queries

`generateContract` reserves canonical declaration-order parameter symbols below
the first fresh counter, reverses them for runtime locals, generates the body,
and adds one independently defined-and-true postcondition check per normal
outcome under its original path. The specification uses original parameters and
the captured result, not final local values. `Accepted` requires ordered requires
definedness for every typed input, existence of a typed requires-satisfying input,
and `ValidFrom` for body and post checks on every such satisfying input. It adds
no global satisfiability requirement for loop invariants.

| Contract theorem | Quantified statement and assumptions |
| --- | --- |
| `parameter_symbols_bounded`, `post_check_guard` | Canonical entry symbols are below the reserved bound, and every post check keeps exactly its outcome path. |
| `post_check_sound`, `covered_post` | Valid post requirements and represented parameters/result establish independently interpreted `Spec.eval` truth; coverage transports frozen parameter denotation across fresh extensions. |
| `contract_spec_sound` | Successful generation, acceptance, verification-ready annotated `WellTyped`/`HasType`, typed actual parameters and true requires establish actual-machine specification with declared result type and independent postcondition. |
| `contract_run_sound` | Under those premises, every actual closed-run budget exhausts or returns a value of the declared type satisfying the postcondition. |
| `contract_steps_value`, `contract_steps_no_trap`, `contract_steps_no_invalid` | The corresponding finite closed traces establish the type/postcondition or exclude trap/invalid. |
| `contract_preconditions_defined`, `contract_nonvacuous` | Acceptance implies independently interpreted ordered requires definedness on every typed input and an actual typed satisfying input. |

`tagFrom` assigns one key to each check by position. `queryKeys` computes distinct
keys, and `queryChecks` retains original guarded checks for each key. `queries`
groups exactly those checks. The classifier may merge checks into one query or
separate them; it does not change any guard or required formula.

| Query theorem | Quantified statement and assumptions |
| --- | --- |
| `tag_erases`, `tag_length` | Removing tags recovers the original check list exactly, with the same length. |
| `key_mem`, `keys_unique`, `check_mem` | The emitted keys are unique and exactly those with tagged checks; selecting a key retrieves exactly its original checks. |
| `partition_exact`, `query_list_exact`, `tagged_partition_exact` | All emitted query formulas hold exactly when the complete original guarded-check conjunction holds, independently of normal outcome existence. |
| `validity_partition_exact` | All grouped queries valid under every earlier-symbol-preserving extension are equivalent to `ValidFrom` for the original checks. |
| `analyze_queries_run_sound` | This exact grouped validity yields the same actual closed-run safety and normal coverage as the complete generator theorem. |

`LoopVCGExamples` includes support rejection, absent annotation rejection,
independent false/undefined invariant clauses, ordered requires definedness,
source-order argument effects and callee isolation, final false-guard mutation,
a safe infinite loop with an accepted false postcondition and no finite return,
rejection of a trap before divergence, and retention of that trap through
arbitrary query grouping. An accepted contract with mutable shadowing and an
effectful loop guard preserves declaration-order entry parameters, while the
otherwise identical reversed-parameter postcondition is rejected. Each example
is kernel checked.

The model uses path-split outcomes; production uses a distinct merged-flow
representation. Source lowering, annotation attachment, classifier-to-source
occurrence/clause/query-name correspondence, global allocation-event manifests,
production limits, SMT encoding and solver/model correspondence remain open.
In particular, the formal validity premise includes mathematical models with an
out-of-range head value behind an inactive guard. A production decoder must
account for applicable domains or justify a different encoding; it cannot
silently strengthen this theorem's premise. An abstract head countermodel is not
a replayed concrete source execution. Production loop verification uses solver
trust, and no production termination claim follows.

## Sufficient generation height with a supplied call rank

`LoopGenerationSupport`, `LoopGenerationRank`, `LoopGenerationComplete`,
`LoopGenerationCorollaries` and `LoopGenerationExamples` add 29 audited statements,
preserving the preceding 292. They establish a sufficient expansion height for
the unchanged `LoopVCG.analyze`. This result concerns symbolic generation, not
logical acceptance, execution safety or production resource completeness.

The premises are verification-ready annotated `WellTyped` functions and a body
with annotated `HasType`; `PreconditionsTyped` for every table entry; a supplied
natural rank covering every syntactic call; and a symbolic environment whose
length equals the static context length. `PreType` is result-free static
specification typing with declaration-order parameters and the existing scalar
operator types. It has no truth, definedness or satisfiability premise.

`CallsBelow rank ceiling e` and `ArgumentsBelow` traverse all syntax, including
both branches, every call argument, effectful loop conditions and loop bodies.
Every call to `f` must satisfy `rank f < ceiling`. `Ranked fs rank` requires this
coverage of each function body under that function's own rank. The rank is a
supplied witness: no theorem here constructs one from a separately defined DAG,
extracts source call edges or certifies the production cycle checker.

`nodes` counts term constructors and their children; `argumentNodes` sums the
argument counts. Typed invariant/specification instantiation is structurally
total and does not consume analyzer expansion height. The explicit bounds are:

```text
bodyBound fs = 1 + sum(nodes(fn.body) for fn in fs)
sufficientHeight fs ceiling e = ceiling * bodyBound fs + nodes e + 1
rankBound fs rank = 1 + sum(rank(i) for i in [0, fs.size))
tableHeight = rankBound fs rank * bodyBound fs + bodyBound fs + 1
```

Structural children reduce node count. Expanded callee bodies reduce rank and
have node count below `bodyBound`. The actual generator gives sibling arguments,
outcomes and branches the same smaller child height; height is not a sequential
work allowance. The proof inducts over that actual height and establishes
normal-output environment length along with generation success.

| Theorem in `APL.LoopGeneration` | Quantified statement and assumptions |
| --- | --- |
| `lookup_exists` | An in-bounds lookup in any finite symbolic list returns an element. |
| `pre_instantiate`, `requires_total` | Typed result-free specifications and Boolean requires lists instantiate successfully for symbolic parameter lists of the declared length. |
| `assertion_total`, `assertions_total` | Typed current-local assertions and invariant lists instantiate successfully for symbolic environments of the context length, even when their arithmetic is undefined. |
| `shape_single`, `shape_combine`, `sequence_total`, `bind_total` | Outcome environment lengths and total child actions compose through the actual singleton, combination, sequence and bind constructors. |
| `update_total`, `fresh_total`, `domain_total`, `head_total` | In-bounds updates and length-correct fresh-environment/domain/head construction succeed; updates and fresh environments preserve length. Mutable unit uses literal unit as in the existing generator. |
| `sequence_results`, `bind_results`, `arguments_total`, `pop_total` | Generic output properties compose; argument generation preserves caller environment length and captures one value per argument; scope removal succeeds and drops one cell. |
| `member_sum_bound`, `body_bounded`, `nodes_positive`, `argument_node_bound` | Finite syntax, argument and table-body sizes satisfy the displayed structural bounds. |
| `arguments_rank`, `rank_cost_decreases` | Every argument inherits call-rank coverage, and an expanded callee has smaller weighted rank/size cost. |
| `analyze_complete` | Under the typing, metadata, supplied-rank and length premises above, `ceiling * bodyBound fs + nodes e < height` implies that the actual `LoopVCG.analyze` returns some analysis and every outcome environment has length `Γ.length`. Complete induction discharges all child-totality premises. |
| `uniform_generation`, `exists_uniform_height` | The explicit sufficient term height, or one existential height outside the inputs, works for every symbolic environment of the context length, every incoming path and every initial fresh counter. |
| `function_generation` | For any table lookup, `Ranked` supplies the body call-rank premise and the concrete bound guarantees generation under immutable reversed parameters. |
| `rank_bounded`, `table_uniform_height` | Every table entry's supplied rank is below `rankBound`; the single displayed table height works for every function and every symbolic input of its parameter length, path and fresh counter. |

Symbolic contents are unrestricted. The theorem does not require supported
variable IDs, denotation by actual values, a true path, valid generated checks,
precondition satisfiability or invariant truth/definedness. It therefore does
not replace the separate soundness theorem's premises. It preserves the length
of every normal output environment without assuming a normal runtime return.

The ten private kernel witnesses include a shared-call DAG with multiple
parameters and a disconnected function; a call in an effectful nested-loop
condition; false/undefined typed preconditions and invariants; arbitrary symbols
and colliding fresh counters; rank contradictions for source-dead self-recursion,
mutual recursion and a recursive argument inside a false loop body; and a
universally undefined symbolic cell that still generates. Another witness pairs
successful generation of `while true` with the actual `LocalState.run` returning
`none` at every finite budget. Generation success does not imply runtime return.

The theorem uses finite syntax, unbounded natural counters and unrestricted
finite model collections. It gives no work, time, memory, query or allocation
bound for an implementation and no completeness guarantee at fixed Rust limits.
It does not assert minimal height, runtime termination, rank existence/extraction,
source graph/annotation/contract correspondence, or Rust/SMT/solver/native
correctness. Production loop verification remains separately `smt-trusted`.

## Flat scalar products with local state

`FlatProductsValues`, `FlatProductsMachine`, `FlatProductsTyping`,
`FlatProductsRun`, `FlatProductsSafety`, `FlatProductsEmbedding` and
`FlatProductsExamples` add 55 audited general/support statements, preserving all
preceding 321 statements and their dependency definitions. Their namespace is
`APL.FlatProducts`; they describe a separate runtime model.

`Flat α` contains a list with proofs of nonempty length at most eight. New `Ty`
and `Val` each wrap an existing scalar or a bounded tuple of existing scalar
fields. Ordered field types determine tuple shape. Unit is not an empty tuple,
and a singleton tuple is distinct from its field. Scalar i64 values retain their
existing range invariant, and operators reuse the existing scalar arithmetic
through an explicit result embedding. Tuple equality and inequality require
matching shapes and compare the completed field lists.

`Term` is untyped syntax. Empty, overwide and nested construction, invalid
projections, bad references and ill-typed operations remain representable.
`HasType` and `ArgsTyped` are independent inductive judgments, separate from
`infer`. Tuple typing matches every field against its bounded scalar shape;
projection requires an actual in-bounds type lookup. `WellTyped fs` checks every
actual function body against its declared result under immutable parameters in
reversed declaration order. It permits recursion and makes no acyclicity,
termination or arithmetic-safety assumption.

The machine carries the current environment through each field and argument.
Tuple frames retain captured scalar prefixes in reverse order and reverse once
on completion. Projection consumes one completed base, including all constructor
fields. Equality evaluates both operands. Local scopes pop their own binding
while retaining outer mutations. Calls enter isolated captured-argument
environments and restore the caller environment saved after argument effects.
False loop exits retain the condition's final environment.

| Theorem in `APL.FlatProducts` | Quantified statement and assumptions |
| --- | --- |
| `Flat.ext`, `Flat.make_fields` | Equal ordered fields determine equal bounded values/shapes; rebuilding an existing bounded list succeeds. |
| `scalar_canonical`, `tuple_canonical` | A value-type equality yields the corresponding scalar or bounded tuple representation and its field-type equality. |
| `embedResult_typed`, `unary_typed`, `binary_typed`, `shortCircuit_typed` | The old typed scalar result embeds; the declared unary input or successful binary type computation yields a typed result, allowing defined traps; a typed short-circuit result has the operator's result type. |
| `construct_typed`, `project_typed` | Construction is typed when field types equal a bounded shape; projection is typed when the base has that tuple type and the requested shape lookup succeeds. |
| `scalarList_complete`, `scalarList_sound`, `make_fields` | Scalar type-list conversion succeeds exactly on scalar wrappers; successful bounded-list construction retains the original fields. |
| `infer_complete`, `infer_sound`, `type_unique` | Declarative typing and successful inference coincide for arbitrary signatures, contexts and terms; two typings have the same result type. Every term and argument-list constructor is covered. |
| `signatures_lookup`, `signatures_lookup_inv`, `checked_functions` | Function and signature lookups agree in both directions; checking every actual body under reversed immutable parameters establishes `WellTyped`. |
| `env_cons`, `env_tail`, `env_lookup`, `update_typed`, `update_other`, `immutable_unchanged` | Runtime cell types match the static context. Cons/tail preserve the correspondence, valid typed lookups exist, typed updates preserve it, and a single checked update leaves other cells and immutable bindings unchanged. |
| `step_complete`, `step_sound`, `step_iff`, `deterministic`, `stopped_iff` | Independent `Step` and executable `step` coincide for arbitrary raw states/tables, so stepping is deterministic. Stopped states are empty-continuation returns, defined traps or raw invalid. |
| `run_sound`, `run_complete`, `run_iff` | An actual successful run gives a finite trace and stopped final state. Conversely, every finite trace to a stopped state has some sufficient transition budget. No typing or termination premise is hidden in these correspondence results. |
| `args_scalar_cons`, `args_scalar_nil`, `resume_typed` | Typed scalar field lists yield head/tail or empty-list facts; a typed operator result resumes under a typed environment and continuation. |
| `preservation`, `progress`, `steps_preserve`, `safety`, `no_invalid` | Preservation requires a well-typed function table, typed initial state and one independent step. Progress requires a typed state. With the table premise, every finite trace preserves typing, is stopped or can take a step, and cannot reach invalid. All constructor obligations are discharged, including call bodies and tuple-prefix completion. |
| `finite_run_safe`, `entry_typed`, `entry_safety` | A completed actual run from a typed state under a well-typed table returns the declared type with an empty continuation or a defined trap. Entry typing requires an actual nullary function lookup; entry safety additionally requires the well-typed table and a finite trace. |
| `embed_typed`, `embed_signatures`, `embed_wellTyped`, `embed_update`, `embed_resume` | Old LocalState typing, function tables, cell updates and scalar operator results embed into the new model. |
| `embed_step`, `embed_steps`, `embed_stopped` | Every old transition gives a new transition; finite traces and stopped states embed, including malformed and trapping raw states. |
| `embed_finite_run`, `embed_finite_value`, `embed_finite_trap` | An actual completed old run yields some new budget with the embedded outcome; specialized value/trap results preserve final environments and values or trap kinds. This is forward finite embedding. |

`EnvTyped` equates runtime cell types with static context types. Frame and
continuation typing connect current and outer contexts and result types,
including captured tuple prefixes and saved caller environments. These are
structural typing premises, not an assumption of semantic safety. Progress alone
does not replace the `WellTyped` table premise needed by preservation: a typed
entry into an ill-typed table can still step to invalid. Raw assignment updates
values without rechecking source permissions; the typed theorem uses the static
permission premise.

The nineteen private boundary examples cover field and argument snapshots,
projection once and all-field evaluation, mutation order, equality effects,
trap priority, whole-value replacement, caller isolation, recursive tuple
returns, loop state, final false-guard mutation, width limits and raw rejection.
An all-budget witness places a divergent first field before a later trap and
applies the full finite-prefix safety theorem; reversing the fields preserves
the prior trap. Another witness shows why the well-typed table premise cannot be
dropped. Supporting private lemmas and examples are replayed with the module,
not added to the audited public statement count.

Type safety permits defined arithmetic traps and divergence. It does not prove
trap freedom, runtime termination, reverse divergence correspondence or equal
production resource accounting. The finite mathematical machine does not model
Rust allocation/slot/output limits. Source parsing and elaboration, annotations,
JSON adapters, Rust checking/evaluation, shared tuple storage and reclamation,
MIR/native code, ownership and the SMT stack remain separate correspondence or
trust obligations. No aggregate verification-condition generator is covered by
these runtime theorems.

## V2 reader acceptance soundness

`APL/FlatProductsWireSafety.lean` proves acceptance soundness for the actual
`APL.FlatProductsWire.document`, `decode` and `execute` definitions used by
`MainV2`. The reader and execution algorithms are unchanged.

`InputTyped` is an independent proposition indexed by the input and its result
type. Its expression case requires `HasType #[] [] e t`. Its program case requires
`WellTyped fs`, the actual entry lookup, no entry parameters and an i64 result.
Every function body is included, whether the entry can reach it or not. The proof
aligns the signature pass with the reconstructed table before applying inference
soundness; the alignment is proved rather than assumed.

| Theorem in `APL.FlatProductsWire` | Quantified statement and assumptions |
| --- | --- |
| `document_typed`, `decode_typed` | A successful return from the actual document reader or text wrapper implies `InputTyped input t` for some result type. |
| `document_program_typed`, `decode_program_typed` | Successful program decoding yields a well-typed complete function table and an actual nullary i64 entry. |
| `execute_typed` | For an `InputTyped` input and every fuel budget, the actual execution wrapper satisfies `ResultTyped`: a successful value has the expected type, defined traps and resource limits are allowed, and invalid is excluded. |
| `execute_no_invalid`, `execute_value_type` | For an `InputTyped` input, the execution result is never invalid and any successful value has the input's result type. These specialize `execute_typed`. |
| `decoded_execute_safe` | Successful `decode` supplies a result type and typing proof for the input, with invalid exclusion and returned-value typing at every fuel budget. |

The theorem needs no successful execution, positive fuel, acyclic call graph or
termination premise. It composes acceptance with the existing typed-machine
safety theorem. The result establishes model type safety, not trap freedom or
tuple contract verification.

The text wrapper proof inverts successful size, lexical and JSON steps before
applying `document_typed`. It does not prove how those steps interpret text or
that every valid document is accepted. Term reconstruction, serialized metadata,
JSON-text meaning, source correspondence, Rust behavior, Lean compilation/runtime
and native execution retain separate obligations. No kernel certificate for
individual artifact bytes is generated.

`test_flat_products.py` checks hand-authored valid/malformed artifacts, source
exports and old scalar embeddings against independently specified outcomes,
including exact JSON field sorts and shape. Type rejection precedes evaluation
even with zero fuel. Resource probes check tool-specific boundaries separately
and do not count as finite semantic agreements. Run
`python3 formal/test_flat_products.py --rust target/debug/anl` after building both
formal executables and the compiler. These executable comparisons complement
the reader acceptance theorem without proving the remaining correspondence
obligations.

## Merged flat-tuple contract verification

The additive `ProductLogic`, `ProductAnnotations`, `ProductEntry` and
`ProductFlow` modules define contract verification over the existing
`flat-products-2026-11-17` machine. The executable language and earlier scalar,
local-state and product runtime definitions remain unchanged. The checking
command and Lean version are those at the start of this inventory.

`APL.ProductFlow.analyze` is a concrete generator with one symbolic result, one
environment, one normal-return guard, a guarded-check list and a fresh counter.
It handles every annotated term constructor, including tuple construction and
projection, strict and short-circuit operators, mutation, scopes, conditionals,
calls and invariant loops. Successful generation at the supplied finite height
is an explicit premise. This is a merged generator, separate from the earlier
scalar continuation and path-split generators.

### Actual-machine soundness

`APL.ProductFlow.analyze_sound` requires a well-typed complete erased function
table, successful `analyze`, and support of the initial symbolic environment and
path below the starting identity bound. Its `SoundAt` conclusion quantifies over
every mathematical model and actual environment that represent those symbols.
It requires actual environment typing, an established incoming path and
`ValidFrom` for the generated checks.

`ValidFrom` means that every guarded check holds in every model agreeing below
the starting bound. The conclusion is `APL.FlatProducts.LoopVerification.EvalSpec`
for the actual `FlatProducts` continuation machine. On normal return, `Covered`
requires an existential model extension that agrees below that bound, establishes
the merged normal guard and represents the complete result and final environment.
Universal check validity and existential normal coverage are separate premises
and conclusions. An unselected branch need not denote or terminate.

`APL.ProductFlow.analyze_run_sound` gives the result at every actual transition
budget. Exhaustion remains inconclusive. `analyze_no_finite_trap` and
`analyze_no_finite_invalid` exclude finite traces to traps or invalid states under
the same premises. `analyze_normal_coverage` represents every finite normal result
and final environment.

`APL.ProductFlow.fresh_head_coverage` constructs an agreeing extension for any
typed actual head environment that preserves immutable bindings. Every mutable
non-unit field receives a distinct fresh identity; units and immutable bundles
retain their values. The loop proof establishes initialization and preservation,
analyzes the effectful condition and true-guard body, and passes the final false
condition's environment to the continuation. It permits divergence.

Fields and call arguments evaluate left to right and retain completed snapshots.
Projection evaluates the complete base. Strict tuple equality evaluates both
complete operands. Calls reverse whole source arguments for the callee's local
index convention and restore the caller environment after the body. The
`FlatProductsFrame` and `FlatProductsContinuation` statements establish these
rules over the existing machine, including its tuple and projection frames.

### Specification, entry and contract statements

`APL.ProductAnnotations.Spec.instantiate_sound` relates successful instantiation
to the independent mathematical specification evaluator under parameter, result
and local representation. `instantiate_defined` makes generated definedness
equivalent to an actual specification result; `instantiate_value` relates the
returned value. These rules retain all fields of a projection base and both
complete equality operands. Outer Boolean short circuit remains selective.
`ProductAnnotations` has independent typing, and `erase_wellTyped` proves that
erasing its complete typed table yields a well-typed `FlatProducts` table.

`APL.ProductEntry.parameter_entry_iff` equates the complete parameter-domain
formula with a represented typed runtime argument list. Every integer leaf must
lie in i64 range, while specification arithmetic remains mathematical.
Parameter layouts reserve scalar field slots in source order, including units.
The display-head lemmas prove the logical identity equation and disjointness
from reserved parameter slots. They do not prove that Rust reconstructs source
identities or emits the corresponding display strings.

`APL.ProductFlow.contract_reachable_iff` requires successful `generateContract`.
It equates satisfiability of the generated entry path with existence of typed
runtime parameters satisfying all requires clauses. `contract_accepted_nonvacuous`
extracts that witness from semantic acceptance. `contract_accepted_entry_defined`
establishes ordered requires definedness for every typed input, including inputs
that do not satisfy requires. Each clause is defined when all earlier clauses
are true; later clauses cannot justify earlier definedness.

`APL.ProductFlow.contract_queries_sound` requires a well-typed complete annotated
table, successful `generateContract`, typed runtime parameters satisfying
requires, and semantic acceptance of every query in `contractQueries`. For every
transition budget, the actual machine either exhausts its budget or returns a
covered value and final environment satisfying every ensures clause with the
original entry parameters. The theorem does not require a particular source
function ID. `root_contract_sound` additionally requires a table lookup for the
function and proves its declared result type, final environment typing and
preservation of immutable entry bindings.

`contract_accepted_no_finite_trap`, `contract_accepted_no_finite_invalid` and
`contract_accepted_normal` give the corresponding finite-trace contract results.
None promises a normal return.

### Exact query partition

`APL.ProductFlow.exact_named_check_partition` and `named_groups_partition` prove
that flattening the grouped checks is a permutation of the original check list.
They preserve multiplicity, rather than only set membership. Groups have distinct
keys and contain only checks with their key. The final layer retains a body group
even when it is empty and adds one separate entry-satisfiability query.
`entry_check_keys`, `post_check_keys` and `invariant_check_keys` identify indexed
clause checks in order.

`APL.ProductFlow.contract_queries_exact` equates semantic acceptance of the final
queries with universal validity of all guarded checks and an existential entry
witness. Safety queries negate a guarded conjunction and expect unsatisfiability;
the entry query expects satisfiability. This is a theorem about mathematical
query acceptance, not solver replies. The model stores a callee-precondition check
after its expanded body checks, while production stores that check first.
The partition result permits reordering and preserves every occurrence.

### Public statement inventory

The table lists 174 public named statements across 24 modules, in addition to
the earlier 384 audited names and 48 replayed modules. The claims above specify
the central quantified interfaces. The supporting statements retain the local
typing, lookup, representation, support, range and successful-generation premises
in their source declarations. No theorem assumes the Rust implementation correct.

| Module and public statements | Quantified coverage and assumptions |
| --- | --- |
| `FlatProductsFrame.lean`<br>`APL.FlatProducts.frozen_refl`<br>`APL.FlatProducts.frozen_trans`<br>`APL.FlatProducts.frozen_lookup`<br>`APL.FlatProducts.update_frozen`<br>`APL.FlatProducts.evaluation_frame`<br>`APL.FlatProducts.first_return_steps`<br>`APL.FlatProducts.first_return_isolated`<br>`APL.FlatProducts.first_return_lift`<br>`APL.FlatProducts.first_return_iff`<br>`APL.FlatProducts.first_return_frame` | Typed immutable-cell framing, first-return decomposition, isolation and continuation lifting for the actual machine. |
| `FlatProductsContinuation.lean`<br>`APL.FlatProducts.LoopVerification.spec_mono`<br>`APL.FlatProducts.LoopVerification.literal_rule`<br>`APL.FlatProducts.LoopVerification.local_rule`<br>`APL.FlatProducts.LoopVerification.assignment_rule`<br>`APL.FlatProducts.LoopVerification.binding_rule`<br>`APL.FlatProducts.LoopVerification.conditional_rule`<br>`APL.FlatProducts.LoopVerification.unary_rule`<br>`APL.FlatProducts.LoopVerification.binary_rule`<br>`APL.FlatProducts.LoopVerification.args_spec_mono`<br>`APL.FlatProducts.LoopVerification.call_rule`<br>`APL.FlatProducts.LoopVerification.fields_spec_mono`<br>`APL.FlatProducts.LoopVerification.tuple_rule`<br>`APL.FlatProducts.LoopVerification.projection_rule`<br>`APL.FlatProducts.LoopVerification.tuple_binary_rule`<br>`APL.FlatProducts.LoopVerification.invariant_loop_rule`<br>`APL.FlatProducts.LoopVerification.closed_run`<br>`APL.FlatProducts.LoopVerification.closed_to_spec`<br>`APL.FlatProducts.LoopVerification.spec_frame`<br>`APL.FlatProducts.LoopVerification.no_finite_trap`<br>`APL.FlatProducts.LoopVerification.no_finite_invalid`<br>`APL.FlatProducts.LoopVerification.normal_result` | Compositional actual-machine rules for literals, locals, assignment, bindings, branches, operators, calls, tuple fields and projection, plus invariant loops, closed runs, framing and finite-trace consequences. |
| `ProductLogicScalar.lean`<br>`APL.ProductLogic.embedTerm_eval`<br>`APL.ProductLogic.eval_ite_selected`<br>`APL.ProductLogic.embedFormula_holds`<br>`APL.ProductLogic.embed_denotes`<br>`APL.ProductLogic.SymTerm.eval_agree`<br>`APL.ProductLogic.SymTerm.supported_mono`<br>`APL.ProductLogic.Formula.holds_agree` | Conservative scalar term/formula embedding, selected-only conditional evaluation, and evaluation or truth preservation under supported model agreement. |
| `ProductLogicValues.lean`<br>`APL.ProductLogic.embedValue_type`<br>`APL.ProductLogic.ProductDenotes.shape`<br>`APL.ProductLogic.ProductDenotes.eval`<br>`APL.ProductLogic.EnvRep.shape`<br>`APL.ProductLogic.construct_capture`<br>`APL.ProductLogic.project_full_base`<br>`APL.ProductLogic.ProductDenotes.agree`<br>`APL.ProductLogic.EnvRep.agree`<br>`APL.ProductLogic.definedFields_iff`<br>`APL.ProductLogic.ProductDenotes.all_defined`<br>`APL.ProductLogic.equality_sound`<br>`APL.ProductLogic.inequality_sound`<br>`APL.ProductLogic.embedValue_injective`<br>`APL.ProductLogic.merge_selected`<br>`APL.ProductLogic.runtime_equality_sound`<br>`APL.ProductLogic.runtime_inequality_sound`<br>`APL.ProductLogic.mergeEnv_selected`<br>`APL.ProductLogic.EnvRep.replace`<br>`APL.ProductLogic.EnvRep.reverse`<br>`APL.ProductLogic.runtime_lift_typed`<br>`APL.ProductLogic.embedValue_representable`<br>`APL.ProductLogic.flatProducts_equality`<br>`APL.ProductLogic.flatProducts_inequality` | Exact-shape product and environment representation, complete-field definedness, capture and projection, equality, selected-branch merging, whole-value replacement and bounded-runtime lifting. |
| `ProductLogicLayout.lean`<br>`APL.ProductLogic.leafSlot_in_bounds`<br>`APL.ProductLogic.leafSlot_unique`<br>`APL.ProductLogic.headIdentity_disjoint`<br>`APL.ProductLogic.headIdentity_injective`<br>`APL.ProductLogic.scalar_reservedCount`<br>`APL.ProductLogic.scalar_parameterOffset`<br>`APL.ProductLogic.scalar_leafSlot`<br>`APL.ProductLogic.parameterScalar_unit`<br>`APL.ProductLogic.parameterValue_shape`<br>`APL.ProductLogic.parameterLayout_shapes`<br>`APL.ProductLogic.parameterLayout_supported`<br>`APL.ProductLogic.parameterLayout_lookup`<br>`APL.ProductLogic.parameter_tuple_field` | Parameter-slot bounds and uniqueness, disjoint fresh identities, scalar layout compatibility, unit literals, parameter shapes, support and field lookup. |
| `ProductAnnotations.lean`<br>`APL.ProductAnnotations.erase_typed`<br>`APL.ProductAnnotations.erase_signatures`<br>`APL.ProductAnnotations.erase_wellTyped`<br>`APL.ProductAnnotations.erase_lookup` | Independent annotated typing erases to the existing term, signature and complete-table typing; function lookup commutes with erasure. |
| `ProductFlowSupport.lean`<br>`APL.ProductFlow.value_domain_sound`<br>`APL.ProductFlow.env_domain_sound`<br>`APL.ProductFlow.value_domain_complete`<br>`APL.ProductFlow.env_domain_complete`<br>`APL.ProductFlow.fresh_value_shape`<br>`APL.ProductFlow.fresh_value_bounded`<br>`APL.ProductFlow.fresh_value_covers`<br>`APL.ProductFlow.fresh_env_bounded`<br>`APL.ProductFlow.fresh_env_covers`<br>`APL.ProductFlow.fresh_head_coverage`<br>`APL.ProductFlow.fresh_env_identities`<br>`APL.ProductFlow.fresh_env_distinct`<br>`APL.ProductFlow.fresh_env_disjoint` | Runtime domains are sound and complete for representation. Successful fresh generation preserves shape/support and covers typed environments with distinct, contiguous, disjoint mutable non-unit identities. |
| `ProductSpec.lean`<br>`APL.ProductAnnotations.Spec.instantiate_sound`<br>`APL.ProductAnnotations.Spec.instantiate_defined`<br>`APL.ProductAnnotations.Spec.instantiate_value` | Successful specification instantiation agrees with independent evaluation, with equivalent definedness and matching values under representation. |
| `ProductEntry.lean`<br>`APL.ProductEntry.runtime_leaves_count`<br>`APL.ProductEntry.parameter_model_rep`<br>`APL.ProductEntry.parameter_entry_exists`<br>`APL.ProductEntry.parameter_domain_satisfiable`<br>`APL.ProductEntry.parameter_entry_complete`<br>`APL.ProductEntry.parameter_entry_iff`<br>`APL.ProductEntry.parameter_initial_support`<br>`APL.ProductEntry.parameter_layout_length`<br>`APL.ProductEntry.parameter_body_entry`<br>`APL.ProductEntry.display_head_initial`<br>`APL.ProductEntry.display_head_increment`<br>`APL.ProductEntry.display_head_injective`<br>`APL.ProductEntry.display_head_order`<br>`APL.ProductEntry.display_head_parameter_disjoint`<br>`APL.ProductEntry.display_head_identity` | Typed runtime parameters construct a representing model; domain satisfaction conversely supplies typed parameters. Parameter layout length/support, body-entry reversal and display-to-logical head equations are preserved. |
| `ProductClauses.lean`<br>`APL.ProductAnnotations.Spec.clause_sound`<br>`APL.ProductAnnotations.requires_vc_sound`<br>`APL.ProductAnnotations.assertions_vc_sound` | Boolean clause instantiation, ordered requires definedness/truth, and independent assertion conjunction agree with mathematical specification semantics. |
| `ProductSupport.lean`<br>`APL.ProductFlow.merge_supported`<br>`APL.ProductFlow.merge_env_supported`<br>`APL.ProductAnnotations.Spec.instantiate_supported`<br>`APL.ProductAnnotations.Spec.clause_supported`<br>`APL.ProductAnnotations.requires_supported`<br>`APL.ProductAnnotations.assertions_supported` | Successful value/environment merges, specification instantiation, Boolean clauses, requires and assertions preserve the stated symbol-support bound. |
| `ProductRuntime.lean`<br>`APL.ProductFlow.runtime_literal_denotes`<br>`APL.ProductFlow.runtime_literal_supported`<br>`APL.ProductFlow.runtime_unary_sound`<br>`APL.ProductFlow.runtime_binary_sound` | Runtime literals denote bounded values and are supported; successful unary/binary symbolic operations with valid definedness match the actual checked runtime operation. |
| `ProductFlow.lean`<br>`APL.ProductFlow.group_exact` | The guarded-check conjunction holds exactly when every original guard implies its requirement. |
| `ProductFlowBounds.lean`<br>`APL.ProductFlow.analyze_bounded` | Successful analysis preserves the incoming fresh lower bound and establishes output support and boundedness. This is a symbol-support result, not generation completeness or a production resource bound. |
| `ProductFlowSemantics.lean`<br>`APL.ProductFlow.merge_flow_covered`<br>`APL.ProductFlow.runtime_tuple_value`<br>`APL.ProductFlow.runtime_project_value`<br>`APL.ProductFlow.args_fields_spec`<br>`APL.ProductFlow.arguments_sound` | Selected merged-flow coverage, actual tuple construction/projection, field/argument continuation specifications, and ordered argument analysis under the generator hypotheses. |
| `ProductFlowLoops.lean`<br>`APL.ProductFlow.loop_analysis_sound` | Successful invariant-loop analysis is sound under successful child analyses, support/representation, typed actual environments, valid checks and the actual-machine invariant rule. |
| `ProductFlowRules.lean`<br>`APL.ProductFlow.literal_sound`<br>`APL.ProductFlow.local_sound`<br>`APL.ProductFlow.assignment_analysis_sound`<br>`APL.ProductFlow.unary_analysis_sound`<br>`APL.ProductFlow.binding_analysis_sound`<br>`APL.ProductFlow.projection_analysis_sound`<br>`APL.ProductFlow.conditional_analysis_sound`<br>`APL.ProductFlow.strict_binary_analysis_sound` | Constructor soundness for literals, locals, assignment, unary operations, bindings, projection, conditionals and strict binary operations under their analysis and representation premises. |
| `ProductFlowBoolean.lean`<br>`APL.ProductFlow.logical_binary_analysis_sound` | Short-circuit Boolean analysis is sound with the selected operand state and guarded checks, under the stated child-analysis, typing and support premises. |
| `ProductFlowCalls.lean`<br>`APL.ProductFlow.call_analysis_sound`<br>`APL.ProductFlow.tuple_analysis_sound` | Call expansion and tuple construction are sound under ordered captured arguments/fields, typed complete tables, successful generation and valid checks. |
| `ProductFlowSoundness.lean`<br>`APL.ProductFlow.analyze_sound`<br>`APL.ProductFlow.analyze_run_sound`<br>`APL.ProductFlow.analyze_no_finite_trap`<br>`APL.ProductFlow.analyze_no_finite_invalid`<br>`APL.ProductFlow.analyze_normal_coverage` | Concrete analyzer soundness for every constructor, all actual transition budgets, exclusion of finite trap/invalid traces and coverage of every finite normal result. |
| `ProductContractClauses.lean`<br>`APL.ProductFlow.entry_checks_sound`<br>`APL.ProductFlow.entry_checks_supported`<br>`APL.ProductFlow.post_checks_sound` | Successful entry checks establish ordered definedness and an entry path; successful post checks establish all normal-return ensures with frozen parameters. Entry checks preserve support. |
| `ProductQueries.lean`<br>`APL.ProductFlow.exact_named_check_partition`<br>`APL.ProductFlow.grouped_checks_named`<br>`APL.ProductFlow.grouped_keys_distinct`<br>`APL.ProductFlow.named_queries_exact`<br>`APL.ProductFlow.named_query_checks_once` | Exact multiplicity-preserving check grouping, distinct group keys, homogeneous membership, semantic conjunction equivalence and preservation of each named occurrence. |
| `ProductContracts.lean`<br>`APL.ProductFlow.contract_eval_sound`<br>`APL.ProductFlow.contract_requires_defined`<br>`APL.ProductFlow.contract_reachable_iff`<br>`APL.ProductFlow.contract_accepted_eval`<br>`APL.ProductFlow.contract_accepted_run`<br>`APL.ProductFlow.contract_accepted_nonvacuous`<br>`APL.ProductFlow.root_contract_sound`<br>`APL.ProductFlow.contract_accepted_no_finite_trap`<br>`APL.ProductFlow.contract_accepted_no_finite_invalid`<br>`APL.ProductFlow.contract_accepted_normal`<br>`APL.ProductFlow.contract_accepted_entry_defined` | Contract continuation/run soundness, ordered requires definedness, equivalence of entry satisfiability with typed runtime witnesses, nonvacuity, root typing/framing, and finite-trace contract corollaries. |
| `ProductContractQueries.lean`<br>`APL.ProductFlow.named_groups_partition`<br>`APL.ProductFlow.named_groups_keys_distinct`<br>`APL.ProductFlow.named_groups_named`<br>`APL.ProductFlow.named_groups_exact`<br>`APL.ProductFlow.contract_queries_exact`<br>`APL.ProductFlow.entry_check_keys`<br>`APL.ProductFlow.post_check_keys`<br>`APL.ProductFlow.invariant_check_keys`<br>`APL.ProductFlow.contract_queries_sound` | Final named groups retain exact multiplicity and keys, including an empty body group when needed. Final query acceptance is exact; entry/post/invariant clause keys are indexed correctly; accepted contract queries imply all-budget machine safety and ensures. |

### Product proof boundaries

The theorem describes an independently typed mathematical generator and the
existing Lean machine. It does not prove source parsing or annotation
reconstruction, source binding or occurrence IDs, Rust generation, SMT rendering
or solver answers, countermodel decoding, or native execution. Structural formal
expansion sites are not a proof of production report provenance. Production
verification remains `smt-trusted`.

Successful generation remains a premise. The older scalar supplied-rank
generation-height theorem does not establish product generation completeness.
No product theorem establishes termination, solver completeness, sufficiency of
production resource bounds or correspondence to source or native execution.
Runtime budget exhaustion remains inconclusive. Earlier scalar and runtime
theorems retain their original statements and scopes.

## Axiom dependencies and trust

The original expression `infer_complete`, `infer_sound`, and `type_unique`
theorems use exactly `propext` and `Quot.sound`; the other expression theorems
use exactly `propext`. Every inventoried program theorem uses exactly `propext`
and `Quot.sound`, except `Program.resume_typed`, which uses only `propext`.
The VCG audit reports each theorem's transitive dependencies. Earlier generator
proofs use only `propext` and `Quot.sound`; fresh-identity uniqueness and the
invariant generator soundness proofs also use the permitted `Classical.choice`. No project
axiom, incomplete proof, native-evaluation trust axiom, or disabled kernel check is admitted. Kernel-reduced smoke examples use
`decide`, not native-evaluation proof shortcuts.

The axiom audit is an executable rejection check, not merely printed output.
Its allowable set is explicit, and all 558 names in the earlier APL inventory
are included. Its 72 modules are replayed in separate kernel-checker processes.
The additional ANL memory package has its own all-declaration audit and replay
list; the scope below describes its 72 source modules and three CLI entrypoints.
The source-level guard also rejects proof-bypass and unsafe declaration syntax.
The model's meanings, theorem statements, Lean kernel, allowed logical axioms,
host environment, and hardware remain assumptions. Replaying declarations does
not establish that the formal definitions match every intended ANL rule.

## Explicit gaps

FM-01 through FM-05 are discharged for the documented v0 scalar expression/function
model; local state and flat scalar products have the separate scoped results above. Typing
theorems alone do not establish termination or trap freedom. VCG guarantees
require accepted logical obligations and the documented expansion boundary.
No result establishes completeness at fixed CLI resource limits or correctness of source/module elaboration, Rust checking,
JSON-text interpretation or native compilation. The v2 reader acceptance theorem
establishes typing of its successful model result, with the narrower scope above. The expression syntax intentionally has no
call constructor; program terms use a separate type to make that boundary visible.

FM-06 remains open. Source-to-core correspondence has differential and negative
testing evidence. V2 reader acceptance soundness establishes typing of the
returned model input; it does not prove the Rust frontend, checker, serializer or
JSON-text interpretation correct. Source elaboration, including discarded-let
index shifts, is tested through the actual compiler export path.

FM-07 is partial: the call-free, finite call-expansion, loop-free local-state and
invariant-loop model generators, ordered callee precondition obligations, contract
soundness and the invariant generator's exact mathematical query partition are
checked. The separate merged product generator adds actual-machine safety,
normal-result/environment coverage, typed runtime entry witnesses and exact
contract-query acceptance under successful generation and the premises above. Sufficient symbolic expansion height is also proved for the invariant
generator given a supplied complete call rank. Rank existence/extraction, source
call-graph validation, source acyclic-expansion correspondence, separate
syntax-inlining preservation, production named-condition correspondence and the
production/SMT/solver bridges remain open. Runtime verification reports therefore
remain solver-trusted, including the production invariant-loop and flat-tuple
routes. Product generation completeness, solver completeness and production-bound
sufficiency remain open.

FM-08 is partial. The owned-buffer extension below proves canonical model
Core/MIR lowering and finite completed correspondence in both directions. It also
adds scoped ownership/loan safety. Optimization, production Rust and native-backend
correctness, general ownership and whole-language verification remain open.

## Owned buffers and Core/MIR correspondence

The `ANL.Memory` modules implement `anl-owned-buffers-v1` separately from the
historical APL namespaces, reusing flat-product scalar/value definitions. The
72-module extension includes the model, its proof companions, strict readers and
reference-output/IO definitions. Three separate CLI roots expose pair checking,
a raw reader probe and a resource-aware reference runner. Module count is not a
count of independent product guarantees.

Raw Core terms contain declared annotations, resource indices and heap site
numbers without hidden typing evidence. Raw MIR contains Temp/Slot/resource IDs
and declared counts. Raw machine states and worlds are executable finite data.
The independent judgments do not define typing or transitions as successful
checker/runner results. Complete checking includes every function and body,
unique IDs/names, signatures, annotations, admissible profile, entry and canonical
per-function heap sites. Recursive calls require no acyclicity premise.

| Scope | Statements and source | Precise guarantee |
| --- | --- | --- |
| Core static acceptance | `checkTerm_iff`, `checkProgram_iff`, `type_unique` in [MemoryTyping](ANL/MemoryTyping.lean) | Executable checking agrees with independent `HasType` and `WellFormedProgram`; ordinary and resource contexts remain independent |
| Concrete heap | [MemoryHeap](ANL/MemoryHeap.lean) | Executable finite LIFO store, fresh positive/empty identities, initialized fixed length, refusal/zero behavior, write frame/length preservation and exact normal close, under the world invariant |
| Core execution | [MemoryMachine](ANL/MemoryMachine.lean), [MemoryRun](ANL/MemoryRun.lean), [MemoryExecute](ANL/MemoryExecute.lean) | Independent steps and total executable step agree; determinism, stopped characterization, completed soundness/completeness and exact retained exhaustion prefix |
| Finite Core safety | `preservation`, `progress`, `no_invalid`, `entry_safety`, `normal_entry_cleanup` in [MemorySafety](ANL/MemorySafety.lean) | Checked entries preserve continuation/capability/world invariants over every finite prefix; normal entry leaves no owned storage or resource bindings |
| Loans and sites | `read_loan_prefix` in [MemoryLoans](ANL/MemoryLoans.lean), `entry_event_site` in [MemoryOrigin](ANL/MemoryOrigin.lean) | Read-loan contents survive each protected finite interval; events refer to sites in the recorded function’s checked body |
| Previous model embedding | [MemoryEmbedding](ANL/MemoryEmbedding.lean), [MemoryEmbeddingTyping](ANL/MemoryEmbeddingTyping.lean), [MemoryEmbeddingExecution](ANL/MemoryEmbeddingExecution.lean) | Separate memory-free typing/execution embedding connects the prior flat-product model under the stated embedding premises |
| MIR static model and lowering | [MemoryMirTyping](ANL/MemoryMirTyping.lean), `program_total_wellFormed`, `checked_program_lowers` in [MemoryLoweringProofs](ANL/MemoryLoweringProofs.lean) | Independent MIR judgments/checker and canonical lowering; checked Core has a well-formed deterministic lowered program with exact metadata/inventory |
| MIR execution | [MemoryMirMachine](ANL/MemoryMirMachine.lean), [MemoryMirRunProofs](ANL/MemoryMirRunProofs.lean) | Independent MIR steps, deterministic executable runner, completed and retained-prefix facts |
| Resource policy | [MemoryResources](ANL/MemoryResources.lean), [MemoryResourceRun](ANL/MemoryResourceRun.lean), [MemoryResourceAccounting](ANL/MemoryResourceAccounting.lean), [MemoryResourceDepth](ANL/MemoryResourceDepth.lean), [MemoryResourceEntry](ANL/MemoryResourceEntry.lean) | Tool results project to abstract prefixes; checked accounting/limits, independent expression nesting and normal-entry reservation cleanup; preflight blocks work before allocation |
| Strict document acceptance | `checkCoreDocument_iff`, `checkMirDocument_iff`, `checkDocuments_iff`, `accepted_documents` in [MemoryWireSafety](ANL/MemoryWireSafety.lean) | Successful actual reader/checker results provide independent whole-program typing and canonical pair acceptance |
| Local reference interface | [MemoryReferenceBounds](ANL/MemoryReferenceBounds.lean), [MemoryReferenceSafety](ANL/MemoryReferenceSafety.lean), [MemoryReferenceOutput](ANL/MemoryReferenceOutput.lean) | Actual checked execution projects to independent prefixes, excludes invalid, preserves accounting/depth/site properties and bounds event growth by administrative transitions; encoded byte buffer is bounded including its final LF |

The heap model separates positive request identities from empty activations even
when their numeric ordinals coincide. An eligible positive attempt consumes one
response and request ordinal on success or refusal; zero consumes neither. The
world tracks live owners and paired history without pretending the trace records
cell contents. Writes preserve other locations and length. Close requires the
exact top owner. Active capabilities are distinct; recursively suspended caller
descriptors may alias. Normal cleanup is not a trap-cleanup theorem: a trap
retains world, current activation and suspended callers.

The resource wrapper counts depth, expression/fill fuel, slots, live cells and
cumulative tuple fields independently of the unbounded semantics. `Accounted`
relates logical counts to state; `DepthReachable` supplies independent nesting
history rather than inferring depth correctness from stack length. A positive
representable allocation preflights cells, owner slot and fill fuel atomically
before abstract allocation constructs cells. A blocked operation takes no semantic
step or allocator response. Refusal retains spent fill fuel but refunds cells and
descriptor. Bookkeeping unwind does not invent release events. Host backing,
trace/replay capacity and implementation memory use are outside these counts.

### Completed Core/MIR simulation

[MemoryLoweringSoundness](ANL/MemoryLoweringSoundness.lean), in namespace
`ANL.Memory.Simulation`, exports:

- `core_entry_to_mir` and `mir_entry_to_core`: finite terminal executions in both
  directions from the checked entry under `Canonical p q` and the same allocator
  response function. The reverse theorem accepts a raw stopped endpoint and
  proves that a corresponding checked execution is terminal rather than invalid.
- `mir_entry_not_invalid` and `mir_run_not_invalid`: every finite reachable MIR
  prefix and every returned runner state excludes invalid.
- `core_completed_run_to_mir` and `mir_completed_run_to_core`: a completed runner
  result has a corresponding completed run at an independently chosen budget.
- `FinalRelated.world` and `FinalRelated.runtime`: exact final world equality,
  including initialized store contents, counters and ordered trace, plus the
  current/suspended activation and capability relation. Results agree on the
  ordinary value or trap; retained trap state is not discarded.
- `mir_normal_entry_cleanup`: normal entry return has `i64` type, no live owners,
  no active empties, no positive heap and no remaining resource bindings.

The simulation accounts for structural MIR steps and administrative
revoke/restore phases. It preserves source evaluation order, including skipped
negative-length initialization, initialization before target rejection, guards
before a write RHS, and full argument capture before a loan grant. Theorems do not
identify equal numeric step budgets, exhausted states, resource cutoffs, source
fuel or native allocation behavior.

[MemoryPairSemantics](ANL/MemoryPairSemantics.lean) exposes `simulation_canonical`
and the entry, completed-run, no-invalid and normal-cleanup theorems in both
`ANL.Memory.Pair` and `ANL.Memory.Wire`. Their premises are actual
`Pair.check p q = true` and `Wire.checkDocuments ct mt = .ok (p, q)` respectively.
This connects accepted concrete artifacts to the simulation rather than assuming
an external statement that they lower correctly. Pair acceptance requires full
validation and exact canonical lowering; it is not an optimized-program or
alpha-equivalence checker.

### Acceptance, tooling and remaining boundaries

The [buffer](../spec/owned-buffers.md), [MIR](../spec/memory-mir.md) and
[evidence](../spec/memory-evidence.md) protocols define the actual wire forms,
limits and CLI reports. Core logical depth 128 and formal JSON-container depth
1024 are separate bounds. The Rust reader has its smaller pinned parser-container
bound. Acceptance proofs concern the actual Lean functions' returned terms; they
do not prove UTF-8 decoding, JSON parsing, serialization/IO, Lean compilation or
runtime correctness. No per-artifact kernel certificate is generated by the CLI.

`Reference.execute_prefix` and `execute_event_bound` apply to every accepted
reference execution result, including resource/admin prefixes. A transition emits
at most one event, so a returned entry trace has at most the supplied transition
budget's events. `encode_bound` bounds the actual encoded ByteArray. The trace
projection theorem identifies the exported logical events; it is not an
end-to-end theorem about parsing the emitted bytes in another tool. Output-limit
and host failures remain infrastructure outcomes.

All new model declarations are covered by an explicit transitive axiom audit and
separate-process kernel replay. The allowed logical axioms remain `propext`,
`Classical.choice` and `Quot.sound`; generated constructor-index shims are limited
to the exact inventory in [ANL/Audit.lean](ANL/Audit.lean). This audit does not
validate the intended meaning of definitions or turn executable boundary probes
into theorems. The old APL sources and proof scope remain distinct.

The finite 53-row reference corpus and actual-artifact/native comparisons are
implementation evidence. They do not prove Rust source checking, source/module
lowering, native C/allocator correctness, general termination, host allocation
success, physical resource bounds, concurrent safety, general movable ownership,
heap contract verification, freestanding execution or an ANL OS. FM-06 remains a
production correspondence obligation; FM-07 does not gain heap SMT support; FM-08
now includes this finite canonical model lowering result but remains incomplete
for production transforms and native code.

## Unsigned-word model

`anl-words-v1` is cumulative over scalar, state, tuple and scoped-buffer semantics.
The namespaces `ANL.Word` and `ANL.Words` preserve the earlier definitions rather
than relabeling their theorems. Raw word width/payload/annotation combinations
remain independently checkable; the bounded runtime value wrapper is constructed
only after range validation. Heap cells and indices remain the old `i64` domain.

### Accepted primitive, static and machine scope

- `WordCore`, `WordArithmetic`, `WordBits`, `WordConversions` define exact closed
  widths, invalid raw inputs, checked/wrapping arithmetic, logical shifts and
  checked/low-bit conversions. Theorems characterize success and overflow/zero/
  invalid-count results, prove returned ranges, and cover full unsigned conversion
  paths and Euclidean negative truncation. Primitive `invalidInput` is a raw
  boundary, not a source-program trap.
- `WordsValues`, `WordsValueTyping`, `WordsCore`, `WordsTyping` establish the shared
  scalar/flat-product domain, operation typing, independent `HasType`,
  `ArgsTyped`, `WellFormedProgram`, full term/program checker equivalence, and
  invalid-operation exclusion under exact signatures.
- `WordsMachine` through `WordsExecute` cover concrete raw control/frames,
  independent steps, executable-step equivalence, determinism, retained completed/
  exhausted execution, continuation/layout safety, progress/preservation, finite
  no-invalid, loan preservation, canonical site origin and normal entry cleanup.
  Shared five-trap values retain the world and suspended state; traps do not close
  owners. Explicit conversions add a real continuation and metered entry.
- `WordsResources` through `WordsResourceEntry` define actual preflight and
  incremental meter updates, exact semantic prefixes, account/depth invariants,
  limits and normal releases. Depth uses independent nesting metadata rather than
  continuation length. Positive storage construction occurs only after atomic
  cell/slot/fill preflight. Structural zero administrative budget does not call
  the allocator. Host metadata unwind preserves the semantic machine and is not
  a normal-close event or a resumable accounting-state claim.
- `WordsLegacyCore`/`WordsLegacy` embed static syntax, values and typing.
  `embed_step` and `embed_execute` in `WordsLegacyMachine`, and
  `Tool.embed_run` in `WordsLegacyResources`, preserve the actual old operations,
  corresponding same-budget runner outcomes, exact world/trace and resource meter.
  These declarations are in `ANL.Words` and `ANL.Words.Tool`; they do not
  equate Core and MIR budgets.
- `WordsMir`, `WordsMirTyping`, `WordsLowering`, their lowering proofs, and
  `WordsMirMachine`/`WordsMirRun` with proof companions establish independent raw
  MIR checking, canonical static lowering, concrete MIR steps and executable
  finite-run correspondence. Raw invalid outcomes remain distinct from terminals.

The primitive, static, Core/resource/legacy and MIR execution packages have passed
independent source/API review, all-declaration axiom audits and separate-process
kernel replay under Lean 4.36.0. Allowed logical axioms remain `propext`,
`Classical.choice`, `Quot.sound`; generated constructor-index wrappers are checked
by exact type/body, not by a broad namespace exemption. These procedures do not
prove that the chosen mathematical definition captures every intended behavior.

### Accepted finite canonical Core/MIR simulation

`WordsSimulation*` and `WordsLoweringSoundness`, namespace
`ANL.Words.Simulation`, relate actual Core and MIR states through concrete
continuations, temporary/slot/resource bindings, scope frontiers and exact world
identity. `step_match` covers each typed related Core step by a finite MIR path;
zero-target-step cases decrease a concrete rank. The relation does not assume the
execution equivalence it is used to prove.

`core_entry_to_mir` and `mir_entry_to_core` establish both finite terminal
directions under canonical lowering and the same allocation response function.
The reverse direction accepts a raw stopped target endpoint and rules out invalid.
`core_completed_run_to_mir` and `mir_completed_run_to_core` give corresponding
completed runs at independently chosen budgets. `FinalRelated.world` and
`FinalRelated.runtime` preserve exact cells, owner/empty identities, counters,
ordered trace, values or the exact trap, and current/suspended capabilities.
`mir_entry_not_invalid`/`mir_run_not_invalid` cover finite prefixes and retained
runner states; `mir_normal_entry_cleanup` establishes normal i64 return with no
live owners or remaining accessible resources.

`WordsPairSemantics` supplies these entry, completed-run, invalid-exclusion and
cleanup corollaries from the actual `ANL.Words.Pair.check p q = true` premise.
Pair acceptance checks both complete programs and exact canonical lowering.
It is not alpha-equivalence, arbitrary optimization validation or source parsing.
The complete 33-module simulation package has independently passed fresh builds,
all-declaration audit, exact API comparison and separate-process kernel replay.

No theorem equates Core/MIR numeric budgets, exhausted states or tool resource
cutoffs. No general termination, source lowering, Rust implementation, generated C,
host allocator or native binary correctness follows. Heap views remain call-scoped;
this does not establish general movable ownership or concurrency.

### Reader, reference and trust boundaries

The new `WordsWire*`, `WordsPairWire*`, `WordsReference*` and three executable
entrypoints expose the cumulative model. The [word protocols](../spec/words-evidence.md)
specify their raw/pair/reference interfaces and retained incomplete prefixes.
Reader acceptance concerns actual decoded new constructors, operation tags, trap
mapping and resource runner. Old reader theorems and source compilation alone
do not establish a new v4 byte-to-execution claim.

Formal logical depth 128 and JSON-container depth 1024 are separate. Rust retains
its smaller pinned JSON parser envelope (127 admitted containers, rejection at
128). Parser/UTF-8/IO and output serialization, Lean compilation/runtime, Rust,
C and host behavior remain explicit trust boundaries. No CLI produces a per-input
kernel certificate. Finite examples and native comparisons supplement these
proofs and do not prove universal implementation equivalence.

Words add no SMT word theory or VCG rule. Every successfully checked v4 source
returns unsupported verification, even with ordinary-only clauses; rejected
word-dependent clauses are source errors. The full-language release requirements,
hardware operations, freestanding entry and the entire ANL-authored OS remain open.

## Boot static model and Core reader

The `ANL.Boot` namespace models the `anl-boot-core-v1` envelope with revision
`anl-boot-rv64-virt-v1`, ordinary `anl-words-v1` types/terms, and explicit raw
platform, role, effect and bodyless primitive declarations. Malformed metadata,
annotations, signatures and IDs remain representable before checking. The model
reuses the unchanged Words kernel; a platform declaration does not allocate
physical stacks or implement hardware effects.

| Source and theorem | Scope |
| --- | --- |
| [BootCheckProofs](ANL/BootCheckProofs.lean), `checkProgram_iff` | The actual Boolean checker accepts exactly independent `WellFormedProgram`: fixed metadata/roles, full ordinary typing, all-body memory/view exclusion, exact machine prefix, authority inclusion, declaration ordering/IDs/names, primitive discovery and acyclicity. |
| [BootGraphProofs](ANL/BootGraphProofs.lean), `acyclic_iff_cycleFree`, `checkGraph_cycleFree_iff` | The finite path-bound judgment and executable graph check are equivalent to absence of a positive-length cycle in the complete defined-call graph, including unused bodies and dead branches. |
| [BootCheckProofs](ANL/BootCheckProofs.lean) and [BootTableProofs](ANL/BootTableProofs.lean), `WellFormedProgram.call_target`, `primitive_id`, `primitive_keys_unique` | Admitted calls use actual-table targets, exclude role and synthetic entry IDs, and obey the prefix/effect policy. Primitive rows have canonical suffix IDs and unique first-use keys; all are used and at most ten are admitted. |
| [BootTail](ANL/BootTail.lean), `designatedTail_iff`, `SelectedTail.unique`, `noNormalReturn_iff` | The executable initializer-first search agrees with an independent selected-path judgment. Immutable and mutable let initializers take precedence over their bodies. Ordinary typing still checks every subtree. |
| [BootNoReturn](ANL/BootNoReturn.lean), `HasTail.no_normal_return`, `NoNormalReturn.no_value_terminal` | Over actual ordinary `Words.Step`/`Steps`, evaluating a certified body cannot finish with a returned value at the original continuation, or with an empty continuation. The continuation proof covers terminal loops in either child of immutable/mutable lets. |
| [BootCarrier](ANL/BootCarrier.lean), `carrier_wellFormed` | A well-formed boot program has a well-typed ordinary Words signature adapter. Its dummy primitive bodies and synthetic entry are proof devices, not a boot executable or hardware implementation. |
| [BootWireSafety](ANL/BootWireSafety.lean), `checkCoreDocument_iff` | Actual checked decoding succeeds exactly when raw decoding returns that program and its independent boot well-formedness judgment holds. Derived facts cover metadata, roles, effects, call bounds, cycles, primitive identity and static carrier typing. |

The no-normal-return theorems concern the existing ordinary machine and original
continuation. They allow a trap or invalid stopped state and do not prove
infinite progress, trap freedom, hardware delivery/reset, native loop preservation
or adequacy of a physical stack. No theorem here identifies unwrapped execution
of the hosted signature adapter with boot execution. The exported boot envelope
has no dummy bodies or synthetic entry.

The [static probe](README.md#boot-core-static-checking) uses
`Boot.Wire.readCore` and `checkCoreDocument` from [BootWire](ANL/BootWire.lean).
It checks every decoded definition, including unreachable code. Its raw metadata
and supplied annotations are checked rather than replaced by expected values.
The decoded-wire theorem is:

```text
checkCoreDocument text = .ok p
  ↔ readCore text = .ok p ∧ Boot.WellFormedProgram p
```

The 1MiB original-byte limit, logical depth 128 and formal JSON-container depth
1,024 are distinct. Rust's 127-container reader does not have the same admission
domain. The graph checker is a finite mathematical algorithm; its correctness
proof does not bound practical checking time for every byte-admissible table.
The probe emits no per-artifact kernel certificate.

These modules receive all-declaration axiom checking and separate-module kernel
replay. The same allowed logical axioms remain `propext`, `Classical.choice` and
`Quot.sound`. Byte decoding, JSON duplicate-key handling/parsing, I/O, Lean
compilation/runtime and production source-to-Core translation remain trusted or
separately qualified boundaries. Finite actual-export comparisons do not prove
universal Rust/Lean equivalence. Boot MIR admission/correspondence, device and trap
execution, ELF/ABI generation, firmware handoff and the complete ANL-authored OS
remain outside this proof slice.

### Ordinary boot source occurrences

The `ANL.Boot.Origin` model tracks the current defined function and structural
path through its Core body. Each continuation frame carries its parent occurrence;
call frames retain the caller's location while execution enters the callee.
Identical term text at two paths remains two distinct occurrences.

| Source and theorem | Scope |
| --- | --- |
| [BootOriginCore](ANL/BootOriginCore.lean), `lookup_iff`, `designatedTail_located` | Executable lookup agrees with an independent occurrence judgment. The checker-selected tail path locates its actual park loop. Primitive and synthetic bodies have no authored occurrence. |
| [BootOriginAdvanceProofs](ANL/BootOriginAdvanceProofs.lean), `step_iff`, `Step.erase`, `Step.deterministic` | The guarded executable step agrees with independent metadata transition rules, erases to an actual ordinary Words step, and is deterministic. Primitive invocation stops before entry into a dummy body. |
| [BootOriginAlignment](ANL/BootOriginAlignment.lean), `preserve`, and [BootOriginProgress](ANL/BootOriginProgress.lean), `lift`, `stopped_iff` | On well-formed, typed, aligned states, admitted ordinary steps preserve location/frame alignment. Every admitted Words step has a metadata step; stopping occurs exactly at a primitive invocation or ordinary terminal state. |
| [BootOriginReachable](ANL/BootOriginReachable.lean), `root_prefix`, `Steps.deterministic`, `root_prefix_selected`, `park_round` | Finite histories from an actual defined body preserve typing and alignment. A fixed-length history determines its locations, including the exact selected loop occurrence and its silent four-step round. |

Initial roots use the declared body's actual parameter environment, empty
continuations/resources, and the initial ordinary world. Root typing requires
the supplied arguments to have the declared types. Roles can be selected as roots;
ordinary calls still cannot enter roles, primitives or the synthetic adapter.
Alignment is an independent structural relation, not a claim that every aligned
raw state is reachable. Causal occurrence identity follows from the fixed root
and its actual step history, rather than equality of term text.

These theorems stop before hardware primitives. They establish no device effect,
trap-handler reset, delivery schedule, event history, runtime budget, Core/MIR
correspondence or native execution. Raw defensive guard failures remain distinct
from language traps; the typed, aligned theorem domain excludes those failures.

### Core boot effects and trap transitions

The `ANL.Boot.Runtime` model extends ordinary source-occurrence steps with
primitive capture, before/after delivery points, device and CSR transactions,
terminal-handler entry, and recognition of the selected park occurrence. Its
independent `BootStep` rules describe transitions from current state; they do
not define correctness by equality with the executable tick or a future trace.

| Source and theorem | Scope |
| --- | --- |
| [BootRuntimeInputProofs](ANL/BootRuntimeInputProofs.lean), `checkInput_iff` | Input checking agrees with independent bounds and delivery-scope rules. `ValidatedInput` carries this check once; ticking does not revalidate the complete read vector. |
| [BootRuntimeEntryProofs](ANL/BootRuntimeEntryProofs.lean), `enter_iff`, `Start.typed`, `HardwareReset.typed`, `LanguageReset.typed` | Entry uses the actual declared body, correctly ordered typed arguments, empty continuations/resources and root origins. Reset retains the ordinary world and records the abandoned state without fabricating heap cleanup. |
| [BootRuntimeTickProofs](ANL/BootRuntimeTickProofs.lean), `tickRaw_iff`, `tickRaw_step_iff` | The actual tick agrees with independent outcome and transition rules on raw states. The admitted transition is deterministic. |
| [BootRuntimeLaws](ANL/BootRuntimeLaws.lean), `pre_delivery`, `post_delivery`, `blocked_iff` | Before-delivery issues no primitive transaction or read. After-delivery retains the committed result and counters. A missing read response blocks with the state unchanged. |
| [BootRuntimeBoundaryProofs](ANL/BootRuntimeBoundaryProofs.lean), `clear64_testBit`, `primitive_grant_rejected`, `park_boot_seen` | CSR clearing follows the width-64 bit semantics; reserved primitive grants cannot enter fabricated bodies; the observed boot park cannot open a second delivery window. |
| [BootRuntimeResetProofs](ANL/BootRuntimeResetProofs.lean), `Start.invariant`, `HardwareReset.invariant`, `LanguageReset.invariant` | Checked start establishes the local runtime invariant, and handler reset preserves it from an existing invariant. |

Captured primitives retain their actual declaration, structural occurrence,
complete forward argument vector and transaction ordinal. Successful commit
adds one event and advances the ordinal once; a successful read consumes one
supplied byte. CSR writes reduce modulo 2^64. The hardware record describes
bounded CSR values and trap installation, not a UART emulator or a proof of
physical device effects. Language tags 1, 2 and 3 denote overflow, division by
zero and invalid shift; unsupported traps remain defensive invalid states.

Delivery is modeled only at the stated boundaries. A delivery before trap
installation is ineligible; delivery after installation sees the new marker.
Handler entry receives raw bounded `scause`, `sepc` and `stval`, including zero
`stval`. Park recognition uses the selected function and structural path, so
identical loop text elsewhere is insufficient. Each handler episode exposes
its park observation once. Event order is an export projection of a list built
by constant-time cons operations, with no reverse scan in each transition.

These modules establish single-step behavior and start/reset invariants. The
following preservation results extend them to finite execution prefixes.

### Checked boot execution prefixes

For a well-formed boot program and valid input, every finite execution from
the checked entry preserves typing, structural origins, the empty memory
world and the continuation barrier that prevents returning from an entry role.
The next tick either advances safely, blocks on an absent read response, or
retains the state at an ineligible delivery. It cannot report a defensive
invalid state under these premises.

| Source and theorem | Scope |
| --- | --- |
| [BootRuntimeOrdinarySafety](ANL/BootRuntimeOrdinarySafety.lean), `ordinary_local_preservation`, `OriginStep.response_irrelevant` | Ordinary steps preserve the local invariant, caller chain and empty resources. Their result does not depend on allocation responses. |
| [BootRuntimeInterceptionSafety](ANL/BootRuntimeInterceptionSafety.lean), `capture_complete`, `return_typed`, and [BootRuntimeInterceptionBoundary](ANL/BootRuntimeInterceptionBoundary.lean), `primitive_dispatch`, `primitive_return_retains` | A typed primitive frontier is intercepted before any carrier body executes. Its result has the declared type and returns through the actual retained caller continuation. |
| [BootRuntimeNoReturn](ANL/BootRuntimeNoReturn.lean), `BootStep.shield`, `BootStep.localSafety` | Ordinary, primitive, administrative and reset transitions preserve the continuation barrier and local safety. |
| [BootRuntimeSafety](ANL/BootRuntimeSafety.lean), `checked_entry_safety`, `checked_entry_progress`, and [BootRuntimeReachableFacts](ANL/BootRuntimeReachableFacts.lean), `checked_entry_not_invalid` | Every actual finite prefix from checked entry preserves the combined invariant and admits only the stated advance or blocking outcomes. |
| [BootRuntimeAuthority](ANL/BootRuntimeAuthority.lean), `PendingAt.authority`, `PendingAt.machine_authority` | The checked source occurrence supplies authority. Machine operations are confined to the three initialization call paths; ordinary primitive calls require the caller's device capability. |
| [BootRuntimeEventPrefixes](ANL/BootRuntimeEventPrefixes.lean), `checked_prefix_events`, `BootStepsN.ordered_event_prefix` | Committed ordinals are consecutive, consumed read values equal the supplied prefix, and at most one terminal reset occurs. Each successful step adds at most one event in execution order. |
| [BootRuntimeHandlerSteps](ANL/BootRuntimeHandlerSteps.lean), `HandlerAt.tick`, and [BootRuntimeReachableFacts](ANL/BootRuntimeReachableFacts.lean), `handler_prefix_retains` | The exact handler control shapes agree with the actual tick. Handler execution retains transactions, hardware, counters, delivery status and the interrupted snapshot. |
| [BootRuntimeSelectedSpin](ANL/BootRuntimeSelectedSpin.lean), `observed_park_resumes`, `selected_spin_retains`, `selected_park_not_observed_again` | Resuming an observed selected park takes one actual step into its literal-true loop, retaining its lower continuation and origin stack. Further steps cannot observe that park again. |

The safety invariant describes current control, handler shape and transaction
history independently of the executable tick or any future trace. Its history
component alone does not establish control reachability; that connection uses
the actual `BootStepsN` transitions from entry. Read payload projections leave
the unused input suffix intact. Ineligible delivery from a safe state occurs
before handler installation and before any installation event; it is distinct
from read exhaustion.

These are finite-prefix theorems. An ordinary helper may diverge before the
selected park; no eventual-park result is assumed.

### Finite boot execution and resumption

The boot runner stops at fresh handler entry or the selected park observation.
It checks for an observation before checking the remaining budget, including
zero. Without an observation, a zero budget returns the unchanged state as
exhausted. A successful tick consumes one step; a blocked read, ineligible
delivery or defensive invalid result consumes none. A supplied but unused
delivery is reported as `unobserved` only at a covered observation.

`resumeObserved` takes an observation premise and the existing validated input.
With a positive budget it performs one actual tick before running the remainder.
With zero it returns exhausted without advancing. Calling `run` again on an
unchanged observed state can report that same observation; explicit resumption
counts the transition that leaves it.

| Source and theorem | Scope |
| --- | --- |
| [BootRuntimeObservations](ANL/BootRuntimeObservations.lean), `observe_iff` | The state classifier agrees with independent handler-entry and selected-park relations. Raw shape recognition alone does not prove past execution. |
| [BootRuntimeRunAgreement](ANL/BootRuntimeRunAgreement.lean), `runRaw_iff`, `resumeRaw_iff` | The executable runner and resumption agree with independent finite relations over actual boot steps and outcomes. |
| [BootRuntimeRunBounds](ANL/BootRuntimeRunBounds.lean), `runRaw_prefix`, `runRaw_bound`, `run_checked_safety` | Every returned state follows exactly `used` successful steps, with `used` at most the budget. Checked execution preserves safety and excludes invalid results. |
| [BootRuntimeRunCompleteness](ANL/BootRuntimeRunCompleteness.lean), `runRaw_complete`, `runRaw_extend` | Completeness applies to prefixes with no earlier covered observation. Extending an exhausted run composes the actual prefixes. |
| [BootRuntimeObservationLaws](ANL/BootRuntimeObservationLaws.lean), `HardwareReset.observation`, `LanguageReset.observation`, `resume_observed_positive` | Actual resets produce handler observations. From a safe observed state, positive resumption performs a successful counted step. |
| [BootRuntimeObservationLaws](ANL/BootRuntimeObservationLaws.lean), `resume_park_exhausted`, `resume_park_retains` | Resuming an observed park exhausts its positive budget in the existing loop, retaining events, the read cursor and delivery-use state without another observation. |

These bounds count mathematical transitions. They do not bound host recursion,
memory, lookup cost or elapsed time. The modules do not define a runtime CLI or
wire protocol, a host resource policy, Core/MIR boot correspondence, native
stack/ELF/ABI qualification or firmware mediation. No native execution result
follows from these proofs.

### Tail-position execution and event offsets

`runTailRaw` and `resumeTailRaw` compute exactly the same results as the existing
runners for arbitrary raw states and budgets. Their accumulator places recursion
in tail position and counts only successful steps. Observation priority,
zero-budget behavior, blocking and invalid results remain unchanged.

| Source and theorem | Scope |
| --- | --- |
| [BootRuntimeTailRun](ANL/BootRuntimeTailRun.lean), `runAccum_eq`, `runTailRaw_eq`, `resumeTailRaw_eq` | Exact result equality for arbitrary programs, inputs, states and initial counts. |
| [BootRuntimeHistoryCounts](ANL/BootRuntimeHistoryCounts.lean), `History.event_count`, `BootStepsN.event_offsets` | Under independent History, the ordinal and episode determine event length. Finite prefixes identify the exact appended suffix and its offset. |
| [BootRuntimeTailLaws](ANL/BootRuntimeTailLaws.lean), `runTailRaw_safety`, `runTailRaw_event_offsets`, `resumeTailRaw_park_exhausted` | Safety, transition bounds, event offsets and selected-loop resumption transfer through exact equality. |

`State.eventCount` reads the ordinal and episode without traversing the event
list. Its length identity requires History; arbitrary forged summaries are not
certified. Source-level tail position does not establish native stack usage or
host resource bounds. Protocol encoding and native execution remain separate
obligations.

### Finite action sessions

`sessionRaw` validates the complete action-list shape before starting. The first
action is `run`; later actions may `continue` an exhausted state that has no
observation, or `resume` an observation. A zero-budget resume leaves that observation available.
An inapplicable action produces a rejection index without executing it. Blocking
or ineligible delivery stops the session before subsequent actions.

The session keeps one current state and immutable input. Each report row records
its action, successful-step count, cumulative count, event offset, read cursor
and delivery status. Rows refer to prefixes of one final ordered trace; they do
not store copies of prior states.

| Sources and theorems | Scope |
| --- | --- |
| [BootSessionCore](ANL/BootSessionCore.lean), [BootSessionPolicy](ANL/BootSessionPolicy.lean), [BootSessionMeaning](ANL/BootSessionMeaning.lean), `sessionRaw_ran_iff` in [BootSessionEntry](ANL/BootSessionEntry.lean) | Executable action selection agrees with independent applicability and actual `RunTo`/`ResumeTo` endpoints under well-formed program and valid input premises. |
| [BootSessionBounds](ANL/BootSessionBounds.lean), `SessionTo.summary`, `safe`, `rejection_index` | Exact cumulative successful transitions, budget bound, safety, executed action prefix and failed action index. |
| [BootSessionOffsets](ANL/BootSessionOffsets.lean), [BootSessionSlices](ANL/BootSessionSlices.lean), `entry_row_events`, `checked_offsets`, `EventSlices.growth` | Rows identify actual intermediate states and exact final-trace prefixes; adjacent event growth is bounded by the action's successful steps. |
| [BootSessionRunnerCalls](ANL/BootSessionRunnerCalls.lean), [BootSessionCalls](ANL/BootSessionCalls.lean), [BootSessionCostProofs](ANL/BootSessionCostProofs.lean), `GatewayCalls.poststart_counts` | Exact logical classifier/tick counts following the source branches, including applicability, row construction and final reporting. |
| [BootSessionExecutedBounds](ANL/BootSessionExecutedBounds.lean), `entry_executed_budget`, `entry_row_order` | Tick attempts fit the budgets of executed rows; row indices and cumulative counts follow their actual order. |

For a started session with `k` rows, `U` successful steps, `r` ordinary
run/continue rows and rejection indicator `delta`, the classifier count is
`U + r + 2*k + delta`. It is at most the sum of requested budgets plus three
times the number of requested actions. Tick attempts equal `U` plus at most one
final blocking attempt. Malformed action lists and failed starts perform no
classifier or tick calls and are outside the nonempty-row formula.

These counts describe source call sites, not elapsed time, allocation or native
instructions. The pure input domain remains `Nat`; delivery ordinals are not
restricted by action budgets. The reference layers below supply input limits and pure bounded result encoding.
Host stack/resource qualification, a session CLI and native correspondence
remain separate work.


### Reference input admission

The pure reference gateway accepts a strict Core document and a request for the
same checked program. Core admission limits the program to 128 declarations,
8,192 raw body nodes and 64 parameters or ordinary call arguments. Node counting
visits every constructor child, including unused and forbidden memory forms.
These caps precede the existing complete static checker.

Requests contain initial register words, a finite read-byte sequence, optional
scoped fault delivery and a nonempty action list. The first action must be `run`;
later actions must be `continue` or `resume`. The complete list is validated
before a runtime state is created.

| Limit | Bound |
| --- | --- |
| Request bytes / container depth | 1 MiB / 16 |
| Read bytes / supplied delivery-origin edges | 65,536 / 128 |
| Actions | 32 |
| Transitions per action and across all actions | 65,536 |

Delivery ordinals are positive uint64 values and may exceed the transition
budget. Register words use canonical unsigned decimal strings; read values are
bytes. An opaque device-tree word is an abstract input, without a physical-address
validity claim.

| Sources and theorems | Scope |
| --- | --- |
| [BootReferenceAdmission](ANL/BootReferenceAdmission.lean), `checkAdmission_iff`, `checkCoreDocument_iff` | Executable admission agrees with independent structural limits and the original strict Core checker. |
| [BootReferenceRequest](ANL/BootReferenceRequest.lean), `checkRequest_iff` | Scalar form, resource limits, action shape and actual input scope agree with independent request validity. |
| [BootReferenceRequestWire](ANL/BootReferenceRequestWire.lean), [BootReferenceInputProofs](ANL/BootReferenceInputProofs.lean), `checkDocuments_iff`, `checked_start_exists` | Strict decoded requests use the same admitted program and provide an actual valid runtime start. |
| [BootReferenceInputBounds](ANL/BootReferenceInputBounds.lean), `boundedArray_iff`, `array_limit_before_elements`, `checked_session_calls` | Array caps precede element mapping; checked requests bound logical classifier calls to 65,632 and tick attempts to 65,536. |

Error order follows the actual stages. Byte and depth guards precede shared JSON
parsing. Array counts precede element decoding; decoded scalar validation
precedes budgets, action shape and environment scope. An oversized collection
can therefore reject before a malformed unvisited element is inspected.

The decoding theorems are conditional on actual parser results. UTF-8, JSON,
lexical numeric checks and decoded-key handling retain their existing trust and
qualification boundary. The depth theorem proves that the concrete guard
succeeded, without an independent JSON-depth semantics theorem. These modules
provide no result encoder, IO/CLI, host allocation or stack bound, native
correspondence, or guest execution claim.


### Reference result projection and encoding

The pure result exporter projects a completed reference session without running
another transition or classifier. Independent relations describe values,
pending operations, phases, saved interruptions, action rows, final state and
unused input. Rows refer to offsets in one final event sequence. Checked-session
theorems connect them to actual finite runtime prefixes and read consumption.

| Sources and theorems | Scope |
| --- | --- |
| [BootRuntimeSavedPhase](ANL/BootRuntimeSavedPhase.lean), `checked_prefix_interrupted_source` | A retained interruption comes from an actual earlier reset source, with a finite-prefix split. |
| [BootReferenceProjectionCore](ANL/BootReferenceProjectionCore.lean), [BootReferenceProjectionGuards](ANL/BootReferenceProjectionGuards.lean), [BootReferenceProjection](ANL/BootReferenceProjection.lean), [BootReferenceProjectionValues](ANL/BootReferenceProjectionValues.lean), [BootReferenceProjectionProofs](ANL/BootReferenceProjectionProofs.lean) | Independent view relations, conversion equivalences and exact recovery when a summary or final view cannot be exported. |
| [BootReferenceProjectionContext](ANL/BootReferenceProjectionContext.lean), [BootReferenceProjectionSession](ANL/BootReferenceProjectionSession.lean) | Checked identity and role bounds, actual prefix/count/row/read conservation, stored-frontier next actions and status meaning. |
| [BootReferenceOutputJson](ANL/BootReferenceOutputJson.lean), [BootReferenceOutput](ANL/BootReferenceOutput.lean) | Guarded pure encoding, bounded event count and streaming fragments, with explicit trace omission on error. |
| [BootReferenceOutputMinimal](ANL/BootReferenceOutputMinimal.lean), [BootReferenceOutputBounds](ANL/BootReferenceOutputBounds.lean), `encodeResult_bound`, `encodePrestart_bound`, `encodeResult_nonerror` | Every result's actual ByteArray is at most 8,388,608 bytes including LF. Non-error result encoding requires a valid context, full projection and a successful bounded buffer. |

The encoder bounds the event count at 65,536 before reversing and streaming it.
Each event is validated before its fragment. The first shape or byte failure
produces an explicit error and a trace-free retry retaining the validated
summary and final state. A further failure uses a fixed unavailable-summary
envelope. Its actual UTF-8 byte bound is checked by kernel reduction; equality
with the structured JSON renderer is separately qualified for all four fixed
variants. Missing counters mean unavailable information, never fabricated zero
execution. JSON object-key order is non-normative; array order is preserved.

The additive `Output.Total` entrypoints preserve the original full-output
attempt and its first error. Their trace-free recovery has a successful-write
proof for every guarded projected report, with at most 630,041 actual bytes
including LF. Prestart errors likewise serialize successfully within 12,289
bytes, retaining their original status and bounded reason. Neither path relies
on a successful opaque JSON compression result. The defensive fixed envelope
remains for internal raw misuse; guarded recovery cannot reach it.

| Sources and theorems | Scope |
| --- | --- |
| [BootReferenceDecimalText](ANL/BootReferenceDecimalText.lean), [BootReferenceUtf8](ANL/BootReferenceUtf8.lean), [BootReferenceJsonString](ANL/BootReferenceJsonString.lean), [BootReferenceStringBytes](ANL/BootReferenceStringBytes.lean) | Canonical decimal values, actual UTF-8 byte counts, reason truncation and total string-escaping expansion bounds. |
| [BootSummaryWriterCore](ANL/BootSummaryWriterCore.lean), [BootSummaryWire](ANL/BootSummaryWire.lean), [BootSummaryCombinators](ANL/BootSummaryCombinators.lean) | Successful extension of every sufficient buffer prefix, with independent scalar, array and uniquely named object-field meaning. |
| [BootSummaryEnvelopeSpecs](ANL/BootSummaryEnvelopeSpecs.lean), [BootSummarySuccess](ANL/BootSummarySuccess.lean), `recovery_success`, `projected_recovery_success`, `prestart_success` | Concrete component bounds compose into actual successful trace-free summary and prestart writes, both below 1 MiB including LF. |
| [BootSummaryOutput](ANL/BootSummaryOutput.lean), [BootSummaryOutputProofs](ANL/BootSummaryOutputProofs.lean), `first_success_unchanged`, `projected_first_failure`, `encodeResult_nonerror` | The first full encoder and first error are preserved. Non-error results still require full projection; every result retains the 8 MiB output bound. These are pure entrypoints, with no hosted CLI activation. |

The output origin-path limit of 128 remains an explicit guard: these proofs do
not derive it from the input logical-depth limit. `Wire` uses the existing total
`Json.renderString` as an explicit diagnostic-string leaf; it is not a general
JSON parser theorem or an equivalence with opaque `Json.compress`. JSON parsing,
Unicode escaping semantics, UTF-8/ByteArray runtime behavior, peak host memory,
stack/time bounds, output IO and CLI routing remain separate obligations. These
modules do not establish native correspondence, guest execution or hardware
behavior.

## Conditional native call-frame algebra

`ANL.Boot.NativeFrame` models 64-bit addresses, byte memory, registers and an
abstract concrete-step relation. At caller entry SP `E`, a call at depth `d`
places a callee with bound `h` below `E - d`; its complete access spans are
separate from caller slots in `[E - d, E)`. Composed prefixes stay within the
upper bound `max(previous, d + h)`. The bound need not be reached.

| Sources and theorems | Scope |
| --- | --- |
| [BootNativeFrame](ANL/BootNativeFrame.lean), `frame_separated`, `frame_preserves_slots`, `write_prefix_noninterference` | Whole-byte caller-slot separation and preservation, conditional on the supplied finite run, frame bounds and complete write-effect contract. |
| [BootNativeFrameComposition](ANL/BootNativeFrameComposition.lean), `call_prefix_bound`, with `callee_prefix_rebased`, `sequential_peak` | Local and leaf contracts compose at actual caller SP `E - d`, with a maximum of sequential call bounds rather than their sum. |
| `continuation_aligned`, `return_low_bit_neutral`, `call_return_frame` | From the actual linking instruction at aligned PC `P`, the return is `P + 4`; clearing its low bit is neutral. The supplied return and ownership contracts preserve caller slots and callee-saved registers and identify the owned continuation. |
| `root_substitution`, `terminal_requirement` | A supplied stackless root contract establishes the declared stack with arbitrary incoming SP/RA. Separately supplied hardware/language root bounds fit a shared terminal reservation exactly when their maximum fits. This does not add either terminal bound to the abandoned boot continuation. |
| [BootNativeFrameCut](ANL/BootNativeFrameCut.lean), `linked_cut_prefix`, `nonlinking_cut_prefix` | A supplied linking or nonlinking transfer extends the actual finite run and frame prefix to the slot with an empty memory-access list, preserving caller slots and hardware state. Linking sets RA to `P + 4`; nonlinking preserves the actual incoming RA, including an earlier AUIPC result. Neither theorem executes the slot. |
| `independent_terminal_roots` | Supplied completed hardware and language roots establish separate frame prefixes and mapped access spans under a shared reservation bounded by their maximum. No interrupted boot-frame bound is added. |

`LocalPrefixContract`, `LeafContract`, `WriteSound`, `LinkSound`, `ReturnSound`
and `RootThunkContract`, together with `NonlinkingSound` for a nonlinking cut,
are explicit hypotheses, not facts inferred from a
binary or observations. Hardware state is separate; no universal fault rollback
is assumed. Theorems over finite prefixes do not establish termination or exact
peak reachability. Concrete instruction semantics, decoder/control-flow analysis,
compiler lowering, source-to-ELF refinement, root-thunk validation and hardware
entry remain separate obligations. These modules grant no positive native-image
admission and do not establish an ANL-authored operating system.

## Conditional native low-byte memory algebra

[BootNativeByteMemory](ANL/BootNativeByteMemory.lean), in namespace
`ANL.Boot.NativeByte`, uses the frame model's 64-bit words and byte memory.
Every access supplies a nonwrapping span. Supported load widths are 1, 2, 4
and 8 bytes; signed and unsigned loads use little-endian byte order.

| Theorems | Scope and premises |
| --- | --- |
| `unsignedLoad_low8`, `signedLoad_low8` | At a supported width, the loaded word's low byte equals the byte at the starting address. |
| `storeLE_base`, `storeLE_index`, `storeLE_outside` | A positive-width store writes the source low byte at its base, the corresponding encoded byte at each in-range index, and preserves bytes outside its span. |
| `unsignedLoad_after_store`, `signedLoad_after_store` | Supported store and load widths may differ; reloading at the same starting address preserves the stored low byte. Both spans must be nonwrapping. |
| `store_preserves` | An initially valid abstract memory map and a source fact denoting the stored low byte remain valid after a positive-width store: retain that fact at the base, forget facts for other overwritten bytes, and preserve facts outside the span. |
| `unsignedLoad_preserves`, `signedLoad_preserves` | An initially valid fact at the starting address describes the low byte of the corresponding supported load. |

`Fact` distinguishes unknown bytes, constants and origins interpreted by an
arbitrary valuation. These are memory-algebra results, not proofs of the Rust
map or register-transfer implementation. They do not establish instruction
refinement, device responses, ABI extension bits, caller/handler behavior or
source-to-native correspondence. The separate experimental
[UART inspection APIs](../spec/boot-bundle.md#conditional-v3-uart-inspection)
retain those boundaries. The model is included in the complete declaration
audit and separate kernel replay; the audit inspects the exact generated,
universe-parameterized `Fact` constructor-index wrapper without a general
unsafe allowance.

[BootNativeByteMemoryFull](ANL/BootNativeByteMemoryFull.lean) adds full-word
results. An eight-byte store followed by a signed or unsigned eight-byte load
at the same nonwrapping address returns the entire stored 64-bit word.
`AgreesOn` describes byte-for-byte agreement over a supplied span; disjoint
nonwrapping stores preserve that span, and agreement preserves its loaded
value. `reload_saved_eight` therefore recovers the stored word after any
supplied memory change that still agrees on those eight bytes. These statements
supply no concrete instruction, fault, permission or caller-frame contract.

## Conditional native low-byte register and state algebra

[BootNativeByteRegisters](ANL/BootNativeByteRegisters.lean) proves preservation
of low-byte facts for modular addition and bitwise AND with supplied integer
immediates, supplied LUI values and supplied AUIPC PC/immediate values.
`addi_writeback`, `andi_writeback`, `lui_writeback` and `auipc_writeback`
preserve `RegsHold`; `unknown_writeback` safely forgets the destination fact.
Writes to the zero register are discarded. The separate zero-value lemmas
preserve an initially zero register; they do not establish its initial value.

[BootNativeByteState](ANL/BootNativeByteState.lean) combines register and memory
facts under one arbitrary, fixed origin valuation. Register updates, supported
signed/unsigned loads and stores preserve `Inv`, given its initial validity.
Memory accesses retain the explicit nonwrapping spans and supported widths.
Reloading at the store's base preserves the source low byte at a nonzero
destination, including when source and destination coincide.
`finite_prefix` transports an initial invariant along supplied finite steps
whose preservation is separately established; it supplies no instruction-step
relation, progress or termination theorem.

These models do not connect decoded instructions or the Rust analyzer to the
mathematical operations. Immediate decoding, PC/effective-address agreement,
finite-map correspondence, device origins/responses, full-register ABI values,
caller/handler behavior and source-to-native refinement remain separate.
Both models participate in the declaration audit and separate kernel replay;
they add no unsafe-wrapper allowance.

## Conditional native device-origin algebra

[BootNativeByteDevice](ANL/BootNativeByteDevice.lean) connects supplied byte
responses and origin tags to the combined register/memory invariant.
`PreservesKnown` requires a supplied memory change to preserve each address
whose current fact is not unknown; unknown addresses may change.
`memory_preserves` and `inv_preserves` retain the corresponding facts under
that premise.

`read_preserves` installs a supplied, zero-extended byte and origin fact through
the existing register writeback operation, which discards writes to the zero
register. It requires the fixed origin valuation to interpret that token as the
supplied response, initial invariant validity and known-memory preservation.
`write_preserves_and_payload` proves low-byte equality with a supplied entry
argument when the source register carries its origin tag and that tag has the
supplied interpretation; it also preserves the invariant under the same memory
premise. `finite_origin_endpoint` extracts the interpreted byte from a final
register tag along a supplied finite trace with an initial invariant and
per-step preservation.

These are conditional equations. They do not establish that a device access
occurs, that a response arrives, that origin tokens are fresh, or that accesses
have a particular ordering. The model supplies no UART instruction semantics,
Rust-map correspondence, caller/handler contract, full-register ABI result or
source-to-native refinement. Its declarations are included in the complete
audit and separate kernel replay without adding an unsafe-wrapper allowance.

## Conditional selected native instruction model

[BootNativeByteWords](ANL/BootNativeByteWords.lean) defines a selected 32-bit
instruction decoder for ADDI, LUI, LD, LBU, SD, SB, the exact
`fence iorw,iorw` word `0x0ff0000f`, and the exact return word `0x00008067`.
Other encodings are rejected. Its concrete state contains a PC, registers and
byte memory. Fetch requires four-byte alignment, a nonwrapping instruction
span, a supplied fetch relation and execute permission, and an initially zero
x0 register.
Ordinary loads/stores additionally require nonwrapping, naturally aligned
spans, ordinary classification of every byte, access permission and supplied
completion. These restrictions describe this selected profile.

[BootNativeByteWordsProofs](ANL/BootNativeByteWordsProofs.lean) connects an
`OrdinaryStep` to an abstract `Lift` with the same concrete register/memory
result. `ordinary_preserves` and `normal_silent_preserves` preserve the low-byte
invariant from its initial validity, including the selected decoder result for
a silent normal step. Writes to x0 are suppressed, but LD/LBU to x0 still
require the memory-access premises. Return clears the low address bit;
four-byte return-target alignment is an explicit premise, and a return
preserves registers and memory. `normal_zero_preserved` retains x0 for every
normal-step constructor under its fetch premise.

Device and fence steps have separate actions and supplied completion
predicates. This checkpoint does not prove their memory invariant, occurrence,
ordering or response behavior. It also does not prove all RISC-V instructions,
Rust-decoder/map correspondence, complete UART leaf endpoints, caller/full-ABI
behavior or source-to-native refinement. The audit inspects only the three
named Op/AddressClass/Action constructor-index wrappers with empty universe
parameters and exact monomorphic type/body checks; all prior wrapper checks
remain in force. The three new modules have separate kernel replay entries.

## Conditional native UART literal fixtures

The [fixture sources and data](fixtures/native-uart/fixture.json) preserve seven
complete selected bodies, totaling 92 little-endian instruction words. The
`NativeByteWordsLiterals` module checks each exact decoding.
`NativeUartFenceCertificate` and `NativeUartByteCertificates` derive concrete
pre-return results from supplied normal-step sequences: one fence and full unit
zero, a completed device response in the pre-return result's low byte, or the entry argument's
low byte at the actual device write followed by full unit zero. They also derive
the instruction PCs, stack addresses and restored SP. Fetch, access permissions,
classification, normal completion and the stated entry/alignment conditions
remain explicit premises. These are fixed-artifact results, not a theorem about
all accepted Rust reports.

`NativeUartFenceRestoration` strengthens only the fence leaf. Agreement across
its actual fence cut on each of the two saved eight-byte slots yields full x1
and x8 restoration. An additional completed normal return and aligned entry RA
yield a return PC equal to that RA. The six read/write leaves permit arbitrary
post-device memory and have no saved-register restoration or executed-return
claim. None of these statements proves caller execution, exclusive frame
ownership, DMA/interrupt safety, fence ordering, progress or a complete ABI.

The `NativeUartFixtures` library uses a separate exact four-module inventory;
its audit checks every fixture-owned declaration with no unsafe allowance, and
each fixture has its own kernel replay. The generic ANL model audit and wrapper
policy are unchanged. Private qualification clients are not included.

The committed ANL source and six generated payloads accompany selected text
bytes, an extraction manifest and a clearly labeled report projection. The
read-only fixture checker verifies their public hashes, all 92 literal inputs,
PC arithmetic and seven identity/effect/return-location/byte-relation joins.
The projection omits private paths and observer register-restoration tokens;
its hash differs from the original report. Original whole ELF/image hashes are
historical provenance: the originals contain private debug paths and are not
published or reconstructed. Their extraction into the selected byte fixture
remains retained offline evidence, not a kernel-checked ELF parser, compiler
correctness theorem or proof that an image was loaded or executed. Generated C
and assembly are compiler output from ANL. Rust native-admission and
source-correspondence flags remain false.

## Boot v2 static model and Core reader

The separate `ANL.Boot.V2.Program` preserves raw metadata, declaration signatures,
ordinary bodies, and effects before checking. `Operation.legacy` retains the V1
operation family. `Operation.illegalInstruction` preserves its supplied natural
authority, which static policy requires to be zero. This is a distinct V2 model,
not a V1 program carrying an extra operation through a hosted entry.

| Sources and theorems | Scope |
| --- | --- |
| [BootV2CheckProofs](ANL/BootV2CheckProofs.lean), `checkProgram_iff` | The actual Boolean checker agrees with independent V2 well-formedness, including metadata, all-body ordinary typing, prefix and role policy, canonical primitive discovery, and acyclicity. |
| [BootV2GraphProofs](ANL/BootV2GraphProofs.lean), `checkGraph_cycleFree_iff` | The complete defined-call graph has no positive-length cycle, including unused definitions and dead branches. |
| [BootV2Authority](ANL/BootV2Authority.lean), `WellFormedProgram.illegal_call_only_boot`, `PrimitiveValid.illegal_signature` | Every syntactic illegal call belongs to the boot entry; its primitive has the exact empty-parameter, unit-result, machine-effect signature and zero authority. |
| [BootV2Carrier](ANL/BootV2Carrier.lean), `carrier_wellFormed`, and [BootV2TailBridge](ANL/BootV2TailBridge.lean) | The shared Words signature adapter is well typed. The designated-tail bridge excludes a returned value at the original ordinary-machine continuation. Its dummy bodies are proof devices, not an exception implementation. |
| [BootV2FaultProofs](ANL/BootV2FaultProofs.lean), `checkInput_iff`, `SiteValid.byte_bound`, `TransferValid.fixed_payload`, and `forwardedStatus_*` | Independent local predicates cover input presence, uint64 slot bounds and alignment, fixed payload fields, and the bounded status-bit calculation. They define no transition system or firmware behavior. |
| [BootV2WireSafety](ANL/BootV2WireSafety.lean), `checkCoreDocument_iff` | Checked decoding succeeds exactly when raw decoding returns the same V2 program and its independent well-formedness judgment holds. |
| [BootV2WireAdmission](ANL/BootV2WireAdmission.lean), `checkAdmission_iff`, `checkProbeDocument_iff`, `admission_precedes_static` | The separate structural admission predicate agrees with its Boolean check, composes with static checked decoding, and takes precedence over static rejection. |

The exact checked-reader statements are:

```text
Wire.checkCoreDocument text = .ok p
  ↔ Wire.readCore text = .ok p ∧ WellFormedProgram p

Wire.Admission.checkProbeDocument text = .ok p
  ↔ Wire.checkCoreDocument text = .ok p ∧ Wire.Admission.Admissible p
```

The reader constructs V2 directly and reuses the strict metadata, natural,
ordinary-term, and JSON readers. It does not replace malformed metadata or
nonzero authority with expected values. Admission reuses the existing whole-tree
node and call-arity counters, with 128 declarations, 8,192 raw nodes, and
64 defined parameters or call arguments. These are probe resource bounds,
not semantic restrictions or a theorem about host memory and elapsed time.

The fault input and event vocabulary in [BootV2FaultAPI](ANL/BootV2FaultAPI.lean)
keeps an abstract pending request distinct from a supplied forwarding response.
Its local predicates do not establish that execution reaches a request, that a
response arrives, that a handler runs, or that the interrupted continuation
cannot resume. These data definitions alone supply no transition or progress
theorem; the runtime relations below specify the separate model transitions.
The V1 runtime, session, and output theorems above do not
extend automatically to this V2 operation.

The module inventory, all-declaration audit, exact generated-wrapper allowlist,
and separate-module kernel replay cover this addition. The allowed logical
axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

Decoded acceptance does not certify JSON text against an independent parser
specification or prove compiler refinement. Actual compiler-export checks cover
only their retained artifacts and common admission domain. Boot MIR and origin
correspondence, linked instruction identity, native execution, firmware
forwarding, hardware delivery, and the complete ANL-authored OS remain outside
this static and wire gateway.

## Boot v2 origins, transitions and local coherence

The V2 runtime uses the actual `ANL.Boot.V2.Program`. It shares the
program-independent ordinary-machine operations and proof machinery, without
executing a V1 carrier program or its dummy primitive bodies. Source origins
remain attached to the active control and continuation stack.

| Sources and theorems | Scope |
| --- | --- |
| [BootV2Origin](ANL/BootV2Origin.lean), [BootV2OriginProofs](ANL/BootV2OriginProofs.lean) | Origins resolve against actual V2 defined rows, including role roots. Ordinary defined-target admission excludes role and non-defined targets; it never invokes the synthetic carrier entry. Origin-aware stepping agrees with independent action selection and application; preservation lemmas retain supplied typing and source alignment under their stated premises. |
| [BootV2RuntimeCore](ANL/BootV2RuntimeCore.lean), [BootV2RuntimeInput](ANL/BootV2RuntimeInput.lean) | State, phases, snapshots and events; checked input agrees with independent validity. Legacy delivery and fault response are distinct inputs, and after-operation delivery for an illegal operation is rejected. |
| [BootV2RuntimeEntry](ANL/BootV2RuntimeEntry.lean) | Raw start and reset use actual defined-row lookup. Typed entry requires V2 well-formedness, role signatures, typed arguments and the initial world; raw lookup does not enforce a signature dynamically. |
| [BootV2RuntimeEffects](ANL/BootV2RuntimeEffects.lean), [BootV2RuntimeEffectProofs](ANL/BootV2RuntimeEffectProofs.lean) | Legacy effects retain the exact V2 operation row and signature, with typed completion and an origin-preserving ordinary return bridge. |
| [BootV2RuntimeFrontiers](ANL/BootV2RuntimeFrontiers.lean), [BootV2RuntimeFrontierProofs](ANL/BootV2RuntimeFrontierProofs.lean) | Source-selected legacy and fault frontiers, check/predicate agreement, and distinct before, commit and raised validity. `FaultAt` omits installation, hardware validity and the counter; phase checks belong to command readiness. |
| [BootV2RuntimeCommands](ANL/BootV2RuntimeCommands.lean), [BootV2RuntimeCommandProofs](ANL/BootV2RuntimeCommandProofs.lean), `command_iff`, `atCut_iff` | Independent `Ready` and `Cut` relations agree with command selection and delivery cuts, with unique command and deterministic cut outcomes. |
| [BootV2RuntimeTick](ANL/BootV2RuntimeTick.lean), [BootV2RuntimeTickProofs](ANL/BootV2RuntimeTickProofs.lean), `execute_iff`, `tickRaw_iff`, `tickRaw_step_iff` | Independent `Execute`, `BootOutcome` and `BootStep` relations agree with the total functions. Outcomes are deterministic; stopped outcomes retain exactly the input state. |
| [BootV2RuntimeFaultLaws](ANL/BootV2RuntimeFaultLaws.lean) | Legacy delivery priority before fault commit, ordinal/latest-raised discipline, exact stable blocking for a valid pending fault with no response, and the fields retained or reset by forwarding. |
| [BootV2RuntimeCoherence](ANL/BootV2RuntimeCoherence.lean), [BootV2RuntimeMachineSafety](ANL/BootV2RuntimeMachineSafety.lean), [BootV2RuntimeInterceptionSafety](ANL/BootV2RuntimeInterceptionSafety.lean) | Independent local coherence, ordinary/legacy machine preservation, reset and fault preservation, and direct typing/alignment projections for the fields actually stored in a passive snapshot. |
| [BootV2RuntimeLocalPreservation](ANL/BootV2RuntimeLocalPreservation.lean), `ready_execute_coherent`, `tick_preserves_coherence`, `Reachable.coherent` | All commands preserve coherence under readiness, well-formed V2 source and valid input. Exact stopped-state retention extends this to total ticks; independently defined finite reachability inherits coherence from a valid start. |

Before raising, the positive request ordinal equals the current counter and the
fault response is unused. Commit additionally requires valid hardware and an
installed handler. Raising advances the counter to the request ordinal plus one
and records `latestRaised`; pending validity uses that post-raise counter. A
missing response blocks only a valid pending request. Invalid pending state is
not hidden by the absence of a response, and no legacy delivery is consulted
while fault-pending.

Forwarding consumes the response once, saves the actual `faultPending` caller
snapshot, and starts the hardware handler as a terminal root with empty
continuation and resource stacks. Its arguments are `[2, fault_pc, 0]`, stored
in reverse order in the ordinary environment. It retains the world, read cursor,
ordinal, legacy-delivery usage, interrupt-enable register and installed handler.
The status transformation clears SIE, sets SPP and copies the former SIE into
SPIE. Raw reset requires only the actual defined handler row; typed forwarding
adds well-formed-source, valid-input and initial-world premises.

`Coherent` is a local predicate, independent of `Reachable`, history and tick
outcomes. It includes active caller typing, source alignment, machine memory,
cursor and counter bounds, role/phase consistency, and only the fields present
in a saved snapshot. In particular, coherence of `faultCommit` does not require
an installed handler. A coherent uninstalled `faultBefore` state may advance to
commit and then produce `invalidState`. Preservation therefore does not imply
command eligibility or progress, nor does a static setup prefix substitute for
a dynamic installation proof.

These results do not port the V1 one-reset handler-history or session/output
theorems to V2. They prove neither global event-history restrictions nor eventual
delivery, handler progress or termination. The Lean runtime is a model, not a new
CLI execution mode. Boot MIR/origin refinement, Rust or native correspondence,
firmware behavior and complete OS implementation remain separate obligations.
The existing all-owned declaration audit and exact constructor-wrapper checks
apply to these modules, with the same three allowed logical axioms.

## Boot v3 static handler policy and reader

`ANL.Boot.V3` reuses `V2.Program`, `Defined` and `Declaration` as raw record types.
Its independent predicates and Boolean checks require the closed
`anl-boot-core-v3` / `anl-boot-rv64-virt-v3` / `rv64-virt-sbi-v3` metadata.
The hardware role may have empty effects or `[1]` (UART) and must contain a
sequencing-selected terminal loop. The language role retains empty effects and
the exact handler body. The boot setup, ordinary Words typing, no-memory policy,
role-call exclusion, primitive validity/discovery and acyclic graph checks are
shared with V2 without assuming V2 well-formedness for a V3 program.

| Sources and theorems | Scope |
| --- | --- |
| [BootV3Check](ANL/BootV3Check.lean) and [BootV3CheckProofs](ANL/BootV3CheckProofs.lean), `checkMetadata_iff`, `checkDefined_iff`, `checkDeclaration_iff`, `checkRoles_iff`, `checkProgram_iff` | Each actual Boolean check agrees with its independent static predicate. Whole-program well-formedness covers every declaration and syntactic branch, the boot and hardware terminal occurrences, exact language body, authority, canonical primitive discovery and acyclicity. |
| `WellFormedProgram.at`, `WellFormedProgram.memoryFree` | A declaration found in a well-formed program satisfies its declaration predicate; every found defined body is memory-free. |
| `MetadataValid.excludes_older_schema`, `WellFormedProgram.not_v2`, `checked_not_v2` | V3 metadata excludes the V1/V2 Core schema strings. V3 well-formedness excludes V2 well-formedness, and V3 checker acceptance implies V2 checker rejection. |
| [BootV3Wire](ANL/BootV3Wire.lean), `checkCoreDocument_iff`, `checked_wellFormed`, `checked_not_v2` | The checked reader accepts exactly a successful raw decoding satisfying V3 well-formedness. Acceptance implies V3 well-formedness and excludes acceptance of the same text by the V2 checked reader. |

The exact checked-reader statement is:

```text
ANL.Boot.V3.Wire.checkCoreDocument text = .ok p
  ↔ ANL.Boot.V3.Wire.readCore text = .ok p
    ∧ ANL.Boot.V3.WellFormedProgram p
```

The raw decoder is the existing V2 record decoder, which retains the supplied
metadata and ordinary body syntax. The V3 check supplies the distinct policy;
there is no conversion to a V2-well-formed program. Flat tuples remain part of
the ordinary Words type system. A selected terminal occurrence is structural
and does not prove that preceding computation reaches it.

These static results supply the V3 admission premises for the separate runtime
results below. The V2 theorems above retain their V2 premises. Neither static
policy nor the selected terminal occurrence establishes device completion,
firmware forwarding or source-to-native refinement.

## Boot v3 entry, local coherence and conditional capture

These modules reuse the raw V2 program, state, transitions and local coherence
predicate with independent V3 well-formedness premises. They do not relabel a V3
program as V2-well-formed or execute the ordinary carrier's synthetic entry and
dummy primitive bodies.

| Sources and theorems | Scope |
| --- | --- |
| [BootV3Carrier](ANL/BootV3Carrier.lean), `carrier_wellFormed` | V3 well-formedness implies well-formedness of the ordinary Words carrier, including defined-body typing, declaration names and IDs, and its synthetic entry. This is a typing bridge, not an execution theorem for the carrier. |
| [BootV3RuntimeEntry](ANL/BootV3RuntimeEntry.lean), `enter_typed`, `start_checked`, `hardware_reset_typed`, `language_reset_typed`, `forward_reset_typed`, `forwarding_checked` | Actual role entry and resets preserve typing, source alignment and active memory freedom under the stated V3, argument, input and initial-world premises. Forwarding existence additionally assumes a valid pending request and a supplied forwarding response. |
| [BootOriginCarrierPreservation](ANL/BootOriginCarrierPreservation.lean), `V2.Origin.preserve_carrier` | An actual admitted ordinary step preserves source alignment under carrier well-formedness, caller typing and initial alignment. It does not establish that a step exists. |
| [BootV3RuntimeCoherence](ANL/BootV3RuntimeCoherence.lean), `ordinary_local_coherent`, `start_coherent`, `hardware_reset_coherent`, `language_reset_coherent`, `legacy_return_coherent`, `forward_reset_coherent` | Local preservation for ordinary steps, start, legacy completion and reset, including typing/alignment of the actual stored snapshot. Hardware-to-language reset replaces the snapshot with the current interrupted caller. |
| [BootV3RuntimeLocalPreservation](ANL/BootV3RuntimeLocalPreservation.lean), `boot_step_coherent`, `ready_execute_coherent`, `boot_outcome_coherent`, `tick_preserves_coherence`, `reachable_coherent` | All actual ready/executed commands preserve local coherence. Stopped outcomes retain the state exactly; total validated ticks preserve coherence, and finite reachability from a valid start inherits it. No progress or command-eligibility premise is derived from coherence. |
| [BootV3Authority](ANL/BootV3Authority.lean), `WellFormedProgram.machine_call_only_boot`, `WellFormedProgram.illegal_call_only_boot` | Machine-effect primitive calls, including the illegal operation, can occur syntactically only in the boot role of a V3-well-formed program. All bodies and branches participate, including unused helpers and dead code. |
| [BootV3RuntimeCapture](ANL/BootV3RuntimeCapture.lean), `located_call_result`, `located_illegal_only_boot`, `captureLegacy_complete`, `captureFault_complete`, `primitive_capture_complete` | Typed, source-aligned primitive invocations with positive ordinals admit the corresponding captured request. Fault capture additionally assumes valid input, the boot episode and unused forwarding; source authority locates the illegal call in the boot role. |

The capture results construct `CapturedLegacy` or `CapturedFault` witnesses.
They do not assert that a command is ready, that a tick advances, that a read is
available or that a device operation completes. The combined capture theorem
retains the boot-episode and unused-forwarding premises even for its legacy
branch. Capture does not provide an installation proof or forwarding response.

The local coherence predicate is independent of history and reachability. It
covers active typing, source alignment, memory, hardware state, roles, phase,
cursor and ordinal bounds, and only fields present in a passive snapshot.
Blocked reads, absent forwarding, ineligible delivery and invalid outcomes are
preserved as stopped states. An uninstalled fault can still reach a commit that
reports `invalidState`; preservation alone does not rule that out.

These results prove no global handler-history restriction, eventual delivery,
read availability, handler progress or completion, or arrival at a selected park.
They do not establish compiler equivalence, Core/MIR origin refinement, native
instruction or Rust analysis correctness, firmware forwarding or device behavior.
The three older native identity interfaces continue to refuse V3. The separate
UART inspection interfaces admit only their conditional native leaf scope.
No runtime runner or command-line route is added. The complete declaration audit
and exact unsafe wrapper inventory remain in force with `propext`, `Classical.choice` and
`Quot.sound` as the only allowed logical axioms.
