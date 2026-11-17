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
