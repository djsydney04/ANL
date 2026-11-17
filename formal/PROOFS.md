# Checked theorem inventory

Semantic revisions: `m1-2026-11-16` and `local-state-2026-11-17`. Proof tool: Lean 4.36.0, official release
commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The checking command is
`formal/check.sh` from the repository root with the pinned Lean tools on `PATH`.
It rebuilds all source, runs `APL/Audit.lean`, and replays the semantic modules
with `leanchecker`. The latter uses the Lean kernel; it is not an independently
implemented proof checker.

The inventory's variables quantify over the formal syntax and states. `Γ` is a
list of scalar types, newest binding first. `e` is untyped expression syntax;
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
trap freedom. No loop-invariant rule, variant, abrupt control-flow semantics,
or native-lowering theorem is included.

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
whole-program loop/recursion rejection is a separate check. The production
forward analysis, its correspondence to this CPS generator, named-query grouping,
source-contract correspondence, SMT translation, and solver evidence remain
unproved. Production loop-free mutable-code verification reports `smt-trusted`
results separately from these model theorems and retains
`termination_proved: false`. Loop-invariant reasoning,
fresh head symbols, and partial correctness of possibly divergent loops require
separate definitions and proofs.

## Axiom dependencies and trust

The original expression `infer_complete`, `infer_sound`, and `type_unique`
theorems use exactly `propext` and `Quot.sound`; the other expression theorems
use exactly `propext`. Every inventoried program theorem uses exactly `propext`
and `Quot.sound`, except `Program.resume_typed`, which uses only `propext`.
The VCG audit reports each theorem's transitive dependencies, which are confined
to `propext` and `Quot.sound`. None currently uses `Classical.choice`, although the
project policy permits it. No project axiom, incomplete proof, native-evaluation
trust axiom, or disabled kernel check is admitted. Kernel-reduced smoke examples use
`decide`, not native-evaluation proof shortcuts.

The axiom audit is an executable rejection check, not merely printed output.
Its allowable set is explicit, and all 134 inventoried names are included.
The source-level guard also rejects proof-bypass and unsafe declaration syntax.
The model's meanings, theorem statements, Lean kernel, allowed logical axioms,
host environment, and hardware remain assumptions. Replaying declarations does
not establish that the formal definitions match every intended APL rule.

## Explicit gaps

FM-01 through FM-05 are discharged for the documented v0 scalar expression/function
model; the local-state extension has the separate scoped results above. Typing
theorems alone do not establish termination or trap freedom. VCG guarantees
require accepted logical obligations and the documented expansion boundary.
No result establishes completeness at fixed CLI resource limits or correctness of source/module elaboration, Rust checking,
JSON adapters or native compilation. The expression syntax intentionally has no
call constructor; program terms use a separate type to make that boundary visible.

FM-06 is differential and negative testing evidence only. The Lean expression
checker's soundness theorem does not prove the Rust frontend, checker, serializer,
or either JSON adapter correct. Source elaboration, including discarded-let
index shifts, is tested through the actual compiler export path.

FM-07 is partial: the call-free, finite call-expansion, and loop-free local-state
generators, ordered callee precondition obligations, and contract soundness above
are checked. Source
call-graph validation, acyclic expansion completeness, separate syntax-inlining
preservation, named-condition decomposition and the production/SMT/solver bridges
remain open. Runtime verification reports therefore remain solver-trusted.

FM-08 is not implemented here. There is no optimization/lowering theorem, native
backend proof, ownership proof, or whole-language verification claim in this
inventory.
