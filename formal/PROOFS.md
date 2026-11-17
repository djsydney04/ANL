# Checked theorem inventory

Semantic revision: `m1-2026-11-16`. Proof tool: Lean 4.36.0, official release
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

## Axiom dependencies and trust

The original expression `infer_complete`, `infer_sound`, and `type_unique`
theorems use exactly `propext` and `Quot.sound`; the other expression theorems
use exactly `propext`. Every inventoried program theorem uses exactly `propext`
and `Quot.sound`, except `Program.resume_typed`, which uses only `propext`.
None currently uses `Classical.choice`, although the project policy permits it. No project axiom, incomplete proof, native-evaluation trust
axiom, or disabled kernel check is admitted. Kernel-reduced smoke examples use
`decide`, not native-evaluation proof shortcuts.

The axiom audit is an executable rejection check, not merely printed output.
Its allowable set is explicit, and all 44 inventoried names are included.
The source-level guard also rejects proof-bypass and unsafe declaration syntax.
The model's meanings, theorem statements, Lean kernel, allowed logical axioms,
host environment, and hardware remain assumptions. Replaying declarations does
not establish that the formal definitions match every intended APL rule.

## Explicit gaps

FM-01 through FM-05 are discharged for the documented scalar expression/function
model. This does not establish termination, trap freedom, completeness at fixed
CLI resource limits, or correctness of source/module elaboration, Rust checking,
JSON adapters or native compilation. The expression syntax intentionally has no
call constructor; program terms use a separate type to make that boundary visible.

FM-06 is differential and negative testing evidence only. The Lean expression
checker's soundness theorem does not prove the Rust frontend, checker, serializer,
or either JSON adapter correct. Source elaboration, including discarded-let
index shifts, is tested through the actual compiler export path.

FM-07 and FM-08 are not implemented here. There is no VCG soundness theorem,
optimization/lowering theorem, native backend proof, ownership proof, or
whole-language verification claim in this inventory.
