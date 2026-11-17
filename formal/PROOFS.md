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

## Axiom dependencies and trust

The transitive dependencies of `infer_complete`, `infer_sound`, and `type_unique`
are exactly `propext` and `Quot.sound`. Each remaining inventoried theorem uses
exactly `propext`. None currently uses `Classical.choice`, although the project
policy permits it. No project axiom, incomplete proof, native-evaluation trust
axiom, or disabled kernel check is admitted. Kernel-reduced smoke examples use
`decide`, not native-evaluation proof shortcuts.

The axiom audit is an executable rejection check, not merely printed output.
Its allowable set is explicit, and all 21 inventoried names are included.
The source-level guard also rejects proof-bypass and unsafe declaration syntax.
The model's meanings, theorem statements, Lean kernel, allowed logical axioms,
host environment, and hardware remain assumptions. Replaying declarations does
not establish that the formal definitions match every intended APL rule.

## Explicit gaps

FM-05 is not discharged. `APL.Program.Step` specifies fuel-free recursive-call
transitions, and the executable program evaluator is tested, but preservation,
progress, and evaluator correspondence for global function environments and
calls are unproved. The expression syntax intentionally has no call constructor;
program terms use a separate type to make that boundary visible.

FM-06 is differential and negative testing evidence only. The Lean expression
checker's soundness theorem does not prove the Rust frontend, checker, serializer,
or either JSON adapter correct. Source elaboration, including discarded-let
index shifts, is tested through the actual compiler export path.

FM-07 and FM-08 are not implemented here. There is no VCG soundness theorem,
optimization/lowering theorem, native backend proof, ownership proof, or
whole-language verification claim in this inventory.
