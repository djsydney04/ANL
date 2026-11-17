# APL formal core

This directory implements the `m1-2026-11-16` scalar function model and the
separate `local-state-2026-11-17` extension in Lean 4.36.0. It includes untyped syntax, declarative typing, independently checked
inference functions, and small-step evaluation machines. Type uniqueness,
preservation and progress cover scalar expressions and recursive global
functions. Finite evaluator correspondence is proved in both directions for
scalar expressions and recursive programs. Program completeness establishes the
existence of sufficient depth and fuel for a given finite reduction. Separate
verification-condition generators prove contract postconditions and trap freedom from interpreted logical obligations for call-free terms and
finite symbolic expansion of function bodies with callee preconditions.
The separate state-aware generator also covers loop-free mutable locals and
finite body expansion over the local-state machine. A separate invariant generator
proves finite-prefix trap freedom and partial correctness for possibly divergent
local-state loops under interpreted logical obligations.

The model covers bounded `i64`, `bool`, `unit`, lexical variables, immutable
lets, all scalar unary and binary operators, conditionals, and forward or mutually
recursive function calls. It is the first mechanized slice of APL. It does not
replace the complete-language roadmap.

## Build and check

Install the version named by `lean-toolchain` through an existing Lean/elan
installation, or put the corresponding official release's `bin` directory on
`PATH`. No third-party Lean packages are required.

From the repository root:

```sh
formal/check.sh
python3 formal/test.py
cargo build --locked
python3 formal/test.py --rust target/debug/apl
python3 formal/test_local_state.py --rust target/debug/apl
```

`check.sh` performs a clean build, rejects incomplete proof and custom axiom
syntax, audits the transitive axiom dependencies of 292 theorem names, and replays
33 semantic modules through separate `leanchecker` processes. Build warnings are errors.
The axiom audit fails on anything outside `propext`, `Classical.choice`, and
`Quot.sound`. The current proofs use these three permitted axioms; the fresh-identity
uniqueness and disjointness lemmas use `Classical.choice`.

The checked toolchain was the official
[Lean 4.36.0 release](https://github.com/leanprover/lean4/releases/tag/v4.36.0),
commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The macOS AArch64 release
archive's SHA-256 was verified as
`49acada8749ad1343eff1224a3d2510ac61ed53363d37b5e738e8c587e7deabd`.
The release is pinned; updating Lean requires repeating all checks.

An isolated installation at the repository's ignored
`.tools/lean-4.36.0-darwin_aarch64` can be used without changing global defaults:

```sh
PATH="$PWD/.tools/lean-4.36.0-darwin_aarch64/bin:$PATH" formal/check.sh
```

That local path is optional and platform-specific. The portable commands above
use the pinned version selected by the developer's toolchain manager.

## Executable reference

The built CLI accepts the shared [core format](../spec/core-format.md):

```sh
formal/.lake/build/bin/apl_formal spec/fixtures/core-expression.json
formal/.lake/build/bin/apl_formal spec/fixtures/core-program.json --fuel 100000
```

Both fixtures produce `{"outcome":"value","type":"i64","value":"42"}`.
The exit codes match the compiler's interchange CLI: 0 for a value, 1 for invalid
IR, 2 for an arithmetic trap, 3 for a resource limit, and 4 for an invocation or
file-access error. Output is one JSON outcome; file-access and invocation
messages go to stderr.

The reader rejects unknown/missing fields, duplicate object members, noncanonical
integer strings, decimal/exponent index representations, invalid UTF-8, unbound
locals, invalid function IDs, wrong arities, and inconsistent types. It checks
all functions and branches, including unused ones. Serialized `ty` annotations
are checked against inference. De Bruijn index zero denotes the newest local;
at function entry it denotes the final declared parameter.

V0 expression documents run `APL.run`, the evaluator covered by the expression
proofs. Each machine transition consumes one unit, and recognizing the terminal
state consumes one additional unit. A literal therefore needs two fuel units.
Fuel zero always yields `resource_limit`.

V0 program documents run `APL.Program.eval`, a separate executable evaluator that
supports named and mutually recursive calls. It charges one unit immediately
before evaluating each expression, with a global decreasing budget and a
256-expression nesting bound. Entry invocation is free; only evaluated arguments,
branches and operands consume fuel. Every finite value, trap or invalid outcome
is proved to have a matching reduction under `APL.Program.Step`. Under a
well-typed function table and term, returned values have the declared type and
`invalid` cannot occur. Conversely, every finite reduction from a term and value
environment with an empty continuation to a value, trap or invalid state has some
depth and fuel budget for which the evaluator returns that outcome. This does not
assert termination or completeness at the CLI's fixed depth bound of 256.
Resource exhaustion is not a terminal language result or proof of divergence.
Program execution is also covered by conformance tests.

The CLI bounds files at 1,048,576 bytes, JSON nesting at 256, expression trees at
128, and indices at 4,294,967,295. These limits and exhausted fuel report
`resource_limit`, except an out-of-range index is invalid IR. Different tools can
hit different bounds. Resource-limited comparisons are inconclusive about
language behavior; they do not establish divergence or type safety.

## Local scalar state

The v1 adapter accepts `apl-expr-v1` and `apl-core-v1` only with revision
`local-state-2026-11-17`. It adds initialized `let_mut`, assignment and structured
while loops according to [the local state specification](../spec/control-flow.md).
Old lets and parameters remain immutable. Imported expressions, including all
branches and unused function bodies, are checked before execution. V0 documents
still use their original adapter, evaluator and revision.

`APL.LocalState` is a separate machine. Its evaluation and return configurations
carry the current value environment. Operands, conditions, arguments and branches
consume that current environment. A binding pushes then pops one initialized
cell. Scope exit preserves changes to older cells. Arguments evaluate in order;
a call copies their values into a fresh parameter frame, then restores the caller
state captured after argument evaluation. Mutability belongs to the static
context, so runtime cells do not contain permissions or aliases. Loop condition
and body frames replace one another at each back edge. The final false condition
retains its effects.

The independent `Step` relation and executable `step` agree in both directions.
The finite `run` corresponds exactly to finite reductions ending at a stopped
state. Progress and preservation cover every constructor, scope transition,
recursive call and loop back edge. Well-typed programs cannot reach invalid
states; they may return a typed value, trap, or continue indefinitely. These are
type-safety results, not termination or trap-freedom results.

V1 CLI fuel counts machine transitions. A terminal state needs no extra unit to
recognize; a literal needs one unit and `while false { () }` needs three. The
machine uses a transition budget instead of Rust's expression-entry fuel and
separate expression nesting bound. Exhaustion in either implementation is
inconclusive. The model does not claim identical resource boundaries. Input size,
JSON nesting, expression depth and index validation remain as described above.

`LocalStateEmbedding` preserves v0 typing and proves that any finite v0 evaluator
value or trap has a matching v1 reduction and a sufficiently budgeted v1 run with
the same value or trap kind. Pure embedded terms also return their original
value environment. This is a forward preservation theorem; it does not equate
budgets or prove reverse divergence correspondence.

The v1 files separate concerns as follows:

- `LocalState.lean` defines terms, permissions, cell updates, configurations,
  independent reductions, and the finite executable machine.
- `LocalStateTyping.lean` proves inference equivalence, cell typing under update
  and scope removal, and preservation of every other cell by an assignment.
- `LocalStateRun.lean` proves executable/reduction correspondence and determinism.
- `LocalStateSafety.lean` proves configuration preservation, progress, finite
  safety, and recursive entry safety.
- `LocalStateEmbedding.lean` proves the v0 embedding statements above.
- `LocalStateExamples.lean` checks ordered argument mutation, isolated callees,
  effectful loop conditions, recursive calls, permission errors and budget edges
  by kernel reduction or simplification.
- `LocalStateWire.lean` and `test_local_state.py` provide strict v1 decoding and
  CLI conformance tests. The JSON adapter, production Rust implementation and
  native compilation remain tested boundaries, not consequences of these proofs.

## Loop-free local-state contracts

`APL.StateVCG` defines a concrete continuation-based generator for local-state
terms. A continuation receives both the symbolic value and updated environment.
Assignments use the environment returned by their RHS. Scope exit removes one
binding and retains outer writes. Conditions and left operands pass their final
state to the selected branch or right operand. Arguments evaluate left to right,
and the callee returns to the caller state captured after all arguments.

The generator reuses the existing mathematical symbolic terms and independently
interpreted formulas. It checks arithmetic guards and ordered callee
preconditions, then expands actual callee bodies. It rejects loops and fails if
the finite expansion height is exhausted. Both conditional branches and both
symbolic short-circuit paths must generate successfully.

`wp_trace` constructs an actual `LocalState.Steps` prefix ending at a returned
value and related final environment. Its arbitrary outer continuation is left
unexecuted. The run and trap-freedom theorems use an empty outer continuation.
For every transition budget, execution either exhausts its budget or returns a
value satisfying the generated postcondition. Successful generation and true
obligations also imply that some sufficient model transition budget exists.
This finite termination result is limited to the successfully expanded Lean
term. It does not establish source graph completeness or a production
termination claim.

`StateVCGContracts` freezes declaration-order entry parameter symbols for
specification interpretation. Runtime local environments use reversed parameter
order. Typed contract theorems require `LocalState.WellTyped`, a body typed under
immutable parameters, typed input values, accepted logical obligations, and true
entry preconditions. They establish the requested result type, postcondition,
and absence of finite traps or invalid states. The raw generator describes the
value-only machine and does not check static assignment permission.

These are model proofs. The production verifier separately supports loop-free
mutable scalar code with acyclic calls and reports `smt-trusted` results.
Source elaboration, graph validation, the production
forward analysis and its correspondence to this CPS generator, named query
grouping, SMT translation, and the solver remain outside the theorem boundary.
Production reports retain `termination_proved: false`. The separate invariant
generator described below is a model result; production loop verification remains
unsupported.

## Foundations for invariant loops

Three modules provide the frame, fresh-model and annotation foundations used by
the invariant generator below. The production frontend separately accepts and
erases typed source invariant clauses; these model proofs do not establish that
frontend's correctness or enable production loop verification.

`LocalStateFrame` proves that a finite typed evaluation preserves immutable entry
cells and binding types through scopes, calls, and loops. It also isolates a
first return to an untouched outer continuation. Merely starting and ending with
equal continuation lists is insufficient: an outer loop may have consumed and
recreated them. None of these frame results asserts termination.

`LoopVCGSupport` retains immutable head symbols, assigns distinct fresh identities
to every mutable numeric or Boolean cell, and uses literal unit for mutable unit
cells. Every typed concrete head agreeing on immutable values has a representing
model extension that preserves all earlier symbols. Consecutive allocations have
disjoint identities. The module also proves that grouping recorded guarded checks
as a conjunction preserves each check. The complete generator adds artifact
support and exact mathematical query partition; a global allocation-event
manifest and source query-metadata correspondence remain separate.

`LoopAnnotations` supplies pure mathematical assertions over current locals,
newest binding first, separately from declaration-order entry/result contracts.
Its `HasType` judgment means verification-ready annotated typing and requires
nonempty Boolean invariant lists. Ordinary source typing continues to accept
unannotated loops. Erasing annotation metadata preserves the actual Lean machine
at every identical budget, even when annotations are empty, ill typed, or false;
that erasure theorem does not establish annotation validity or source lowering.

## Invariant verification in the model

`LoopVCG` implements a concrete path-split generator for annotated local-state
terms, including nested loops, effectful conditions, short circuit and finite
callee-body expansion. It retains guarded checks separately from normal
outcomes, so a trap before an infinite loop cannot disappear when no return
follows. Initialization and preservation each require independently interpreted
invariant definedness and truth. An arbitrary loop head assumes the established
invariant and freshens all mutable nonunit cells; immutable cells remain stable
by the typed frame theorem. The final false guard passes its updated environment
to the continuation without requiring the head invariant to remain true there.

`LocalStateContinuation` and `LoopVCGSoundness` connect successful generation to
actual `LocalState.run` and `Steps`. Validity quantifies every fresh model extension
preserving earlier symbols. Complete generator induction discharges the child
specifications. At every transition budget, execution either exhausts or returns
a represented normal result; no finite trap or invalid trace exists under the
stated typing, support, representation and logical-validity premises. The syntax
expansion bound does not unroll loop iterations. No returning budget or termination
result is asserted.

`LoopVCGContracts` checks postconditions using original declaration-order parameter
symbols and the returned value. Its typed wrapper requires verification-ready
annotated function/body typing and typed actual inputs. Ordered requires
definedness must hold for every typed input, a typed satisfying input must exist,
and body/post checks must hold under all fresh extensions for satisfying inputs.
A safe infinite loop may satisfy a false postcondition; invariants have no global
satisfiability requirement. `LoopVCGQueries` proves that concrete tagging and
grouping preserve all original guarded checks and their mathematical validity.

These are model proofs. The production verifier still rejects loops. The formal
path-split generator differs from production merged flows; source lowering,
annotation attachment, named-query metadata, global allocation manifests,
production limits, SMT encoding, solver correctness and countermodel decoding
remain separate. Guarded head domains do not constrain an inactive head in every
mathematical model, so decoding policies must preserve that distinction. The
[proof inventory](PROOFS.md#invariant-loop-generation-and-partial-correctness)
records the precise theorem premises and remaining bridges.

## Model and evidence

- `APL/Core.lean` defines types, bounded values, untyped expressions, declarative
  typing, inference, checked arithmetic, and their basic theorems.
- `APL/Machine.lean` defines explicit environments, continuation frames, machine
  states, and typing judgments for intermediate configurations.
- `APL/Semantics.lean` defines the inductive, fuel-free `Step` relation and its
  finite closure. It proves preservation and progress and proves both directions
  of correspondence with the bounded executable machine.
- `APL/ProgramSemantics.lean` extends the mathematical small-step vocabulary with
  global functions and ordered arguments. Its relation has no fuel argument;
  infinite reduction represents divergence.
- `APL/ProgramTyping.lean` defines declarative program and argument typing,
  well-typed function tables, captured environments and continuation frames. It
  proves soundness and completeness of `Program.infer`, including calls, and
  uniqueness of inferred types. Function bodies are checked against the complete
  signature table, so forward and mutual recursion require no unfolding of calls.
- `APL/ProgramSafety.lean` proves preservation and progress for every program
  transition, finite reduction safety, exclusion of invalid states, and entry
  safety. No termination assumption is made. Kernel-checked examples cover mutual
  recursion, heterogeneous argument order, bad arity and unknown function IDs.
- `APL/ProgramEvalSoundness.lean` connects the actual bounded `Program.eval` to
  finite relation traces for values, traps and invalid inputs. It proves returned
  value typing and exclusion of invalid outcomes for well-typed programs.
- `APL/ProgramEvalCompleteness.lean` proves that every finite value, trap or invalid
  reduction from an evaluation state with an empty continuation can be reproduced
  by `Program.eval` with sufficient depth and fuel. The proof uses deterministic
  transitions and counted trace prefixes; it does not assume that programs end.
- `APL/VCG.lean` defines mathematical values, symbolic terms and formulas with
  independent interpretation, then a structural continuation-based generator for
  call-free program terms. Its soundness proofs connect valid generated formulas
  to the actual program evaluator and finite reductions, including arithmetic
  trap freedom, intermediate bounds, lexical substitution and short circuit.
- `APL/VCGContracts.lean` models the `apl-verify-v0` specification expressions,
  explicit parameter/result substitution, ordered precondition definedness and
  nonvacuous acceptance. It proves each accepted postcondition independently;
  mathematical specification integers are unbounded. Kernel-checked examples
  include increment and heterogeneous-parameter contracts, rejected
  contradictory/undefined preconditions, discarded overflow, the remainder
  overflow pair, and guarded division.
- `APL/VCGCalls.lean` extends the generator with ordered arguments, callee
  preconditions, and expansion of actual function bodies. Its soundness theorem
  covers the unchanged evaluator at any execution budget and finite reductions.
  `APL/VCGCallsExamples.lean` checks nested calls with mixed parameter types,
  argument trap order, rejected undefined or false preconditions, missing
  functions, wrong arity, and exhausted expansion bounds.
- `APL/StateVCG.lean` defines symbolic local-state updates and a finite expansion
  generator, proving direct trace and executable-run soundness over the existing
  `LocalState` machine. `APL/StateVCGContracts.lean` adds frozen parameter/result
  specifications and typed contract corollaries. `APL/StateVCGExamples.lean`
  checks RHS effects, scope exit, branches, short circuit, argument capture,
  isolated calls, a parameterized increment contract, arithmetic failure,
  false/undefined preconditions, and unsupported expansion cases.
- `APL/Program.lean`, `APL/Wire.lean`, and `Main.lean` implement program execution
  and strict interchange. The total program inference function is proved against
  declarative typing; the JSON adapter and executable compilation remain trusted
  or tested boundaries.
- `APL/Smoke.lean` contains kernel-reduced arithmetic, trap, short-circuit,
  scoping, and typing examples. `test.py` drives the actual executables against
  specified expected outcomes and a separate Python integer oracle, including
  deterministic generated terms and source-to-core recursive cases when Rust
  comparison is enabled.

The FM-07 foundation checks one postcondition at a time; absence of a requested
postcondition can use `true`. The original generator rejects calls. The call-aware
generator accepts only when symbolic expansion succeeds within a supplied tree
height, including both conditional branches and short-circuit operands. The bound
is independent of evaluator depth and fuel. At each call it checks lookup and
arity, inserts ordered callee precondition definedness and truth, and expands the
actual body under reversed argument symbols. Callee postconditions are not assumed.

This proves the Lean expansion generator sound when it succeeds. It does not
prove a source call-graph checker, that every acyclic source program has a
sufficient expansion bound, or equivalence with a separate syntax-inlining pass.
The invariant generator proves a mathematical check partition; correspondence
to production named conditions, Rust generation, source-contract erasure, SMT
encoding and solver evidence remains outside these proofs. `Accepted` means the
logical obligations hold and a typed satisfying input exists; a solver response
is not itself a proof of those facts. Runtime contracts remain erased.

The exact theorem statements, assumptions, and coverage are recorded in the
[proof inventory](PROOFS.md). These proofs concern the Lean model. They do not
prove the Rust parser, resolver, checker, exporter, interpreter, native
backend, runtime, OS, or hardware correct. Executing a compiled Lean evaluator
also trusts Lean compilation and its runtime; a kernel proof is separate evidence.
