# ANL formal core

This directory implements the `m1-2026-11-16` scalar function model and the
separate `local-state-2026-11-17` and `flat-products-2026-11-17` extensions in Lean 4.36.0. It includes untyped syntax, declarative typing, independently checked
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

The original model covers bounded `i64`, `bool`, `unit`, lexical variables, immutable
lets, all scalar unary and binary operators, conditionals, and forward or mutually
recursive function calls. It is the first mechanized slice of ANL. It does not
replace the complete-language roadmap. The separate `ANL.Memory` extension now
models `anl-owned-buffers-v1`, with scoped `i64` owners/read-edit views, finite
Core/MIR correspondence, strict artifact acceptance and resource-aware reference
execution. Its [coverage](PROOFS.md#owned-buffers-and-coremir-correspondence) does
not extend the SMT contract generators to heap programs.

## Build and check

Install the version named by `lean-toolchain` through an existing Lean/elan
installation, or put the corresponding official release's `bin` directory on
`PATH`. No third-party Lean packages are required.

From the repository root:

```sh
formal/check.sh
python3 formal/test.py
cargo build --locked
python3 formal/test.py --rust target/debug/anl
python3 formal/test_local_state.py --rust target/debug/anl
python3 formal/test_flat_products.py --rust target/debug/anl
```

`check.sh` performs a clean build, rejects incomplete proof and custom axiom
syntax, retains the earlier APL audit of 558 named theorems and 72 module
replays, and adds the ANL memory all-declaration audit and separate replay list.
The memory package contains 72 source modules plus three CLI entrypoints; the
umbrella and audit are tooling, not additional proof claims. Build warnings are errors.
The logical axiom audit fails on anything outside `propext`, `Classical.choice`,
and `Quot.sound`. The memory audit separately inspects the exact generated
constructor-index wrappers listed in `ANL/Audit.lean`; it grants no general
unsafe-code allowance. The current proofs use these three permitted axioms; the fresh-identity
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
formal/.lake/build/bin/anl_formal spec/fixtures/core-expression.json
formal/.lake/build/bin/anl_formal spec/fixtures/core-program.json --fuel 100000
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

These are model proofs. The production verifier separately supports mutable
scalar and flat-tuple code with annotated loops and acyclic calls and reports
`smt-trusted` results.
Source elaboration, graph validation, the production
forward analysis and its correspondence to this CPS generator, named query
grouping, SMT translation, and the solver remain outside the theorem boundary.
Production reports retain `termination_proved: false`. The separate invariant
generator described below is a model result; it does not certify the production
invariant-loop verifier.

## Foundations for invariant loops

Three modules provide the frame, fresh-model and annotation foundations used by
the invariant generator below. The production frontend separately accepts and
erases typed source invariant clauses; these model proofs do not establish that
frontend's correctness or certify production loop verification.

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

These are model proofs. The production verifier supports annotated loops with
solver trust. The formal
path-split generator differs from production merged flows; source lowering,
annotation attachment, named-query metadata, global allocation manifests,
production limits, SMT encoding, solver correctness and countermodel decoding
remain separate. Guarded head domains do not constrain an inactive head in every
mathematical model, so decoding policies must preserve that distinction. The
[proof inventory](PROOFS.md#invariant-loop-generation-and-partial-correctness)
records the precise theorem premises and remaining bridges.

## Sufficient symbolic expansion height

`LoopGenerationComplete` proves that the existing invariant generator succeeds
at a sufficiently large height for verification-ready typed annotated functions
and terms, typed result-free preconditions, a supplied decreasing natural call
rank, and symbolic locals of the static context's length. The rank must cover
every syntactic call, including calls in arguments, dead branches and loop
conditions/bodies. Its existence and extraction from a source graph are separate
questions.

The bound is explicit: if `B` is one plus the sum of all function-body node
counts, a term with call-rank ceiling `r` generates at `r * B + nodes(term) + 1`.
`LoopGenerationCorollaries` also supplies a single height for the entire finite
function table. These heights work for arbitrary symbolic contents, incoming
paths and initial fresh counters; every output environment preserves the static
context length. Sibling arguments, outcomes and branches reuse the smaller child
height, so it is not a sequential work budget.

No formula truth, arithmetic definedness, satisfiability, value denotation or
runtime safety is assumed to prove generation. False or undefined typed
assertions still generate obligations. A checked witness combines successful
generation of an infinite loop with absence of a completed machine run at every
finite budget. The result concerns finite expansion in the unbounded model; it
provides no production work/memory bound, runtime termination result or
completeness at fixed Rust limits. The existing soundness theorem still requires
its separate support, representation and logical-validity premises. See the
[exact inventory](PROOFS.md#sufficient-generation-height-with-a-supplied-call-rank).

## Flat scalar products

The separate `APL.FlatProducts` model adds tuples of one through eight scalar
fields to the complete local-state machine, including mutable cells, scopes,
branches, effectful loops and recursive calls. It wraps the existing scalar types
and values and reuses their checked arithmetic. Unit is distinct from a singleton
tuple. Construction captures fields left to right while threading their effects;
projection evaluates its base once and consumes the completed tuple. Equality
and inequality compare same-shaped values after both operands have run. Assignment
replaces a whole value, and calls preserve argument snapshots and caller isolation.

Raw syntax still admits ill-typed terms. Independent declarative typing and
executable inference are proved equivalent and give unique result types. Typed
environment and continuation rules cover construction prefixes, projections,
scope exit and saved caller state. Under a well-typed function table and typed
starting state, preservation and progress exclude invalid behavior along every
finite trace. Defined arithmetic traps remain permitted. A completed actual run
returns the declared type or a defined trap; no theorem promises completion.

The independent `Step` relation and executable `step` coincide on all raw states.
Finite `run` outcomes have matching stopped traces, and every finite stopped trace
has some sufficient transition budget. The forward embedding maps every old
`LocalState` transition and preserves its finite values, final environments and
traps with sufficient new budgets. All preceding scalar definitions and theorem
statements remain unchanged. See the [55-statement product inventory](PROOFS.md#flat-scalar-products-with-local-state)
for exact premises.

These are runtime-model guarantees. They do not extend the scalar verification
condition generators to tuples. Production [tuple verification](../spec/flat-products.md#verification-boundary)
is separately implemented and remains solver-trusted. These runtime theorems do
not establish source lowering, JSON decoding,
Rust evaluation, shared-storage reclamation, native correctness, ownership,
termination or completeness at fixed production limits. Mathematical transition
budgets differ from production expression, depth, allocation and slot limits.
The nineteen private boundary examples are kernel checked but do not inflate
the public theorem inventory.

### Flat-tuple contract verification model

The separate `APL.ProductFlow` generator merges one symbolic value, environment
and normal-return guard while retaining every guarded check. It covers the
existing tuple machine's constructors, including state, calls and annotated
loops. `APL.ProductFlow.analyze_sound` requires successful generation, a typed
complete erased table and bounded symbolic support. Given a typed represented
runtime environment, an established path and universally valid guarded checks,
it proves actual-machine safety at every budget and coverage of every normal
value and final environment by an agreeing model extension.

`APL.ProductFlow.contract_queries_sound` connects semantic acceptance of generated
queries to that machine and all normal ensures. Its premises include a typed
complete annotated table, successful contract generation, and typed input values
satisfying requires. Separate entry results establish ordered definedness and
equate entry satisfiability with a typed runtime witness. The root theorem adds
function-table lookup, result/environment typing and immutable-binding preservation.
Query partition preserves check multiplicity and each original guard.

These statements permit divergent execution and inconclusive exhausted budgets.
They do not establish product generation completeness, solver completeness or
production-bound sufficiency. Source annotation reconstruction, source identities,
Rust generation, SMT/solver correspondence and native execution remain separate
obligations. See the [merged product inventory](PROOFS.md#merged-flat-tuple-contract-verification)
for the exact names, premises, module list and query boundary.

### V2 interchange adapter

The separate `anl_formal_v2` executable accepts `apl-expr-v2` and `apl-core-v2`
with revision `flat-products-2026-11-17`. The existing `anl_formal` executable
and its v0/v1 readers are unchanged. To export and compare a tuple program:

```sh
target/debug/anl dump-core examples/tuples/snapshots.anl > /tmp/anl-tuples.json
formal/.lake/build/bin/anl_formal_v2 /tmp/anl-tuples.json --fuel 100000
formal/.lake/build/bin/anl_formal_v2 /tmp/anl-tuples.json --revision
python3 formal/test_flat_products.py --rust target/debug/anl
```

`APL/FlatProductsWire.lean` checks exact members, duplicate keys, canonical i64
strings, tuple widths and field types, all function signatures and bodies,
permissions, entry rules and serialized type labels before execution. Expression
artifacts reject calls, including calls in dead branches. A lexical check rejects
negative, fractional and exponent index tokens before JSON normalization;
projection also checks the inferred base shape. Tuple outcomes contain an ordered
array of canonical i64 strings, JSON Booleans and nulls, with the same ordered
shape and length as the type array.

`APL/FlatProductsWireSafety.lean` proves acceptance soundness for the existing
`document` and `decode` definitions. A successful expression result is closed and
typed under empty signatures. A successful program result has a well-typed
complete function table and a nullary i64 entry. The proof connects the first
signature pass to the actual reconstructed table, including unused functions.
For every fuel budget, `execute` on that accepted input cannot return `invalid`,
and any returned value has the expected type. Defined traps and resource limits
remain allowed. See the [reader theorem inventory](PROOFS.md#v2-reader-acceptance-soundness).

Scalar-only explicit v2 documents are accepted. `--revision` reports their lowest
applicable semantic class, checking unused signatures and bodies as well. V2
execution always uses `FlatProducts.run`: fuel counts machine transitions, not
Rust expression entries. Input bytes, JSON nesting and expression depth have the
adapter bounds described above. Exit and error outcome forms match the original
CLI. Resource exhaustion is inconclusive about language behavior.

`test_flat_products.py` exercises both actual CLIs with hand-derived finite
values/traps, malformed hand-authored artifacts, fresh source exports and old
scalar embeddings. It distinguishes JSON Booleans from numbers and unit from a
singleton unit tuple. Generated byte/depth probes avoid large committed fixtures.
Separate cases expose differing Rust/Lean fuel and depth limits; resource outcomes
are reported separately from finite agreements. Use `--formal`, `--old-formal`
and `--report` to select built executables or save command evidence. This tests
JSON-text interpretation, serialization and compiled execution as trust
boundaries. Acceptance soundness does not prove that text has its intended
meaning, that every legal document is accepted, or that Rust and native execution
agree with the model. It produces no kernel certificate for individual file bytes.

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

## Owned buffers and memory artifacts

The [buffer specification](../spec/owned-buffers.md) defines `heap`, buffer access,
one read/edit call view, allocation profiles and Core v3. The
[MIR specification](../spec/memory-mir.md) defines resource IDs, guarded operations
and canonical lowering. The [proof inventory](PROOFS.md#owned-buffers-and-coremir-correspondence)
separates static typing, finite heap/capability safety, resource accounting, strict
reader acceptance and completed Core/MIR correspondence.

From `formal/`, build the three developer tools:

```sh
lake build anl_memory_pair_checker anl_memory_raw_probe anl_memory_reference_runner
```

From the repository root, a fresh export and pair check use:

```sh
cargo run --release --locked --features memory-evidence --example memory_evidence -- examples/buffers/basic.anl /tmp/anl-buffer-export
formal/.lake/build/bin/anl_memory_pair_checker /tmp/anl-buffer-export/core.json /tmp/anl-buffer-export/mir.json
```

Pair acceptance supplies the actual `Pair.check`/`Wire.checkDocuments` premises.
It validates both whole programs and exact canonical lowering, with no alpha
renaming or optimized-MIR acceptance. Rejection does not establish either
artifact's individual typing. The raw probe is a boundary diagnostic tool; its
acceptance is not a translation or execution certificate.

The reference runner accepts exactly `CORE_JSON RESPONSE_PLAN_JSON FUEL TRANSITIONS`.
The plan gives a bounded response vector and mandatory default response. The
runner uses checked `Tool.start?`/`Tool.run`, with expression/fill fuel distinct
from administrative transitions. Every result retains the exact reached state;
zero administrative budget does not evaluate a pending allocation. The
[protocol](../spec/memory-evidence.md#formal-reference-runner) defines arguments,
limits, report fields and exit statuses, including incomplete transition exhaustion.

The [portable fixture runner](../validation/memory/README.md) is under
`validation/memory/`; `python3 validation/memory/run.py audit` checks its inputs.
The gate takes explicit tool paths and a fresh output directory, with primary
groups `static,bridge,pairs,controls`. Its independent oracles
and actual exported pairs supplement the theorems. The 53-row reference bridge
observed 18 values, 8 traps, 7 resource limits and 20 rejections. There is no
universal production/native equivalence claim, no equal Core/MIR budget theorem,
and no proof of bytes-to-JSON parsing, Lean compilation/runtime or host I/O.
The hosted allocator is not an ANL OS memory manager. Heap-bearing `anl verify`
returns unsupported, rather than treating model memory safety as a heap contract.

The memory replay inventory has 75 entries: 72 ANL modules and three CLI roots.
The import-only umbrella is checked structurally and built; it is not passed as
a `leanchecker` namespace prefix, which would expand into concurrent replays.

## Unsigned words and cumulative execution

The [word specification](../spec/words.md) describes source arithmetic, conversions,
Core v4 and word MIR. The new `ANL.Word` primitive layer and `ANL.Words` cumulative
model keep all historical `APL.*` and `ANL.Memory` definitions unchanged. Words
compose with flat tuples, mutable state, calls/loops and scoped `i64` buffers.

Accepted proofs cover primitive result ranges and exact trap conditions,
independent raw checker equivalence, finite Core/MIR machine safety/correspondence,
resource preflight/prefix accounting and exact legacy execution embeddings.
Canonical lowering has finite completed correspondence in both directions under
the same response stream, with exact world and current/suspended capabilities.
Corresponding Core/MIR transition budgets are independently existential. No
termination, equal-budget exhaustion or production compiler/native theorem follows.
See the [word theorem inventory](PROOFS.md#unsigned-word-model).

The new strict reader/reference executable targets are `anl_words_raw_probe`, `anl_words_pair_checker`
and `anl_words_reference_runner`, built with Lake from `formal/`. The
[word protocol](../spec/words-evidence.md) records exact invocations, new schemas,
separate expression/fill and administrative budgets, and retained incomplete
prefixes. These tools use the new model; changing printed revision IDs alone
would not establish correspondence. Their byte/JSON/IO and compiled execution
boundaries remain explicit.

Word `verify` remains unsupported with exit 7 before external tools. Word-dependent
specifications are rejected; ordinary word-free clauses may still type-check
beside words and are erased on ordinary execution. Runtime safety is not a proof
of those clauses or of an ANL-authored OS.

## Boot Core static checking

The [boot profile](../spec/boot-profile.md) has a separate raw `ANL.Boot.Program`
and independent static judgment. Its checker validates fixed platform metadata,
roles, all ordinary bodies, effect permissions, the full acyclic call graph and
canonical primitive declarations. The [boot proof inventory](PROOFS.md#boot-static-model-and-core-reader)
also records designated-tail and ordinary-machine no-normal-return guarantees.
These results do not execute a device or establish a bootable image.

With the pinned Lean tools on `PATH`, build the static probe from `formal/`:

```sh
lake build anl_boot_raw_probe
```

From the repository root, export a checked boot source and check its Core
independently:

```sh
./target/release/anl dump-core examples/boot/park.anl > /tmp/anl-boot-core.json
formal/.lake/build/bin/anl_boot_raw_probe /tmp/anl-boot-core.json
```

The probe prints `{"raw_valid":true,"reason":""}` and exits 0. It accepts exactly
one file path. Invalid input exits 1, a reader resource limit exits 3, and an
argument or I/O failure exits 4. Rejections use `raw_valid:false` and a nonempty
reason; an output failure may leave an empty or partial report and never retries
with a second JSON document. Reason contents are bounded to 1,024 UTF-8 bytes
before JSON escaping. Rust `eval-core` remains a separate route: valid boot Core
returns unsupported status 7 rather than executing the program.

The probe enforces 1,048,576 original bytes, logical expression depth 128 and
JSON-container depth 1,024. Rust's separate JSON reader admits 127 containers;
these transport bounds differ. Successful Lean checking implies the independent
static judgment for the returned raw program. UTF-8/JSON parsing, I/O, compiled
probe execution and production source checking remain trust boundaries. There
is no boot pair checker, hardware interpreter or native boot backend in this slice.

The separate [conditional native call-frame algebra](PROOFS.md#conditional-native-call-frame-algebra)
proves finite-prefix frame separation, byte preservation, call-depth upper bounds,
aligned return and root-stack substitution from explicit local/leaf execution and
instruction-effect contracts. It does not discharge those contracts for emitted
RISC-V code or prove compiler, ELF, firmware or guest correspondence.

## Boot v2 Core static checking

`ANL.Boot.V2` adds a separate raw program and static checker for
`anl-boot-core-v2`, revision `anl-boot-rv64-virt-v2`, and target
`rv64-virt-sbi-v2`. The ordinary types and terms remain `anl-words-v1`.
The V1 model and `anl_boot_raw_probe` retain their existing envelope.
Neither reader converts between versions. V2 documents with only legacy
operations still require the V2 reader.

With the pinned Lean tools on `PATH`, build the separate probe from `formal/`:

```sh
lake build anl_boot_v2_raw_probe
```

From the repository root, pass an existing V2 Core artifact as the single path:

```sh
formal/.lake/build/bin/anl_boot_v2_raw_probe path/to/anl-boot-core-v2.json
```

Replace the example path with the artifact to check. Keep actual compiler
exports unchanged when comparing source checking with the independent probe.
Successful acceptance prints `{"raw_valid":true,"reason":""}` and exits 0.
Invalid input exits 1, a resource limit exits 3, and usage or IO failure exits 4.
The bounded report and failed-output behavior match the V1 static probe.

The V2 probe admits at most 128 declarations, 8,192 total raw body nodes,
64 parameters per defined function, and 64 arguments per ordinary call.
Every raw child counts, including dead code and forbidden memory forms.
These probe limits precede static policy and are separate from V2 semantic
well-formedness. The existing 1 MiB byte, 128 logical-depth, and 1,024 JSON-depth
limits also apply. A resource result does not establish a language error.

The checker validates every body, the exact setup prefix, roles, effects,
canonical primitive discovery, and the complete acyclic call graph. The new
`illegal_instruction` row has no runtime parameters, result `unit`, and
machine authority zero. Only the boot entry may call it after the setup prefix.
Its presence does not skip later typing or permit a handler or dead helper call.

The [static V2 proof scope](PROOFS.md#boot-v2-static-model-and-core-reader) covers
decoded acceptance and local fault-data predicates. The probe remains a static
checker; it does not run the runtime model below. JSON parsing, compiled IO,
source translation, boot MIR and origin correspondence, native behavior, and
the complete ANL-authored OS remain separate boundaries.

## Boot v2 local runtime model

The [runtime proofs](PROOFS.md#boot-v2-origins-transitions-and-local-coherence)
operate directly on the V2 program, its ordinary-machine state and source
origins. Independent `Ready`, `Execute`, `BootOutcome` and `BootStep` relations
agree with command selection and the total `tickRaw` function. A validated-input
wrapper exposes `tick`; neither function adds a boot execution route to the CLI.

Illegal-instruction capture, raising and externally supplied forwarding are
separate transitions. A matching legacy delivery has priority before fault
commit. A valid pending fault with no forwarding response is stable and blocked;
an invalid pending state is rejected. Forwarding starts the declared hardware
handler with fresh terminal-root continuations, saving the actual pending caller
snapshot instead of resuming it.

The local `Coherent` predicate covers active typing, origins, machine memory,
input cursor, ordinal, stack role, phase and the fields stored in an interrupted
snapshot. Well-formed V2 source and valid input are explicit premises of its
preservation theorem. Coherence does not imply that the next command is eligible:
an uninstalled fault may advance to commit and then report `invalidState`.
The finite `Reachable.coherent` corollary does not establish progress, forwarding
availability or a global event-history theorem.

These modules are included in the existing `formal/check.sh` inventory, complete
axiom audit and separate-module kernel replay. The separate
[transfer-cut proofs](PROOFS.md#conditional-native-call-frame-algebra) preserve a
supplied frame prefix through a linked or nonlinking transfer to a slot and bound
two independent terminal roots by their maximum. They assume the concrete-step
and root contracts; they do not prove Rust analysis, instruction decoding,
exception delivery or source-to-native correspondence.

## Boot v3 static handler model

The [v3 profile](../spec/boot-profile-v3.md) admits a hardware-handler prefix with
empty effects or UART authority and a designated terminal loop. The language
handler remains exactly its empty terminal loop. Ordinary types, including flat
tuples, retain their existing boot rules; memory and views remain unavailable.
Every definition and syntactic branch is checked, including unused helpers and
dead code. Ordinary role calls and recursive helper graphs remain forbidden.

The Lean interface is a library API. From `formal/`, `lake build ANL` builds the
model umbrella. In a Lean module, import the checked reader and its theorems:

```lean
import ANL.BootV3Wire

#check ANL.Boot.V3.checkProgram
#check ANL.Boot.V3.checkProgram_iff
#check ANL.Boot.V3.Wire.checkCoreDocument
#check ANL.Boot.V3.Wire.checkCoreDocument_iff
```

`ANL.Boot.V3.Program` reuses the V2 raw record type. The V3 checker and independent
`WellFormedProgram` predicate require the closed V3 metadata, the broader hardware
role policy and all unchanged typing, setup, authority, discovery and acyclicity
conditions. Reusing the record type does not make a V3 program V2-well-formed.
The checked reader reuses the raw decoder, then applies the V3 checker. It returns
`.ok p` exactly when that decoder returns `p` and the V3 predicate holds.

There is no separate V3 command-line probe or runtime runner. The V1/V2 probes
keep their existing revisions. The production Rust interfaces are
`boot::import_core_v3` and `boot::import_pair_v3`; their implementation is not
certified by the Lean reader theorem. All three existing native identity APIs
reject V3 with their typed revision-unsupported result, including programs with
no illegal operation.

The [proof inventory](PROOFS.md#boot-v3-static-handler-policy-and-reader) states
the exact static scope. These three modules add no V3 runtime transition,
local-coherence, completion or native-execution theorem. JSON parsing, IO,
source translation, canonical Core/MIR agreement and native/device behavior
remain separate boundaries.
