# Flat tuples

The `flat-products-2026-11-17` extension adds tuples to source checking,
interpretation, native compilation and strict core interchange. Tuples have
1 through 8 fields, each `i64`, `bool` or `unit`. They can be parameters, return
values, local bindings and branch results, including in recursive functions and
programs with mutable state and while loops. Executable entry remains
`fn main() -> i64` with no parameters.

The cumulative [unsigned-word revision](words.md) adds ordinary word values and
new schema IDs without widening this historical revision. Its
[word artifact protocols](words-evidence.md) apply to v4 programs; buffer cells,
resource permissions and evaluation order remain unchanged.

## Syntax and types

| Form | Meaning |
| --- | --- |
| `()` | The existing unit value; its type is `unit` |
| `(e)` | Grouping; the type and value of `e` |
| `(e,)` | A singleton tuple |
| `(a, b)` or `(a, b,)` | A two-field tuple |
| `(i64,)` or `(i64, bool, unit)` | Tuple types; a comma is required |
| `value.0` | Field zero of a tuple |

The ordered field types and arity define the tuple's shape. `(i64,)` is distinct
from `i64`, and unit is not a zero-field tuple. Nested tuples, records, arrays,
destructuring, and field assignment are unsupported. Tuple type fields must be
scalar; `(i64)` and `()` are not type aliases. Tuple values and types allow a
trailing comma; function parameter and argument lists retain their existing
rules and do not allow one.

Projection binds more tightly than unary operators and evaluates its base once.
Its index is a single source digit from `0` through `7`, strictly less than the
base tuple's arity. `.01`, negative or computed indices, out-of-bounds indices,
and projection from a scalar are static errors. Because tuple fields are scalar,
`pair.0.0` is invalid. Projection is not a place that can be assigned to.

`==` and `!=` accept two tuples of the same shape. Equality compares every scalar
field by value, including unit; inequality negates that result. Tuples have no
ordering, arithmetic, Boolean operations or truthiness conversions.

## Evaluation and value snapshots

Construction evaluates every field left to right, capturing each completed
scalar value before the next field begins. Projection evaluates the complete
base: `(7, 1 / 0).0` traps before returning anything. Both equality operands
finish in order before their fields are compared, even when the first fields
differ. Existing checked arithmetic, short circuit and trap order remain intact.

Reading or passing a tuple captures its value. Later replacement of the original
binding does not alter that snapshot. A mutable tuple can be replaced only by a
whole value of the same shape. For example, after `let saved = pair;` and
`pair = (2, true);`, `saved` retains the previous value. In
`f(pair, { pair = (2, true); pair })`, the first argument retains the old value and
the second receives the replacement. Callee-local mutation cannot change caller
bindings. No mutable payload, pointer identity or storage alias is exposed.

The [count-and-sum example](../examples/tuples/count-sum.anl) returns two results
from a loop. The [snapshot example](../examples/tuples/snapshots.anl) exercises
ordered argument capture, a saved value and whole-tuple replacement:

```sh
./target/release/anl eval examples/tuples/count-sum.anl
./target/release/anl run examples/tuples/snapshots.anl
```

These print `55` and `42`, respectively. Native lowering uses ordinary C structs
with deterministic shape declarations, initialized fields and ordered
temporaries. Tuple copies and comparisons do not rely on padding or `memcmp`.
Generated tuple operations introduce no heap allocation or stable foreign ABI.

## Version selection and core JSON

A structural scan covers all loaded function signatures, expression types and
children, and retained binding metadata. A tuple anywhere selects
`apl-core-v2` or `apl-expr-v2` with semantic revision
`flat-products-2026-11-17`, even in an unused function, dead branch or skipped
argument. Otherwise state selects the existing v1 revision; otherwise export
retains v0. The [v0](core-format.md) and [v1](control-flow.md#typed-core-and-interchange)
formats and scalar outcomes remain unchanged and reject tuple types and tags.

V2 admits all existing local-state constructors. Program artifacts keep the
complete function table, declaration-order parameters, de Bruijn locals and
nullary scalar entry. Expression artifacts remain closed and call-free.
A scalar-only document explicitly labeled v2 is accepted, then classified by
its contents as immutable scalar or local state. Rust retains the old scalar
evaluation resource behavior; the v2 label alone does not activate tuple resource
counters. Separately, source/program export selects the lowest applicable program
schema. This program exporter does not provide a general expression-document
reexport API.

A type is a scalar string or exactly `{"tuple":["i64","bool","unit"]}`.
The tuple array has 1 through 8 scalar strings; nested type objects are invalid.
The additional expression forms contain exactly these members:

| `tag` | Other members |
| --- | --- |
| `tuple` | `fields`: ordered array of expressions; `ty`: matching tuple type |
| `project` | `value`: base expression; `index`: integer token 0 through 7; `ty`: inferred scalar field type |

The importer independently infers shape and projection bounds, checks every
function signature and body, and rejects forged types. Projection indices reject
negative numbers, `-0`, fractions, exponents, strings and booleans. Duplicate or
unknown object fields, nested/overwide tuples, and mismatched fields are invalid
IR. The original scalar integer-string rules still apply.

Run the [tuple expression fixture](fixtures/tuple-expression.json) with
`./target/release/anl eval-core spec/fixtures/tuple-expression.json`. Its outcome is:

```json
{"outcome":"value","type":{"tuple":["i64","bool","unit"]},"value":["42",true,null]}
```

The value array has the same length and ordered scalar representations as the
type array: canonical decimal strings for `i64`, JSON booleans for `bool`, and
`null` for unit. Existing scalar, trap, resource-limit and invalid-IR outcome
shapes and exits are unchanged. Human tuple display is not an interchange format.

## Checked resource limits

Existing input, graph, parser-depth, evaluation-depth and fuel limits still
apply. Tuple construction costs one expression fuel unit plus its fields;
projection costs one plus its base. The following additional evaluation limits
apply when the checked program structurally contains tuples:

| Resource | Limit | Charging boundary |
| --- | ---: | --- |
| Cumulative tuple allocation work | 1,048,576 scalar fields | Evaluate into bounded scratch storage, then checked-add arity before allocating the immutable payload. Copies and projections do not recharge; destruction does not refund. A trapped field constructs no tuple. |
| Logical active slots | 65,536 | Count retained caller environments and all live argument-buffer reservations, including partially filled outer buffers. Reserve all arguments before allocating their vector; transferring it into a callee does not charge twice. A let reserves before growth. Scope/call returns release their counts. |
| Exported v2 JSON | 1,048,576 UTF-8 bytes | Bound production of the exact compact document, excluding the CLI's final newline. |
| Emitted v2 C | 67,108,864 UTF-8 bytes | Bound the complete translation unit, including declarations, signatures and intermediate formatting. |

All counter arithmetic is checked. Allocation work charges actual tuple arity,
not spare capacity in its backing storage. Tuple width is checked before growing
an oversized field collection. Each binding or reserved argument counts as one
logical slot, including unit and tuple values. Slots are not vector capacity or heap bytes;
scratch values are bounded separately by width 8 and evaluation depth 256.
An unrecoverable evaluation error drops its buffers and ends evaluation.

Limit exhaustion is `resource_limit`, exit 3, rather than an arithmetic trap,
invalid source, infrastructure failure or evidence of divergence. Output-budget
failure publishes no partial stdout or artifact, preserves an existing build
destination and does not launch the C compiler. Native execution does not inherit
the interpreter's fuel, slot or tuple-allocation budgets. Host stack, allocator
and compiler resources remain external limits; these checks make no hard heap or
RSS guarantee.

## Verification boundary

Flat tuples are supported by `anl verify` throughout the acyclic fragment with
annotated while loops. Every loaded function is checked, including unused
functions. Missing invariants and recursive call graphs reject the attempt
before tool discovery. Ordinary checking, interpretation and native compilation
type-check and erase clauses without proving or dynamically enforcing them.

Specifications use flat tuples of 1 through 8 mathematical integer, Boolean or
unit fields. Construction, references, constant projection and same-shape
equality or inequality are permitted. Every `requires`, `ensures` and `invariant`
clause still has Boolean type. Calls, blocks, local declarations, assignments,
`if`, nested tuples, tuple arithmetic and tuple ordering are excluded from clauses.

Every constructed field must be defined before the tuple is available. Projection
retains definedness of the entire base. Thus `(7, 1 / 0).0 == 7` is undefined.
Equality and inequality require both complete operands to be defined, even when
the first fields differ. `(0, 1 / 0) != (1, 2)` is also undefined. Boolean short
circuit may guard the entire tuple operation, as in
`divisor == 0 || (7, 1 / divisor).0 == 7`.

Specification integer fields and arithmetic intermediates are unbounded.
Executable integer parameters and fields remain i64 values. The verifier checks
each executed arithmetic intermediate and bounds each integer parameter or
arbitrary loop-head field individually. Existing truncation-toward-zero division
and remainder rules are unchanged.

Symbolic evaluation retains the runtime order above. Construction captures each
completed field. A call captures each complete argument before evaluating the
next argument. Assignment evaluates the entire right-hand side before replacing
the binding. Postconditions use the original entry parameters. Conditional flows
merge matching shapes field by field and retain only the selected branch's
runtime obligations under its guard.

Every visible mutable non-unit field gets a distinct arbitrary loop-head symbol,
including fields the loop never writes. Unit fields remain unit. Immutable
bindings retain their captured values. Invariants establish relations between
these fields before each condition evaluation. Effects of the final false
condition reach the continuation. Verification checks partial correctness and
finite-execution safety under the stated assumptions; it does not prove termination.

The [snapshot contract](../examples/contracts/tuple-snapshots.anl) and
[count-and-sum contract](../examples/contracts/count-sum.anl) are complete examples.
The [verification guide](../docs/verification.md#verify-tuple-contracts) gives their commands.

### Tuple verification reports

The product route is selected by any tuple in loaded signatures, executable
terms, retained binding types, contracts or invariants. This scan is distinct
from executable revision selection. A tuple used only in a clause selects the
product report while `semantic_revision` remains `m1-2026-11-16` or
`local-state-2026-11-17`, as appropriate for the erased executable program.
Source errors retain the existing v0 error envelope with null semantic revision.

| Field | Value |
| --- | --- |
| `schema` | `anl-verify-v3` |
| `verification_revision` | `anl-flat-products-verify-v1` |
| `scope.functions` | `all_loaded` |
| `scope.fragment` | `invariant_flat_products_acyclic` |
| `scope.model_proof` | `APL.ProductFlow.contract_queries_sound` |
| `trust` | `smt-trusted` |
| `type_checked`, `contracts_erased` | `true`, `true` |
| `tested`, `dynamic_checks` | `false`, `false` |
| `scope.termination_proved`, `scope.native_correctness` | `false`, `false` |

The route retains the source, compiler, solver, exact query and hash fields of
the [invariant-loop report](loop-verification.md#invariant-loop-report-contract).
It also retains source-loop metadata, expansion and loop-occurrence records,
guarded-check provenance and all outcome distinctions. A product-bearing graph
uses this route even if it contains no loop. Function and binding types use
scalar strings or the structured `{"tuple":["i64","bool","unit"]}` representation.
Existing scalar report schemas, revisions and query behavior remain unchanged.

Parameter identities follow source parameter order, then field order. Each scalar
reserves one logical slot and each tuple reserves its arity. Unit reserves a slot
without creating an SMT variable. Once a function's parameter layout is built,
its record exposes `parameter_leaf_slots` and `initial_logical_bound`, both equal
to the reserved slot count, plus `head_display_start`. Layout metadata records
`order: "source_parameter_then_field"` and
`unit_slots: "reserved_without_smt_variable"`.

Non-unit scalar parameters use `pN`; tuple fields use `pN_fK`, where `N` is the
source parameter index and `K` is the field index. Each model symbol records a
scalar `type` and an `origin` containing `kind: "parameter"`, `index`,
`logical_id` and, for tuple fields, `field_index`. Every non-unit entry field is
requested, including unused fields. Unit fields produce no model entry.

Loop-head symbols use `hN`. Their origin retains the source function, binding,
loop node, expansion and occurrence, with `field_index` for tuple fields and
`logical_id`. For each verified function the identity is
`initial_logical_bound + N - head_display_start`. Only allocated non-unit head
symbols count toward the 4096-symbol limit. Source binding count, reserved
parameter slots and allocated head symbols are distinct quantities.

Models must contain exactly the requested scalar symbols. Missing, duplicate,
extra or incorrectly typed fields are protocol errors. Integer entry fields must
be within i64 range. Head integers use mathematical decimal strings and retain
`within_machine_range`; an inactive guarded head may lie outside the machine
range. Models remain abstract assignments with `replayed: false`, not concrete
execution traces. A head-state refutation can identify an invariant that is too weak.

### Verification limits and trust

Product verification retains the existing attempt-wide ceilings of 1000000
symbolic work units, 100000 arena nodes, 4096 non-unit head symbols, 100000
expression visits, depth 256, 1024 queries, 1048576 bytes per query and 16777216
total query bytes. Solver output and timeout bounds are unchanged. Field
traversal, capture, copy, merge, instantiation and metadata work are charged
before growth. Each `Arena::render` output byte also costs one work unit before
emission, including declarations, definitions and query-body framing. Existing
parameter-declaration charges remain. Work can therefore run out before the
independent symbol, query or byte caps. A limit returns `unknown`; completed
query evidence remains, and no unfinished query is reported as a completed obligation.

The `resources` record retains the work, arena-node and head-symbol counts,
expansions, loop occurrences and pending queries accumulated during generation.
These counters and the recorded limits do not establish a performance guarantee.

Successful verification remains `smt-trusted`. It establishes the requested
arithmetic-safety and partial-correctness obligations under the recorded encoding
and solver assumptions. Source annotation reconstruction, Rust generation, SMT
rendering and solver answers, native execution, termination and completeness at
production limits remain separate trust or proof obligations. The
[formal inventory](../formal/PROOFS.md#merged-flat-tuple-contract-verification)
states model coverage independently. `scope.model_proof` names the model theorem,
which requires successful generation, a typed annotated table, typed inputs
satisfying requires and semantic acceptance of every generated query. It does
not certify the report, Rust generator or solver reply. The report retains
`scope.proof_gaps` for the remaining implementation and completeness boundaries.

## Formal runtime and comparison boundary

The separate [flat-tuple runtime model](../formal/PROOFS.md#flat-scalar-products-with-local-state)
covers construction, projection, equality, mutable locals, loops and recursive
calls. Independent inference and declarative typing agree. Under a well-typed
function table and typed starting state, finite traces preserve typing and cannot
reach invalid; defined arithmetic traps remain possible. Completed runs and finite
stopped traces correspond with sufficient model budgets, and finite LocalState
outcomes embed forward. These are runtime-model guarantees, not tuple contract
verification or termination proofs.

The separate [v2 adapter](../formal/README.md#v2-interchange-adapter) independently
validates artifacts before executing `FlatProducts.run`. Scalar-only v2 inputs
receive their structural semantic classification, but this Lean executable always
uses the flat-products transition machine. Its fuel is not Rust expression fuel,
and it does not model Rust allocation/slot/output limits. Executable comparisons
check finite values, traps and malformed artifacts; resource-limit cases are
inconclusive. The actual Lean reader has a proved acceptance boundary: successful
`document` or `decode` returns a closed typed expression or a well-typed complete
function table with a nullary i64 entry. At every fuel budget, `execute` excludes
invalid outcomes and preserves returned types. Defined traps and resource limits
remain possible. Source lowering, JSON-text interpretation, Rust evaluation and
storage reclamation, compiled Lean execution and native code remain separate
trust or correspondence boundaries. Scalar verification-condition proofs do not extend
to tuples by inheritance.
