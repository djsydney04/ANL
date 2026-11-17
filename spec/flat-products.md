# Flat tuples

The `flat-products-2026-11-17` extension adds tuples to source checking,
interpretation, native compilation and strict core interchange. Tuples have
1 through 8 fields, each `i64`, `bool` or `unit`. They can be parameters, return
values, local bindings and branch results, including in recursive functions and
programs with mutable state and while loops. Executable entry remains
`fn main() -> i64` with no parameters.

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

The [count-and-sum example](../examples/tuples/count-sum.apl) returns two results
from a loop. The [snapshot example](../examples/tuples/snapshots.apl) exercises
ordered argument capture, a saved value and whole-tuple replacement:

```sh
./target/release/apl eval examples/tuples/count-sum.apl
./target/release/apl run examples/tuples/snapshots.apl
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
`./target/release/apl eval-core spec/fixtures/tuple-expression.json`. Its outcome is:

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

Specifications remain scalar mathematical expressions. Constant clauses and
clauses naming only scalar parameters or locals can accompany tuple-bearing
functions. A tuple reference is rejected at that reference; tuple construction
and projection are invalid inside clauses. Tuple bindings retain their positions
in source contexts, so later scalar names do not change meaning.

After source checking, any structural tuple use rejects the entire verification
attempt before scalar formula conversion, route analysis or tool discovery.
This rejection takes precedence over recursion and missing loop invariants.
`apl verify ... --json` returns exit 7 and these fixed fields:

| Field | Value |
| --- | --- |
| `schema` | `apl-verify-v2` |
| `semantic_revision` | `flat-products-2026-11-17` |
| `verification_revision` | `apl-flat-products-unsupported-v1` |
| `status`, `trust` | `unsupported`, `not_established` |
| `compiler`, `solver` | `null`, `null` |
| `obligations` | `[]` |
| `type_checked`, `contracts_erased` | `true`, `true` |
| `tested`, `dynamic_checks` | `false`, `false` |

`scope.functions` is `all_loaded`; `scope.fragment` is
`unsupported_flat_products`. Arithmetic safety, partial correctness, termination
and native-correctness flags (`arithmetic_safety`, `partial_correctness`,
`termination_proved`, `native_correctness`) are all `false`, and
`scope.model_proof` is `null`.
The remaining top-level members are `sources`, `functions` and `message`.
Each source records `id`, `path`, `path_bytes_hex`, `sha256` and `bytes`.
Each function records `id`, `name`, `parameter_types`, `result` and `location`;
types use the scalar-string/tuple-object representation above. Locations retain
source IDs, byte spans, path bytes and line/column positions. `message` is
`flat products are unsupported by the scalar verifier; no safety or partial-correctness claim was established`.
There are no scalar analysis limits, expanded-node counters or loop metadata.
Source/type errors still occur before this report can be formed.

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
inconclusive. Source lowering, JSON decoding, Rust evaluation and storage
reclamation, compiled Lean execution and native code remain separate trust or
correspondence boundaries. Scalar verification-condition proofs do not extend
to tuples by inheritance.
