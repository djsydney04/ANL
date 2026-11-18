# Memory MIR and canonical pair checking

`anl-memory-mir-v1` is a developer interchange for the structured memory IR.
It uses semantic revision `anl-owned-buffers-v1` and the same admissible
[allocation profile](owned-buffers.md#target-profile-and-native-abi) as v3 Core.
It is not an installed `anl` subcommand or a general optimization certificate.

The cumulative [unsigned-word revision](words.md) adds ordinary word values and
new schema IDs without widening this historical revision. Its
[word artifact protocols](words-evidence.md) apply to v4 programs; buffer cells,
resource permissions and evaluation order remain unchanged.

## Raw documents

The root has exactly `schema`, `semantic_revision`, `allocation_profile`,
`functions`, `entry`. A function has `id`, `view`, `params`, `result`, `body`,
`temp_count`, `slot_count`, `resource_count`. IDs equal table positions. A view
is null or `{mode,resource}`. Ordinary parameters are Temps; Temp and Slot each
have `{id,ty}`. Block has `{instructions,yield}`; an instruction has
`{destination,operation}`. Types remain scalars and flat scalar tuples.

An operation is a tagged object with exactly its payload fields:

| Tag | Payload |
| --- | --- |
| integer / boolean / unit | value / value / no fields |
| tuple | fields |
| project | value, index |
| unary | op, operand |
| binary | op, left, right |
| call | function, arguments |
| mutable_scope | slot, initial, body |
| load / store | slot / slot, value |
| while | condition, body |
| branch | condition, then, else |
| heap_scope | site, owner, length, initial, success, failure |
| buffer_length | resource |
| buffer_read | resource, index |
| buffer_write | resource, index, value |
| call_view | function, resource, mode, arguments |

Ordinary operands are typed Temps, slot operands are typed Slots, and resource
operands are static IDs. Mutable-scope body, while condition/body and branch
alternatives are Blocks. Heap length is a Temp, while initializer, success and
failure remain Blocks. A write's value is an RHS Block. This preserves the
negative-length and index guards before those computations. View-call ordinary
arguments are already captured Temps; the operation grants the loan afterward.
Logical short circuit lowers to branch, not eager binary `and` or `or`.

Validate all functions, all nested blocks and dense declared ID tables. Temp,
Slot and resource binders are unique within a function; uses must be visible and
well typed. Calls match complete signatures, body yields match results, and the
entry has no view/arguments and returns i64. A heap owner is visible only in its
success block. No resource Temp, resource Slot, pointer operation, arbitrary free,
or resource-valued yield exists. A static binder can execute repeatedly and is
not an allocation identity.

## Canonical lowering

Parameters receive the first Temps. Lower operands left to right; allocate an
instruction destination after lowering its nested computations. Immutable local
aliases retain their Temp. Mutable scope assigns a Slot after the initializer;
reads emit loads. Branch lowers then before else; while lowers condition before
body. Short circuit lowers its right block once and uses the captured left Temp
for the short branch. Counts include unexecuted syntactic blocks.

An incoming view uses resource ID zero. Heap site `h` uses resource ID
`h + (view present ? 1 : 0)`. Lower its length, initializer, success and failure
in that syntactic order; runtime execution still follows the guarded language
order. Writes lower index then RHS block. View calls lower ordinary arguments
before their operation. The executing function ID supplies the function component
of trace sites; it is captured before evaluating heap children.

`ANL.Memory.Pair.check` validates both decoded artifacts, requires matching
revision/profile/function-entry structure, and compares the MIR with this exact
canonical lowering. Alpha-renaming, alternative optimizations, claimed annotations
and supplied certificates cannot bypass comparison. Independent MIR typing alone
does not imply this canonical relation.

The accepted finite simulation relates checked Core and canonical MIR under the
same allocator response stream. It preserves completed values/traps, the complete
mathematical World and current/suspended runtime capabilities in both directions,
excludes invalid canonical MIR prefixes, and preserves normal entry cleanup.
Runner budgets are independently existential. Equal steps, fuel, resource cutoffs,
exhausted states, general termination, Rust lowering, C/native correctness and
SMT heap contracts are outside that theorem. Pair/Wire acceptance supplies the
premise for these semantic corollaries; bytes-to-JSON interpretation and compiled
checker execution remain explicit boundaries.

## Independent pair checking

The formal reader bounds Core at 1048576 bytes, MIR at 8388608 bytes, logical Core
expression and MIR block depth at 128, and JSON containers separately at 1024.
A flat MIR instruction does not spend another block-depth unit. Strict decoding
rejects duplicate/missing/extra fields and requires canonical unsigned JSON
integers fitting uint64 for IDs. Integer literals use canonical i64 decimal
strings; Boolean literals use JSON Booleans and unit has no payload.

From `formal/`, build `anl_memory_pair_checker` with Lake. Its executable accepts
exactly two paths:

```text
formal/.lake/build/bin/anl_memory_pair_checker CORE.json MIR.json
```

It writes one JSON object with `schema`, `status`, `semantic_revision`,
`allocation_profile`, `reason`. Schema is `anl-memory-pair-check-v1`; revision
is `anl-owned-buffers-v1`. Accepted exits 0 with the exact common profile and an
empty reason. Rejected exits 1, reader resource limit exits 3, and invocation/I/O
error exits 4; all three have null profile and a UTF-8 reason bounded to 1024
bytes. A rejected pair report does not establish that either artifact was typed
individually. Missing/killed/invalid reports are incomplete infrastructure
evidence. See [export and execution protocols](memory-evidence.md).
