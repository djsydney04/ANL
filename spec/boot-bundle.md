# Boot MIR and source bundles

`anl emit-boot FILE --out DIRECTORY` checks an ANL boot program and publishes
six generated files for `rv64-virt-sbi-v1`. It does not compile, link or execute
them. The [source and Core profile](boot-profile.md) remains the admission boundary.
Source policy, including UART initialization, polling and terminal loops, stays
in ANL. No handwritten C/Rust OS subsystem is linked or copied into the bundle.

The [v2 extension](boot-profile-v2.md) retains these six payloads and publication
rules, with separate schema identifiers and an assembly primitive for an explicit
illegal instruction. The v1 identifiers and native setup API below remain closed.

## Checked canonical pairs

The Rust library's `anl::boot::lower` consumes a `CheckedProgram` and returns an
opaque `CheckedPair`. `import_pair(core_text, mir_text)` independently checks the
Core document and raw MIR, then requires the entire decoded MIR, including counts,
to equal canonical lowering of that Core. A structurally typed alternative MIR
is insufficient. `export_pair_core` and `export_mir` export the paired documents;
`emit(&pair)` returns an immutable `Bundle` with `files()` and `publish(path)`.
There is no hosted-program conversion or standalone boot MIR permit.

`Bundle::setup_identity()` returns a borrowed, read-only view for a narrow v1 setup
profile: exactly the three declared roles, the three mandatory machine setup
primitives and no generated scalar helpers. It retains the actual declaration
IDs, signatures, effects, generated symbols and byte ranges alongside the six
exact bundle payloads. Each role is identified by its declared entry, including
when function declarations are reordered. The view and its rows cannot be
constructed or modified through the public API.

An additional function, scalar helper or other primitive makes this projection
unsupported; ordinary bundle emission still succeeds. The projection adds no
serialized fields and changes no generated payloads. Its native return labels
describe the emitted interfaces; they are not proofs of return behavior, stack
adequacy, primitive authority or native correctness.

For v2, `Bundle::illegal_slot_identity()` returns a separate borrowed
`IllegalSlotEmissionView` when the checked program declares the illegal-instruction
primitive. A v2 bundle without it returns `None`; v1 returns a typed revision
error. The view retains the actual primitive ID, signature, effect, generated
symbol, six payloads and textual assembly range. It cannot be publicly constructed
or mutated. The textual range does not denote a linked PC or instruction length.

`Bundle::exception_setup_identity()` provides a separate v2 view only for the
three declared roles, three mandatory setup primitives and one illegal primitive,
with no additional functions or generated scalar helpers. Ineligible projections
return typed errors without preventing ordinary bundle emission. The old
`setup_identity()` remains v1-only, including for v2 bundles without the illegal
primitive. These views add no serialized fields and change none of the six
payloads.

MIR has schema `anl-boot-mir-v1`, semantic revision `anl-boot-rv64-virt-v1` and
ordinary revision `anl-words-v1`. Its root fields are exactly:

```text
schema, semantic_revision, ordinary_semantic_revision, target_profile,
image, stacks, devices, entries, functions
```

All platform metadata and primitive rows equal the checked Core metadata.
Defined rows have exactly:

```text
kind:"defined", id, name, view:null, params, result, effects, body,
temp_count, slot_count, resource_count:0
```

Parameters, blocks, typed temporaries, initialized slots and operations use the
existing [word MIR encoding](words.md#core-v4-and-word-mir). Primitive rows remain
bodyless, and calls use their declared signatures. The strict reader rejects
duplicate decoded keys, unknown fields, noncanonical numeric tokens, invalid
indices and annotations, and inconsistent counts. Its input limit is 8,388,608
bytes; Rust's 127-container transport bound also applies.

`CheckedPair::origins()` exposes derived source occurrences for emitted MIR
instructions. A Core path identifies constructor children, not an expression's
text or equality class. A MIR path contains ordered `blocks` entries of
`{instruction, child}`, followed by a final `instruction` index. Block selectors
are `mutableBody`, `whileCondition`, `whileBody`, `branchThen` and `branchElse`.
`parks()` returns the boot, hardware and language selected occurrences in that
order. The mapper records actual lowering decisions and resolves each selected
Core tail to its canonical MIR instruction. These are static locations, not
evidence that execution reaches them or that Core and MIR execution correspond.

A serialized Core edge has an `edge` tag: `letValue`, `letBody`,
`whileCondition`, `whileBody`, `ifCondition`, `ifThen`, `ifElse`, `unaryOperand`,
`binaryLeft`, `binaryRight`, `convertOperand`, `projectOperand`, or `assignValue`.
`callArgument` and `tupleField` additionally carry a zero-based `index`.
Paths are relative to the named defined function's body.

## Files and manifest

Every file is UTF-8 with a final LF. Limits include that LF:

| File | Maximum bytes | Contents |
| --- | ---: | --- |
| `core.json` | 1,048,576 | Checked boot Core |
| `mir.json` | 8,388,608 | Exact canonical boot MIR |
| `program.c` | 67,108,864 | Defined functions, used checked scalar helpers and primitive lowerings |
| `entry.S` | 1,048,576 | Boot and terminal-handler ABI adaptation |
| `link.ld` | 65,536 | Fixed image and stack layout with rejection assertions |
| `manifest.json` | 1,048,576 | Input identity, payload identities and source/code locations |

The manifest has exactly these root fields:

```text
schema:"anl-boot-bundle-v1", semantic_revision:"anl-boot-rv64-virt-v1",
ordinary_semantic_revision:"anl-words-v1", target:"rv64-virt-sbi-v1",
input, artifacts, functions, primitives, origins, parks, abi
```

`input` records `kind`, `bytes` and `sha256`. Source emission uses the exact bytes
retained during checking; it does not reopen the source path. Library emission
from imported Core uses `kind:"canonical_core"` and the emitted canonical Core
bytes. It does not claim the original JSON spelling is preserved.

`artifacts` has keys `core`, `mir`, `c`, `assembly`, `linker`, each containing
`path`, `bytes`, `sha256` for its complete payload. The manifest has no self-hash.
Compiler/tool provenance is external to this deterministic source bundle.

`functions` maps each defined `id`, `name`, and generated `symbol` to `source_span`
and `c_range`. `primitives` records `id`, `operation`, `symbol`, `artifact:"c"`
and `range`. `origins` records `function`, `core_path`, `mir_path`, `source_span`
and `c_range` for every emitted MIR instruction in structural order. Source
spans are null for imported Core. All ranges use inclusive `start`, exclusive
`end` UTF-8 byte offsets; structured parent C ranges may contain child ranges.
For each selected park, the constant condition and empty Unit body map to the
actual inline C fragments `true` and `(void)0;`. These two instructions retain
their original Core/MIR origins without separate C temporary declarations.
Other instructions keep their ordinary emission.

`parks` and `abi` each have `boot`, `hardware`, and `language` keys. A park records
`function`, `core_path`, `mir_path` for the initializer-first selected terminal
occurrence. An ABI row records `function`, `stack`, `symbol`, and `range` into
`entry.S`. It identifies the actual declared role; no first-equal-loop search or
synthetic function substitutes for that role.

## Generated instructions and safety boundaries

The translation unit requires little-endian RV64/LP64, fixed-width integers and
64-bit `uintmax_t`. Ordinary functions and primitives use `anl_boot_f<ID>` symbols.
The three role bodies have external `_Noreturn void` interfaces and retain their
ANL terminal loops. Checked arithmetic uses the established scalar helper guards;
failures call the generated language-entry ABI with tags 1 for overflow, 2 for
division by zero, or 3 for invalid shift. There is no hosted `main`, allocator,
stdio wrapper, exit handler or generated substitute park loop.

Each primitive invocation lowers to the following volatile assembly template
with a compiler memory clobber. The source determines invocation order and operands.

| Primitive | Generated operation |
| --- | --- |
| UART read8 at offset 5 | One `lbu` from `0x10000005`, returned as `u8` |
| UART write8 at offset 0–4 | One `sb` of the evaluated byte to `0x10000000 + offset` |
| I/O fence | One `fence iorw, iorw` |
| Clear `sstatus` mask 2 | One `csrci sstatus, 2` |
| Write `sie` value 0 | One `csrw sie, zero` |
| Install declared hardware handler | One `csrw stvec, REG`, with the generated hardware-entry address |

These templates rely on the declared privilege, accessible device mapping,
instruction set, compiler constraints and firmware handoff. A memory clobber
constrains compiler ordering; it does not supply extra CPU fences, atomicity,
UART polling or synchronization. Such operations must be authored explicitly.

Assembly uses `.option norelax`, `.option norvc` and four-byte-aligned entry
symbols. Boot establishes the declared boot stack and tail-transfers the incoming
hart/DTB arguments to ANL. Hardware entry captures `scause`, `sepc` and `stval`
before establishing the terminal stack and entering the ANL handler. Language
entry narrows its supplied tag to `u8` and enters the ANL language handler on that
stack. These entries do not use inherited `sp`, `gp` or `tp`, restore an
interrupted frame, return from a trap, or implement a scheduler.

The linker description starts at `0x80200000`, retains boot entry first and
reserves the declared 16,384-byte boot and 4,096-byte terminal stacks with
16-byte alignment. Explicit program headers separate executable text, optional
read-only data and writable stack reservations at page boundaries, and declare
a non-executable stack. Nonallocated debug information and stack-size records
are retained for later inspection. Assertions constrain layout to the one-MiB
image range and reject known writable-data, BSS, TLS, dynamic-linking and
initialization sections.

The internal bounded ELF reader checks raw structural ranges, symbol extents,
relocation descriptors and selected image-layout predicates. A separate internal
text checker reconstructs complete executable contributions from the two objects
using `CALL_PLT`, `PCREL_HI20` and ADDI `PCREL_LO12_I`, then compares every byte
with the linked image, including unrelocated bytes. Unsupported symbol-placement,
binding, padding and relocation forms fail closed. Neither checker is connected
to the build command or admits an executable. Native semantic correspondence, general
helper/primitive authority, complete ISA/ABI conformance, general stack adequacy
and exact DWARF/source-loop correspondence remain open. Text reconstruction does not
establish native correctness.

A standalone instruction-inspection library consumes the text reconstruction and
decodes the closed RV64IM+Zicsr profile into instruction descriptors and known
control-flow edges. It rejects forbidden encodings and register uses, and known
control entries that bypass the first instruction of a relocated call pair.
Return-shaped jumps, possible call continuations and eligible memory/CSR/fence
sites retain explicit obligations for later analysis. This inspection does not
establish returns, frames, hardware authority, exact selected-loop identity or
native correctness, and remains unconnected to the build command. The instruction
inspector is a separately linked Rust library, outside the compiler's ordinary
module tree. It links the `anl` library for the opaque emitted identity; Cargo's
ordinary compiler targets do not compile this standalone assembly.

`inspect_machine_with_illegal(TextInspection, IllegalSlotEmissionView)` uses the
same instruction/edge engine with a checked v2 context. It binds the generated
symbol to one globally named, four-byte-aligned, four-byte zero contribution in
the assembly object and linked image, without a relocation patch. Duplicate
canonical names, contradictory bytes and known interior targets are rejected;
unimplemented legal alias or localization forms remain unsupported. Existing
text reconstruction, resource bounds and all other instruction checks still apply.

The bound row has `InstructionKind::IntentionalIllegalSlot`, and `ordinary()`
returns `None`. It has no ordinary return, outgoing edge, call-pair membership or
memory/CSR/fence effect. Incoming calls retain their possible continuation
metadata; that metadata does not establish return from the slot. Context-free
`inspect_machine` and raw decoding still reject zero. The four-byte owned slot
is distinct from instruction length: its first zero halfword is already illegal.

This contextual inventory does not establish source-to-native correspondence,
exception delivery or firmware forwarding. Both `inspect_local_frames` and
`inspect_setup_stacks` return a located `Unsupported` error when given this
contextual machine. They do not produce v2 frame or stack bounds.

A third standalone library's `inspect_local_frames` entry point computes
conditional local-frame facts from the same instruction inventory. It tracks entry-relative stack offsets, register values
and saved frame slots, including the effects of loads whose result is discarded.
Joins lose facts conservatively; a final walk from each function entry removes
observations reachable only through an earlier, stronger state. Calls, stack
changes outside the local domain, CSR/fence operations and unresolved memory
accesses remain explicit boundaries. No state is propagated through a call or its
possible continuation.

A local return summary requires restored entry SP/RA and preserved registers on
every covered return, with no unresolved local boundary. It is conditional on
aligned entry SP/RA, valid nonwrapping frame storage and successful ordinary
instruction completion. Local loops without return sites do not establish
termination or selected-park identity. This local entry point does not establish
call-stack bounds, emitted role/helper identity, reset roots or native correctness.

The separate `inspect_setup_stacks(&Bundle, MachineInspection)` entry point accepts
only the emitted v1 setup profile: three role bodies and the mandatory setup
primitives, without additional functions or scalar helpers. It consumes the
opaque `Bundle` identity, checks complete typed privileged sites and stack-reset
entries, and constructs private summaries for returning setup leaves. The same
frame engine then resumes checked calls at their actual PC+4 continuation,
preserving caller frame bytes and forgetting caller-saved register facts. Peak
stack use is the maximum caller depth plus callee depth, not a sum of sequential
calls. Hardware and language entries start independent terminal-stack episodes
without assumptions about inherited SP or RA; their shared reservation uses the
larger bound.

A conditional setup bound requires complete final rooted coverage and fit within
the actual ELF stack reservations. A frontier leaves the bound absent; a known
retained overrun is rejected even if a later frontier prevents completeness.
These results assume valid nonwrapping storage and normal instruction completion.
Refinement between the concrete Rust analysis, instruction descriptors, native
execution and ANL source remains open, as do stack-metadata agreement and exact
selected-loop/DWARF correspondence. The result's flags for native admission, formal native correspondence, source
correspondence and stack metadata agreement remain false.

The `inspect_exception_setup_stacks(&Bundle, TextInspection)` entry point adds
conditional v2 frame analysis for the closed exception setup profile: three
roles, three returning setup primitives and one intentional illegal slot, with
no additional definitions or scalar helpers. It obtains both typed views from
the same held bundle and runs contextual machine inspection internally. The producer chain from the
six emitted payloads to the supplied objects and image remains a separate
premise; matching opaque role and symbol identities does not establish it. Once
contribution identities are uniquely bound, it checks privileged instructions
and transfer authority across owned bodies, including unreachable code, before
local alias or shape coverage checks. Earlier text/machine errors and ambiguous
identity failures retain their own stage and classification.

A supported boot transfer to the illegal slot becomes an
`ArchitecturalException` frontier at the caller. The slot receives no ordinary
entry state, return summary or continuation traversal. Linking transfers record
the transfer instruction's PC+4 in RA; nonlinking transfers retain the current
RA, including a value changed by a preceding AUIPC. This describes the transfer
cut before architectural trap entry. It does not establish exception delivery
or the hardware state after a trap.

Fault rows and stack bounds use only the final rooted states after joins have
stabilized. A conditional boot-prefix bound requires at least one retained
fault cut and complete supported coverage of the other rooted obligations. It
is the maximum local or caller-plus-leaf depth across that root, including
ordinary loops; it does not prove that a cut is dynamically reached or that a
loop terminates. Unknown stack facts can leave a descriptive cut without a
numeric bound. Known retained capacity violations are rejected even when an
unresolved frontier prevents completeness. Unreachable instructions after a
cut contribute to the machine inventory but not to rooted stack facts.

Hardware and language roots receive independent terminal-stack bounds; their
shared requirement is the maximum of the two. The live boot frame is not added
to that reservation, and no transition from a fault cut to either root is
inferred. The bounds assume valid nonwrapping storage, the stated transfer and
root-thunk contracts, and ordinary instruction completion. The result keeps
native admission, formal native correspondence, source correspondence, stack
metadata agreement and firmware forwarding false. The mathematical
`BootNativeFrameCut` lemmas compose explicit step/frame/thunk premises; they do
not prove the Rust analysis or the concrete instruction implementation.

This standalone library also links the compiler's `anl` library to obtain the
opaque emitted `Bundle`; it accepts no caller-supplied leaf summary or authority
map. It remains outside the compiler's ordinary module and build-command paths.
No native build or CLI route is enabled by these analyses.

## Publication

Emission finishes all six bounded payloads before filesystem work. The parent
directory must exist; the final component must be a basename without a trailing
separator, `.` or `..`. Publication writes and verifies a fresh sibling staging
directory, then uses an atomic no-replace rename. Existing files, directories
and symlinks are preserved. Failure to support that operation is an error; there
is no overwrite fallback. Failed publication retains staging and reports its name.

Construction exhaustion is status 3; I/O, invocation or publication failure is
status 4. Atomic publication does not promise crash durability or protection
against a hostile process with the same filesystem permissions. The command
invokes no target compiler, linker, firmware or emulator. `build --toolchain`
remains unsupported, and the complete ANL-authored OS remains unfinished.
