# Boot MIR and source bundles

`anl emit-boot FILE --out DIRECTORY` checks an ANL boot program and publishes
six generated files for `rv64-virt-sbi-v1`. It does not compile, link or execute
them. The [source and Core profile](boot-profile.md) remains the admission boundary.
Source policy, including UART initialization, polling and terminal loops, stays
in ANL. No handwritten C/Rust OS subsystem is linked or copied into the bundle.

## Checked canonical pairs

The Rust library's `anl::boot::lower` consumes a `CheckedProgram` and returns an
opaque `CheckedPair`. `import_pair(core_text, mir_text)` independently checks the
Core document and raw MIR, then requires the entire decoded MIR, including counts,
to equal canonical lowering of that Core. A structurally typed alternative MIR
is insufficient. `export_pair_core` and `export_mir` export the paired documents;
`emit(&pair)` returns an immutable `Bundle` with `files()` and `publish(path)`.
There is no hosted-program conversion or standalone boot MIR permit.

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
to the build command or admits an executable. Native semantic correspondence, typed
helper/primitive authority, ISA/ABI conformance, stack adequacy and exact
DWARF/source-loop correspondence remain open. Text reconstruction does not
establish native correctness.

A standalone instruction-inspection library consumes the text reconstruction and
decodes the closed RV64IM+Zicsr profile into instruction descriptors and known
control-flow edges. It rejects forbidden encodings and register uses, and known
control entries that bypass the first instruction of a relocated call pair.
Return-shaped jumps, possible call continuations and eligible memory/CSR/fence
sites retain explicit obligations for later analysis. This inspection does not
establish returns, frames, hardware authority, exact selected-loop identity or
native correctness, and remains unconnected to the build command. Its current
assembly uses separately linked Rust inspection libraries; integration into the
compiler's ordinary modules remains a separate boundary.

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
