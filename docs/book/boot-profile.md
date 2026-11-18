# Check and emit an ANL boot program

ANL can check a boot program for the `rv64-virt-sbi-v1` profile and export its
checked Core representation or a complete freestanding source bundle. This first
profile selects one RV64 hart, supervisor mode, explicit stacks and a UART device.
The compiler does not yet link or run a boot image.

From the repository root, build the CLI as described in
[Getting started](../getting-started.md), then run:

```sh
./target/release/anl check examples/boot/park.anl
./target/release/anl dump-core examples/boot/park.anl > /tmp/anl-boot-core.json
./target/release/anl eval-core /tmp/anl-boot-core.json
```

`check` succeeds silently with exit 0. `dump-core` writes an `anl-boot-core-v1`
document. `eval-core` checks that document, prints
`{"outcome":"unsupported_boot_operation"}`, and exits 7. It does not execute
the terminal loop or access hardware.

The [UART example](../../examples/boot/uart.anl) also checks and exports. It
expresses polling, byte writes and fences in ANL, with an intended `ANL` plus
newline byte sequence. Those device effects have not been executed by the boot
toolchain; checking and source emission do not establish device behavior.

```sh
./target/release/anl check examples/boot/uart.anl
./target/release/anl dump-core examples/boot/uart.anl > /tmp/anl-uart-core.json
./target/release/anl emit-boot examples/boot/uart.anl --out /tmp/anl-uart-bundle
```

`emit-boot` succeeds silently and creates a directory containing `core.json`,
`mir.json`, `program.c`, `entry.S`, `link.ld` and `manifest.json`. The parent
directory must already exist and the destination must be absent. Choose a fresh
destination on subsequent runs. An existing file, directory or symbolic link is
preserved; publication fails with exit 4 and identifies the retained staging
directory. Output construction limits fail with exit 3 before creating staging.

The manifest records payload hashes, source spans, structural Core/MIR locations,
generated code ranges and the three selected terminal loops. All polling, byte
sequences and terminal-loop policy come from ANL source. Generated code supplies
individual primitive instructions, checked arithmetic and entry ABI adaptation.
The [bundle specification](../../spec/boot-bundle.md) defines these boundaries.
This command invokes no C compiler, assembler, linker or emulator.

## Declare the platform and roles

The complete [park example](../../examples/boot/park.anl) is:

```anl
platform rv64_virt_sbi_v1 {
    image_base 2149580800u64;
    image_limit 1048576;
    stack boot_stack[16384] align 16;
    stack terminal_stack[4096] align 16;
    device uart0 at 268435456u64 size 256 {
        read8 5;
        write8 0, 1, 2, 3, 4;
    }
    entry boot_entry using boot_stack;
    hardware_trap hardware_fault using terminal_stack;
    language_trap language_fault using terminal_stack;
}

fn boot_entry(hart: u64, opaque_dtb: u64) -> unit effects(machine, uart0) {
    hw::csr_clear(machine, sstatus, 2u64);
    hw::csr_write(machine, sie, 0u64);
    hw::install_trap(machine, hardware_fault);
    while (true) {}
}

fn hardware_fault(raw_scause: u64, raw_sepc: u64, raw_stval: u64) -> unit {
    while (true) {}
}
fn language_fault(tag: u8) -> unit {
    while (true) {}
}
```

The platform block comes first. Its declarations may be reordered, but every
one is required and must use the profile's exact values. This version supports
exactly these two stacks and one device. A declaration records the intended
layout and permissions; it does not reserve physical memory or prove stack space
is adequate.

Role selectors name three distinct functions. Their names are chosen by the
program; their parameter and result types are fixed. A boot program does not
need `main() -> i64`. Ordinary calls cannot invoke any role function. The first
three boot statements must be the shown machine operations, in that order.
Machine authority cannot be used elsewhere, including in an unused helper.

Both trap handlers must contain exactly `while (true) {}`. The boot body must
also have a structurally designated terminal loop: a literal-true loop with an
empty body, possibly reached through a sequence of lets. The compiler checks
unreachable code too. A terminal loop is not a license to leave its suffix
ill-typed, and this structural check does not establish physical fault behavior.

## State which hardware authority a function uses

`effects(...)` follows the result type and precedes any `requires` or `ensures`
clauses. The boot function must declare both `machine` and `uart0`; handlers
declare neither. Other functions may declare `uart0` or no effects. Omission
means an empty set. Source order is immaterial; duplicate authorities are errors.

For example, this helper has UART authority and returns a byte:

```anl
fn status() -> u8 effects(uart0) {
    hw::read8(uart0, 5)
}
```

Every call requires the callee's effects to be included in the caller's effects.
The checker applies that rule to every function and branch. Imports, recursive
call cycles, heap buffers and views are excluded from this boot profile.
Existing word-free contracts and invariants are checked and erased using their
ordinary rules; hardware operations cannot appear in specifications.

The accepted hardware forms are deliberately narrow:

| Source form | Result | Required effect |
| --- | --- | --- |
| `hw::read8(uart0, 5)` | `u8` | `uart0` |
| `hw::write8(uart0, OFFSET, byte)` | `unit` | `uart0` |
| `hw::fence_io(uart0)` | `unit` | `uart0` |
| `hw::csr_clear(machine, sstatus, 2u64)` | `unit` | `machine`, first boot statement |
| `hw::csr_write(machine, sie, 0u64)` | `unit` | `machine`, second boot statement |
| `hw::install_trap(machine, hardware_fault)` | `unit` | `machine`, third boot statement |

`OFFSET` is a literal from 0 through 4; `byte` is an ordinary `u8` expression.
The install selector must name the declared hardware handler. These forms are
statically admitted operations with generated instruction templates. Hosted
evaluation and device execution are unavailable.

Names `hw`, `machine`, `uart0`, `boot_stack`, and `terminal_stack` cannot be
redeclared in boot source. Prefixes `__hw_` and `__carrier_` are reserved,
including for parameters, locals and specification result binders. Generated
primitive names are not callable from source. Hosted identifier and module
rules are unchanged.

## Select a target and recognize unsupported routes

A valid platform block selects boot mode automatically. Source commands accept
`--target hosted` or `--target rv64-virt-sbi-v1`. Explicit hosted selection
conflicts with a boot platform; explicit boot selection requires one.
`eval-core` selects by its document schema and has no `--target` option.

| Route for valid boot input | Result |
| --- | --- |
| `check FILE` | Silent success, exit 0 |
| `dump-core FILE` | Checked boot JSON, exit 0 |
| `eval`, `run`, `emit-c` | Unsupported diagnostic, exit 7 |
| `verify FILE [--json]` | Unsupported report, exit 7, `trust=not_established` |
| `eval-core CORE_JSON` | Unsupported JSON outcome, exit 7 |
| `emit-boot FILE --out PATH` | Complete source bundle, silent success, exit 0 |
| `build FILE --toolchain LOCK -o PATH` | Not implemented, exit 7 |

Unsupported routes still check the whole source or Core document. Missing
required output/lock arguments are invocation errors after source checking.
No lock is opened, external tool invoked, or destination created by an
unsupported boot operation. `--fuel 0` does not bypass checking. Source/IR errors
exit 1, resource limits 3, and invocation, infrastructure or output failures 4.

`verify --json` uses `anl-boot-verify-v1`. It reports type checking, erased
contracts and no arithmetic-safety, partial-correctness, termination, native or
hardware proof. Static acceptance is not a user-contract verification result.

## What remains

The selected bring-up boundary uses external OpenSBI firmware. ANL-authored boot
policy, initialization, drivers and the rest of the OS remain the objective;
firmware is an explicit external dependency. Generated entry/trap ABI and
primitive instructions still need target qualification. Hardware execution,
interrupt delivery, image linking, emulator and physical-device qualification
remain unfinished. No bootable ANL OS is provided.

The [boot specification](../../spec/boot-profile.md) records the exact static and
Core boundary; the [bundle specification](../../spec/boot-bundle.md) covers paired
MIR and generated sources. The [OS architecture](../architecture/operating-system.md) tracks
the wider language capabilities needed to author the complete OS in ANL.
