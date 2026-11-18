# ANL-authored operating system

Status: the required OS is not bootable. The first selected bring-up profile is
RV64 supervisor mode on `rv64-virt-sbi-v1`, with one hart and external OpenSBI
firmware. [Boot source checking and Core interchange](../book/boot-profile.md)
are implemented, including explicit stacks, UART authority and terminal roles.
Native entry/trap ABI generation, hardware execution and image building remain
unfinished. No kernel structure has been selected. Hosted compilation still uses
a Rust compiler that emits C11 with libc output/failure helpers.

The [OS authorship and expressibility gate](../requirements.md#os-authorship-and-expressibility-gate)
is mandatory for completion and final release. Missing OS expressibility requires
an ANL language/compiler extension, followed by an ANL subsystem implementation.

The current scoped-buffer runtime uses a hosted C allocator adapter. Its profile,
fallible request ABI, resource checks and formal heap model support language
bootstrap work. They do not implement physical/virtual memory management, page
tables, a freestanding allocator or an ANL OS subsystem. Those operations still
need ANL language/compiler primitives and ANL implementations under the authorship
gate linked above.

## Planned subsystem boundaries

| ANL-owned subsystem | Responsibility |
| --- | --- |
| Boot and hardware initialization | Enter through the specified handoff, establish execution state, initialize hardware and start the OS |
| Interrupts and scheduling | Define handlers, dispatch events, save/restore task state and schedule execution |
| Memory management | Own physical memory, virtual address spaces, mappings, page tables and allocators |
| Drivers | Manage device discovery, registers, DMA, interrupts and device lifecycle |
| Filesystems and networking | Implement storage formats, persistence, protocols and resource lifecycles |
| System services | Expose explicit authority, isolation, process/task and service interfaces |
| Agent infrastructure | Provide typed tools, durable execution, capability enforcement, budgets and replay over OS services |
| GUI | Provide display, input, rendering and interactive system surfaces over OS services |

These boundaries describe required behavior without choosing a monolithic or
microkernel design. Hosted file, allocation or network adapters exercise language
features but do not supply these OS implementations. Library dependencies that
implement OS behavior are subject to the same ANL authorship requirement.

## Hardware operations (planned)

The [first boot profile](../../spec/boot-profile.md) defines a narrow set of
statically checked UART byte, fence and machine-initialization forms. Their native
lowering and hardware execution are not yet available. The broader operations
below remain language/compiler work; their general interfaces are undecided. Each feature requires a versioned language
contract, target profile, typed IR representation, validated lowering and
executable conformance evidence before exposure. Unsupported targets and invalid
static operands must be rejected; dynamic preconditions must be checked or stated
as explicit unsafe obligations. A scalar safety proof does not cover these effects.

| Operation | Required semantics and safety boundary |
| --- | --- |
| Low-level types, addresses and layout | Define widths, alignment, representation, pointer provenance, address spaces and conversions. Raw addresses cannot manufacture safe references; initialization, lifetime and alias permissions remain explicit obligations. |
| Register and memory-mapped I/O access | Specify target register selectors, privilege, access width, alignment, clobbers and device-visible effects. MMIO must preserve required accesses; volatile access alone provides neither atomicity nor inter-thread synchronization. |
| Interrupt entry and return | Define saved state, stack/alignment requirements, masking, nesting, reentrancy and the target return convention. Compiler-generated entry/exit sequences must connect to ANL handlers without ordinary-call or unwinding assumptions that violate that convention. |
| Atomics | Define supported widths/alignment, indivisible operations and memory ordering. The initial language concurrency contract is sequential consistency; weaker ordering needs its own model and evidence. Interrupt-safe contexts must not secretly use blocking helper locks. |
| Barriers | Distinguish compiler ordering from CPU memory ordering, device ordering and instruction synchronization. State the ordered observations, address domains and target effects; a compiler fence alone cannot promise hardware ordering. |
| Port I/O | On targets that provide ports, define port/address width, transfer width, privilege and ordering separately from ordinary memory. Reject the operation on targets without that facility. |
| Page-table operations | Define entry layout, address/alignment constraints, access permissions, ownership and update ordering. Specify translation activation, invalidation and multicore visibility. ANL implements mapping policy and shootdown protocols using those primitives. |

Privileged and unsafe operations must expose the invariants their callers assume.
Safe ANL APIs can wrap them only when they establish those invariants, including
device ownership, live mappings, interrupt context and concurrent access rules.
DMA additionally requires an explicit contract for device ownership, cache
coherence and visibility; ordinary reference rules alone cannot establish it.

The compiler may generate target instruction sequences from these specified
primitives. An intrinsic is not a way to hide a handwritten C/Rust allocator,
scheduler, driver or other OS subsystem. Generated code and linked helpers must
remain traceable to ANL source or a documented primitive lowering.

## Boot and external trust boundary

The selected initial bring-up uses external OpenSBI firmware. Its target contract
must identify their supplied state and services, entry ABI, memory map, reserved
regions, device state, and the point where ANL takes ownership. Continued firmware
calls require explicit lifetime, privilege and trust assumptions. Hardware and
firmware behavior are not established by ANL type checking or existing proofs.

The OS's own boot responsibilities remain ANL work. An external handoff does not
move hardware initialization, interrupt handling or memory management out of
scope. Temporary handwritten assembly or other non-ANL OS code follows the
gate's minimum-size, missing-capability, replacement-plan and milestone-reporting
rules; it must be eliminated before completion or final release.

## Delivery evidence

The [roadmap](../roadmap.md#anl-os-delivery-track-planned) sequences language
extensions, boot, core OS subsystems, services, agents and GUI. Each increment
must identify implemented ANL source, generated artifacts, remaining gaps and
exact target evidence. Final acceptance traces the full bootable image and its
dependencies, exercises every required subsystem together, and closes the
authorship gate. Hosted language tests and scoped model proofs retain their
existing limits; neither is evidence that the OS already works.
