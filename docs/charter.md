# APL language charter

APL is a general-purpose, strongly and statically typed programming language for
native systems software, high-performance computation, and reliable agent
applications. Its design combines explicit control over resources with expressive
abstractions and integrated formal verification.

APL is currently under development. The architecture describes intended behavior;
it does not establish implemented functionality, proven safety, or performance.

## Language goals

- Reject invalid operations at compile time through precise type rules and sound
  inference. Require explicit conversions where information or safety could be lost.
- Support functional and imperative programming, including algebraic data types,
  exhaustive patterns, generics, closures, mutable state and structured control flow.
- Provide predictable resource lifetimes, ownership and safe references without a
  mandatory tracing garbage collector.
- Compile efficient native executables with explicit memory layout, operating
  system interfaces, native linking and controlled unsafe interoperability.
- Support threads, asynchronous tasks, structured concurrency, message passing
  and synchronization under a defined concurrency memory model.
- Make formal specifications, contracts and verification part of ordinary
  development without requiring a proof for every program.
- Provide typed, observable, capability-controlled agent libraries with durable
  workflows, replay, resource budgets and explicit approval boundaries.

## Defined behavior and evidence

The language specification defines syntax, typing, evaluation, errors, memory,
ownership, effects, concurrency and external interactions. The formal model and
implementation must describe compatible behavior.

Mechanized foundations establish properties for explicitly named language
subsets. Program verification establishes named properties under stated
assumptions. Compiler correctness requires its own evidence for transformations
and code generation. A proof about one part does not certify the entire toolchain.

Type checking, testing, dynamic checking, solver verification and kernel-checked
proof are reported separately. Failed, unsupported, unknown and timed-out proof
attempts never count as established properties. The trusted computing base and
proof coverage remain documented.

Safe concurrency guarantees must distinguish race freedom from deadlock,
starvation and logical protocol correctness. Agent verification constrains
software behavior; it does not establish the truth of external model responses.

## Complete development environment

The complete toolchain must include a native compiler, runtime, comprehensive
standard library and verification system. It must provide project creation,
builds, packages, formatting, linting, tests, documentation, editor integration
and debugging.

Installation must work in clean supported environments using versioned artifacts
with integrity checks. Ordinary users must not need internal compiler or proof
development dependencies. Upgrade and uninstall procedures are part of release
qualification.

The learning material includes a book, working examples, precise language and
library references, and guides for verification, compiler internals, agents,
installation, contribution and interoperability. Documentation is versioned,
searchable and checked against actual language behavior.

A technical whitepaper documents the completed implementation, mathematical
foundations, verified guarantees, trusted components, reproducible measurements,
related work and remaining limitations. It is published as version-controlled
source and a professionally typeset PDF.

## Release standard

The [requirements](requirements.md) define the full capability inventory and
validation criteria. The [roadmap](roadmap.md) divides delivery into executable
increments. An early compiler or formally defined core is a milestone toward the
complete language.

A release requires working integrated programs, passing conformance and regression
tests, checked proof artifacts, security evaluation, reproducible performance
evidence and independent installation and developer-workflow validation. Claims
must match the evidence available for that release.
