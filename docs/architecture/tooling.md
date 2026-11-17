# Toolchain and developer ecosystem architecture

Status: the CLI implements scalar checking, interpretation, native compilation,
file modules, local scalar state and loops, v0/v1 core interchange, and pure acyclic
contract verification. Verification rejects local-state constructs before tools run. Package management, formatting, language-server
integration, source debugging, and release distribution below remain design
proposals unless explicitly identified as implemented.

## One compiler library, several clients

The `apl` CLI calls the compiler library for parsing, resolution, type checking and diagnostics. The planned `apl-lsp` language server will use the same library. The formatter consumes a syntax representation retaining comments and trivia, because a semantic AST cannot preserve them reliably. The documentation generator consumes resolved public declarations and documentation comments. No client reverse-engineers another client's human-readable output.

The current CLI contract is in [compiler architecture](compiler.md). Implemented commands are `check`, `eval`, `build`, `run`, `emit-c`, `verify`, `dump-core`, `eval-core`, and `--version`. Unsupported commands fail explicitly. `verify` reports per-obligation outcomes using Z3 5.3.3; its [guide](../verification.md) explains solver installation, limits, and trust. `new`, `test`, `fmt`, `lint`, `doc`, `add`, and `update` arrive with their working implementations. Publishing help for nonexistent commands must identify them as unavailable.

Diagnostics have a code, severity, primary source span, message, related spans, and optional fixes. UTF-8 byte offsets are the compiler's internal representation. The LSP adapter converts positions according to the negotiated encoding and tests non-ASCII source. The implemented `verify --json` mode emits the versioned `apl-verify-v0` report with structured status and exact source/tool/query identities; diagnostics go to stderr. Its executable semantic revision follows the complete checked program, including v1 for unsupported local state, and is null for source failures before a program is checked. General JSON diagnostics and the LSP adapter remain planned.

## Package and module identities

The implemented [module system](../modules.md) uses explicit `mod name;`
declarations and sibling source files, with private/public interfaces and qualified
paths. The loader builds a bounded canonical graph, shares repeated dependencies,
and rejects cycles. `compile_file(path)` performs this loading;
`compile(source)` remains an in-memory operation. Immutable source snapshots retain
file-specific diagnostics. Native compilation lowers the whole graph together;
there is no package search, network resolution, lockfile, or separate-object cache.
The package design below is a later extension of these boundaries.

`apl.toml` declares package name, version, language edition, targets, dependencies, and declared native links. `apl.lock` records exact source identity, package version or commit, integrity digest and transitive dependencies. The first package implementation supports local workspace packages and locked immutable Git revisions. A registry can follow once publishing identities, immutability, namespace policy and incident response exist.

Module names are lexical identities resolved inside a package. Dependencies are addressed by declared aliases and exact package identities, not arbitrary filesystem traversal. Exported interfaces carry type parameters, ownership/effect requirements and API contracts. Private implementation details do not become visible merely because a source file is readable. Cyclic module and package dependencies have an explicit rejection or strongly connected component policy before support is advertised.

Ordinary builds use the lockfile and do not update dependencies. `apl update` resolves and rewrites it deliberately. `--locked` rejects stale or missing resolution, and `--offline` forbids network access. Local path dependencies are permitted for development but their content digests become release-build inputs. Package extraction rejects path traversal, symlink escape and conflicting entries.

This separation follows the [Cargo manifest/lockfile precedent](https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html). APL's design adds its own edition, runtime ABI and verification metadata; dependency locking alone does not guarantee reproducible binaries.

## Build graph and reproducibility

Build artifacts are keyed by source and dependency digests, compiler version, backend version, target triple, target features, profile, language edition, relevant environment values and runtime ABI. Future verification caches must additionally include contracts, solver version, proof options, assumptions and resource limits. The current verifier binds reports to these inputs but does not import reports or cache proof results. A cached timeout must never become a successful proof under a different configuration.

The driver resolves package dependencies, checks public interfaces, builds a module dependency graph, checks semantic bodies, specializes generic code, lowers and links. Incremental execution may skip unchanged work only when all semantic inputs are in the cache key. The first implementation uses a simple deterministic graph; parallel scheduling comes after race-free cache publication and cancellation handling.

Native build scripts are disabled by default. A package needing generated source declares the generator, inputs, outputs and allowed capabilities. Builds never execute a fetched package's arbitrary code silently. Reproducible mode controls locale, timestamps, paths and environment inputs. Clean repeated builds compare artifact hashes, and differences are explained before claiming bitwise reproducibility.

## Formatting, tests, lints and documentation

Formatting is deterministic and idempotent. The formatter preserves comments and parses its own output. Source round-trip tests compare resolved meaning, with exact golden output for layout choices. `fmt --check` reports changes without rewriting files.

The test runner uses explicit test declarations, collects independent outcomes, bounds time, and reports pass/fail/skip accurately. It invokes the same semantics as ordinary programs. Unit tests, compile-fail fixtures, executable documentation examples, runtime tests and proof checks have distinguishable statuses. Tests do not imply formal verification.

Lints operate on typed information where needed and have stable codes. Suppressions are scoped and visible. Safe automated fixes validate the result; a lint must not erase a required runtime check or effect merely to simplify code.

API documentation comes from public interfaces and tested examples. The documentation site is versioned with the toolchain and searchable. It includes the Book, examples, precise language reference, standard library API reference, verification guide, compiler internals, agent guide, installation, contributor and interoperability guides required by the charter. Every page distinguishes current syntax from proposed features. The whitepaper source references these versioned specifications and actual proof/evaluation artifacts.

## Editor and debugging integration

LSP provides document synchronization, diagnostics, hover, completion, definition lookup, references and rename as supported features. [LSP 3.17](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/) is the protocol baseline. Initialization advertises only implemented capabilities. Cancellation and document-version checks prevent stale edits from applying to a newer buffer.

The current frontend retains source spans and source snapshots for diagnostics; the C11 backend does not yet provide APL source debugging. M2 source-debugging work requires line information and mappings for functions, lexical scopes, variables and types, plus tests in LLDB or GDB. [LLVM's debug-information tutorial](https://llvm.org/docs/tutorial/MyFirstLanguageFrontend/LangImpl09.html) provides a reference for the later direct backend. Debugger success requires stepping an APL program and inspecting its locals, not merely emitting debug flags.

Async stack views and agent trace inspection are later extensions. Release documentation must state whether a particular debugging operation is supported for an optimized build, native target or runtime feature.

## Installation and release contents

The development toolchain uses pinned Rust, Lean and backend tools. End users receive versioned native binaries and required runtime/backend assets. Running an already-built APL binary must not require Rust, Lean or an SMT solver. Verification can be an explicit optional component, but `apl verify` must explain its absence and installation path.

Initial supported platforms are earned individually by clean CI and independent onboarding tests. The candidate matrix is macOS AArch64 and Linux x86-64, followed by macOS x86-64, Linux AArch64 and Windows x86-64 when verified. A source-build success on one host is not a portable release claim.

Release artifacts contain the CLI, compiler libraries where needed, runtime, standard library, license notices, version manifest and integrity information. Provide a package-manager installation route where maintained, plus versioned archives and documented upgrade/uninstall. Keep an installed version usable while an update downloads; activate only after validation. Do not overwrite a working installation with a failed update.

Checksums detect corruption. Authenticated release metadata establishes provenance. Evaluate signed repository metadata using [The Update Framework](https://theupdateframework.github.io/specification/latest/) before enabling automatic updates, and document how verification keys are trusted and rotated. No signature is claimed without the actual published artifact and verification procedure.

## Onboarding and quality gates

An external developer receives only published installation and learning materials. In a clean environment they install APL, inspect `apl --version`, create a project, run it, add a package, see a type error, correct it, and verify a contract. Later release exercises add a generic collection, concurrent application, network service and capability-controlled agent.

The release gate records the exact artifact, platform, commands, expected and observed outcomes, and problems found. Tests run without access to development checkout caches or unpublished instructions. Documentation examples, package resolution, formatter idempotence, LSP behavior, native debugging and upgrades have their own integration tests.

CI grows with implementation. M1 gates compiler tests, conformance, actual formal checks and documentation examples. M2 adds native execution and target-specific checks. Later phases add package integrity, fuzzing, runtime race tests, security review, performance baselines, signed release verification and clean installation. A skipped platform or unavailable solver is recorded as unverified, never as passing.

## Component interfaces

The compiler library provides semantic APIs and source mapping. Tooling consumes those APIs for the CLI, packages, LSP, formatting and documentation generation. Runtime ABI versions constrain distribution compatibility. Verification reports and proof-cache entries follow the formal semantics. Shared JSON, manifest, lockfile and ABI formats require versioned specifications and compatibility tests. Clean-environment release checks validate the combined toolchain.
