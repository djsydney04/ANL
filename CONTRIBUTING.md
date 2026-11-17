# Contribute to APL

Start with the [current state](notes.md) and [requirements](docs/project/requirements.md).
The repository is currently in architecture research. Compiler build and proof
commands will be documented when their implementations exist.

## Propose a language change

1. Identify the charter requirements and the milestone the change serves.
2. State the behavior, competing alternatives, typing and evaluation rules.
3. Define proof obligations, unsafe assumptions and affected compiler interfaces.
4. Add the proposal to the architecture decision records.
5. Obtain independent review before implementing a foundational change.

## Integrate a component

1. Agree on owned files and interfaces with the coordinator.
2. Implement a complete user-observable increment.
3. Add positive and negative tests that would detect a plausible wrong behavior.
4. Run the component tests and affected integration/proof checks.
5. Update specification, examples, trust coverage and requirement evidence.
6. Obtain independent review of critical code and integrate a scoped commit.

Preserve user changes and other agents' assignments. Never disable a failing
proof or test to obtain a passing build. Report unavailable checks as unavailable.

## CI strategy

The initial architecture check will validate repository links and required
artifacts. That check can establish document consistency only, not architecture
quality or language correctness. Independent review supplies the technical gate.

M1 adds pinned Rust formatting, lint, unit, source-conformance and interpreter
checks plus pinned proof-checker builds. M2 adds native execution and differential
tests on supported platform runners. Later stages add verifier regressions,
property/fuzz testing, sanitizers, security analysis, benchmark regression
measurement, documentation examples, installation and artifact integrity checks.

Workflow permissions should be read-only unless a particular release operation
requires more. Pin external actions and dependencies, use lockfiles, and keep
secrets outside logs and repository files. Repository protections remain intact.
Release jobs must depend on all relevant checks and an explicit release audit.
