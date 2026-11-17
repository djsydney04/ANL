# Contribute to APL

Start with the [architecture](docs/architecture/overview.md) and
[language requirements](docs/requirements.md). The repository currently contains
specifications. Compiler build and proof commands will be documented alongside
their implementations.

## Propose a language change

1. Identify the language capability or defect the change addresses.
2. Describe its behavior, competing alternatives, typing and evaluation rules.
3. Identify affected proof obligations, assumptions and compiler interfaces.
4. Define acceptance criteria and representative programs.
5. Obtain independent technical review of foundational changes.

## Validate an implementation

1. Implement a complete observable behavior.
2. Add positive and negative tests that detect plausible incorrect behavior.
3. Run affected component, integration and proof checks.
4. Update the specification, examples, proof coverage and known limitations.
5. Review the change and retain reproducible validation evidence.

Never disable a failing proof or test to obtain a passing build. Report checks
that could not run. Keep designed, implemented, tested and machine-checked
capabilities distinct.

## Continuous integration

The planned initial documentation checks validate links and required artifacts.
They establish document consistency, not architecture quality or language correctness.

The executable-core milestone adds pinned Rust formatting, lint, unit,
source-conformance and interpreter checks, plus pinned proof-checker builds.
Native compilation adds binary execution and differential tests on supported
platforms. Later checks cover verifier regressions, property testing, fuzzing,
sanitizers, security analysis, performance, documentation examples, installation
and release artifact integrity.

Use reproducible tool versions and lockfiles. Keep workflow permissions read-only
unless a specific operation requires more. Keep secrets out of logs and source
files. Release qualification requires the checks relevant to the capabilities
being published.
