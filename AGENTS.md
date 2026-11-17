# APL engineering instructions

Read `/Users/dylanmitic/workspace/agent-skills/guidance/skill-routing.md` when it
exists on the host. Use the relevant engineering and domain skills within the
assigned scope. On other hosts, use available equivalents without installing
unrelated tools.

Start with `notes.md`, `docs/project/requirements.md`, and the architecture
documents relevant to the assignment. The unabridged mandate is
`docs/project/founding-charter.txt`.

- Preserve the full release requirements. A working subset is a milestone.
- Distinguish designed, implemented, tested, machine-checked, and released work.
- Never call a theorem proved without running the pinned proof checker.
- Keep proof coverage and the trusted computing base explicit.
- Agree on syntax, arithmetic, evaluation order, and IR contracts before parallel
  implementation. Update the specification and conformance cases with changes.
- Own disjoint files during parallel work. The coordinator integrates commits.
- Independently review type rules, unsafe code, verification, and compiler passes.
- Record actual commands, results, remaining defects, and next assignments in
  project records. Do not claim idle or terminated agents are still working.
- Commit only reviewed scoped changes. Never bypass branch protections or publish
  release claims before the release acceptance criteria hold.

The current repository is `djsydney04/ANL`. The language name in the charter is
APL. Do not create or rename repositories as an incidental setup step.
