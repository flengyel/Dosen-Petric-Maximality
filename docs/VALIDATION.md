# Validation record

The preliminary Lean development passed GitHub Actions on 22 October 2026 UTC
at code commit `75b3a70482e90094bd147236b22324995522ad5d`.
[Run 39705867222](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/39705867222)
and job 119585645097 completed successfully. The build and audit output is
preserved in `provenance/ci-75b3a704-build.txt`; the source hashes in that
record identify the exact Lean files. Later documentation commits are covered
by their own commit-specific CI runs.

| Check | Result and boundary |
| --- | --- |
| Official compiler | Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc; release archive SHA-256 checked by CI. Lake 5.0.0-src+eb6cafb. |
| Clean build | `lake build` passed on Ubuntu 24.04 with `warningAsError = true` and `autoImplicit = false`. The committed manifest has no external packages. |
| Source screening | Five Lean source files passed module-header, line-count, symlink, and forbidden-token screening. The Python script is a conservative screen, not a Lean parser. |
| Axiom audit | `lake env lean -DwarningAsError=true Checks/Axioms.lean` passed for 176 visible declarations under the DosenPetric namespace. All declaration kinds are inspected. Dependencies outside propext, Quot.sound, Classical.choice are rejected. |
| Representative results | The zero-arrow and occurrence inverse lemmas printed no axioms. The selected relation equalities printed propext and Quot.sound. No proof hole or custom mathematical axiom is used. |
| Script syntax | Bash parsed verify.sh, setup-wsl.sh, and fetch-palomar.sh successfully. The WSL setup script has not been executed on the user's machine. |
| Manuscript integrity | The TeX and PDF match the supplied v4 SHA-256 checksums. No manuscript text or diagrams were revised. |
| Mathematical milestones | Contextual collapse, relative maximality, and the actual-presentation theorem are all open. |
| Independent verification | No Challenge/Solution comparison, NanoDa/con-ron replay, official Palomar preflight, or service verification has run. |

## Lean module-interface handling

The audit uses Lean's `collectAxioms`, including the compiler's exported
dependency data. In Lean 4.35.0 an imported theorem signature may have
`axiomInfo` representation. Treating that representation as a new mathematical
axiom incorrectly rejected the generated constructor theorem
`DosenPetric.ZeroIdentity.mk.injEq`. The corrected audit collects dependencies
for every visible project declaration kind, rather than rejecting the
signature representation or skipping it. An actual axiom appears in its own
dependency set and fails the allowlist.

This is an audit using the compiler's environment, not an independent kernel
replay. See the pinned upstream
[CollectAxioms implementation](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Util/CollectAxioms.lean).
The current production modules expose their declarations in the DosenPetric
namespace. Any later change to module visibility or ownership must extend
the audit coverage accordingly.

## Environment boundary

The cloud preparation environment could download and hash the official Lean
archive, but its Lean executable failed to locate itself in that sandbox.
No locally modified runtime or kernel was substituted. Compilation was
therefore performed by the repository's GitHub Actions runner.

There is no connection from this session to the user's WSL2 filesystem.
After cloning at `/home/flengyel/src/Dosen-Petric-Maximality`, run
`bash scripts/setup-wsl.sh` and retain `.codex-work/verification/verify.log`.
Do not report that local validation as complete before it runs.
