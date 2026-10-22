# Normalization validation (current checkpoint)

The clean starting checkpoint was `a07b3982cd50653c07309daeaa098950f63337ac`
on main. SSH fetch left local and remote main equal. The cached baseline
strict build/audit passed: 23 source files and 1457 project declarations.
Completed conditional and presentation constructions were reused unchanged.

The integrated working-source verification finished at
2026-10-22T14:53:31.735167+00:00: `bash scripts/verify.sh` exited 0 with
**25 Lean source files and 1601 project declarations**. The permitted axioms
remain `propext`, `Quot.sound`, `Classical.choice`; the selected new normalization
declarations use only the first two. Pinned Lean 4.35.0, Init-only production
closure, and the dependency-free manifest are unchanged. One build/audit ran
at a time, with LEAN_NUM_THREADS=1; no clean rebuild of old constructions ran.

Both existing boundary scripts exited 0. All three axiom-injection controls
and both presentation controls rejected with exit 1 and expected diagnostics.
Public import closure passed. Manuscript v4 `sha256sum -c SHA256SUMS` and
`git diff --check` exited 0. Detailed command/result records, source inventory,
raw evidence, and hashes are in `provenance/wsl-normalization/` and
`.codex-work/normalization/`. The strict log's HEAD is the baseline; its dirty
working source is identified by the retained per-file hashes. Post-commit
verification, SSH ref agreement, and report delivery receipts are separate
runtime records; the completion response gives the integration commit.

`Presentation.normalization P` now supplies object normal forms, actual
comparison inverses, inverse tagged coordinates, signed literal correspondence,
and transport formulas for arbitrary P. Global signed-label preservation,
Boolean Coherence, derived arrow negation/naturality, congruence restriction,
remaining substitution-schema/Appendix A laws, and the intended maximality/model
corollary remain open. No milestone is promoted to complete.

The author-side hostile-referee audit addresses the actual new construction
and map. The writing report is explicitly provisional because official
governing-source requests failed; no source-grounded final writing review is
claimed. No independent kernel replay, Challenge/Solution or Comparator run,
independent source audit, official preflight, service verification, publication,
novelty review, or new manuscript compilation ran. Visibility/license and v4
text/diagrams/references were not changed. See
[the normalization report](NORMALIZATION_REPORT.md) and its linked reviews.

---

## Historical presentation-bridge validation (unchanged evidence)

# Presentation-bridge validation

The actual source-presentation bridge was verified locally in WSL2 on
2026-10-22T04:48:37.645568+00:00. Baseline HEAD was
`d7162e7945c98288fe3640506b8e1471c63150ef`, clean on main; SSH fetch left main
and origin/main equal. The baseline strict verification exited 0 and audited
645 declarations. The conditional proof modules and manuscript v4 are unchanged.

The final working-source strict verification exited 0: **23 Lean source
files and 1457 project declarations**. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted by the transitive dependency audit, including
private declarations. The pinned Lean 4.35.0 and dependency-free manifest are
unchanged. New production modules ultimately import only Init.

`bash scripts/verify.sh`, `python3 scripts/check-audit-boundaries.py`,
`python3 scripts/check-presentation-boundaries.py`, manuscript
`sha256sum -c SHA256SUMS`, and `git diff --check` all exited 0. The three axiom
controls each rejected with exit 1 for the named illicit dependency. Both
presentation controls rejected with exit 1: identified tagged projections and
an attempted zero without a correctly typed existing-arrow witness.

Exact commands, exit codes, environment, source inventory, raw logs, and hashes
are retained in `provenance/wsl-presentation-bridge/` and
`.codex-work/presentation-bridge/`. The strict log prints the baseline HEAD and
a dirty working source; the inventory identifies the code actually checked.
The final integration SHA and SSH ref equality are recorded in the completion
response, with post-commit verification under `.codex-work/presentation-bridge/`.

The source quotient has structural, constructed-zero, substitution, and
double-negation instances, plus a well-defined occurrence assignment.
Faithfulness, normalization, signed labels, derived arrow negation, remaining
substitution/congruence correspondence, actual maximality, and the model
corollary remain open. No independent kernel, Comparator, official preflight,
service verification, independent peer review, or publication is claimed.
See [the presentation report](PRESENTATION_BRIDGE_REPORT.md) and its linked
reviews. Repository visibility and licensing were not changed.

---

## Historical contextual-collapse validation (unchanged evidence)

# Validation record

Local verification ran in the actual WSL2 checkout on 22 October 2026 UTC
(21 October America/New_York). The pinned Lean toolchain was already installed;
`setup-wsl.sh` was unnecessary. Both the initial baseline and the integrated
strict verification exited 0. This replaces the earlier WSL-pending status.

The baseline source was `37e1ee3792d04e3634ff6737a3da436e7c1ef476`, initially
clean on `main`, tracking `origin/main`. The origin was
`git@github.com:flengyel/Dosen-Petric-Maximality.git`. Work continued on
`codex/contextual-collapse`. The user subsequently authorized integration into
`main` and an SSH push to `origin/main`. Visibility and license are
unchanged. The checkpoint source hashes and raw build log are preserved
under `provenance/wsl-contextual-collapse/`.

| Check | Observed result and boundary |
| --- | --- |
| Host | Linux M2MA3HI, `6.6.87.2-microsoft-standard-WSL2`, x86_64. Initial memory: 15 GiB total, about 11 GiB available; no swap. |
| Toolchain | Lean 4.35.0, release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb`. No replacement runtime or cross-project compiled artifacts. |
| Command | `bash scripts/verify.sh`, with `LEAN_NUM_THREADS=1`, strict warnings, and `autoImplicit=false`; one build/audit at a time. Exit 0 at baseline and after implementation. |
| Source screening | All 12 Lean files passed module-header, line-count, symlink, and forbidden-token checks. This conservative script is not a Lean parser. |
| Build | Public library and all seven new modules compiled. The generated manifest still has no external packages. Mathlib and Foundation were not added. |
| Axiom audit | 645 visible project declarations checked transitively, including private names via `Lean.privateToUserName`. Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. |
| Selected dependencies | Collapse and generated model use `propext`, `Quot.sound`; isolation and relative maximality also use `Classical.choice`. Contextual retract and all-context transport print no axioms. |
| Negative controls | Direct public axiom, private-name axiom, and a theorem depending on an external private axiom each exited 1 with the required dependency rejection. Sources, commands, statuses, and hashes are retained. |
| Public import closure | Every production module is reachable from `DosenPetric.lean`. This is a local import check, not independent statement or shared-definition comparison. |
| Manuscript integrity | `sha256sum -c SHA256SUMS` from `manuscript/` exited 0 for unchanged v4 TeX and PDF. No text, diagram, or Appendix A reference was changed. |
| Review | Author-side hostile-referee and source-grounded mathematical-writing reviews applied to §§4–5, the implementation, and correspondence map; see `docs/reviews/`. These are not independent peer review. |

## Audit visibility correction

A focused control initially compiled an unused private mathematical axiom
without rejection: the old namespace filter compared only its encoded
internal name. The filter now applies `privateToUserName` before selecting
project declarations, increasing the integrated audit from 619 to 645.
The direct, private, and hidden-dependency controls all reject with this fix.
The audit still uses the compiler's visible environment and exported
transitive dependency data; it is not independent kernel replay.

Imported theorem signatures can appear as `axiomInfo` in Lean 4.35.0's module
interface. The audit collects dependencies for all declaration kinds instead
of interpreting that representation as a new mathematical axiom. See the
pinned upstream [CollectAxioms implementation](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Util/CollectAxioms.lean).
All current production declarations use the DosenPetric namespace. New
namespaces or changes in declaration ownership require corresponding audit
coverage.

## Reproducible evidence

The evidence directory preserves the baseline environment and log, integrated
verification log, source inventory and SHA-256 hashes, and negative-control
report and raw files. Its record identifies the baseline commit plus exact
working-source hashes rather than mislabelling a dirty build as a test of the
baseline commit. Session logs remain in `.codex-work/contextual-collapse/`
and `.codex-work/verification/`. The final committed-source verification is
recorded separately there after creating the local checkpoint.

## Mathematical and external boundaries

`ContextualCollapse.total` and `relative_maximality` are conditional theorems.
The complete §5 interface has a generated nonthin fragment model with an empty
hom-set. The actual Došen–Petrić presentation, its coherence theorem, its
normalization and substitution bridges, and the every-interpretation model
corollary remain open. No milestone is promoted to an actual-presentation
formalization by the model check.

No Challenge/Solution packaging, Comparator comparison, NanoDa/con-ron replay,
official Palomar preflight, service verification, automated service review,
or publication has run. The official policy must be rechecked before those
separate tasks. The historical CI baseline at code commit
`75b3a70482e90094bd147236b22324995522ad5d` remains in
`provenance/ci-75b3a704-build.txt`; it is not substituted for local WSL evidence.
