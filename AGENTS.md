# Project instructions

Work in `/home/flengyel/src/Dosen-Petric-Maximality` under WSL2. Inspect Git
status and the current task before editing. Preserve unrelated work and all
other checkouts, including FailureOfComposition and Categorical_Rice_Shapiro.

Read `docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md`,
`docs/CODEX_NEXT_SESSION.txt`, `docs/MANUSCRIPT_STATEMENTS.md`,
`docs/MANUSCRIPT_COVERAGE.md`, and
`docs/PALOMAR_REQUIREMENTS.md`. The current manuscript in `manuscript/` is v6;
v4 and v5 remain preserved. Preserve the text, diagrams, and Appendix A references
unless revision is requested.

## Full-paper objective

Formalize the complete mathematical content of manuscript v6: the short q_A/e_A
proof, maximality for the actual equation-generated presentation with every
required input proved, the model corollary, all unnumbered mathematical claims,
and both appendices' constructions, equations, examples and diagram identities.
Maintain exact claim-to-declaration correspondence. Preserve the existing
symmetric-fold proof as an alternative route.

`docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md` governs this overall endpoint;
`docs/CODEX_NEXT_SESSION.txt` governs the immediate continuation toward full
Reducibility and coherence. The existing three milestones remain distinct;
even actual-presentation maximality alone does not certify the entire paper.
Published dependencies used in the proof must be proved or supplied by verified,
compatible Lean results, not left as uninstantiated fields or mathematical axioms.

## Mathematics

- Keep the three milestones in the coverage map separate. Do not represent a
  theorem relative to published inputs as a completed formalization of the
  actual Došen–Petrić presentation.
- Composition `Category.comp f g` applies `f` and then `g`; it corresponds to
  manuscript `g ∘ f` and Mathlib `f ≫ g`.
- Preserve empty hom-sets. Zero arrows require an existing-arrow witness.
  Do not add `HasZeroMorphisms` for the intended category.
- Keep uniform substitution on arrow terms and their types explicit. A kernel
  of one interpretation is not necessarily a substitution congruence.
- Repeated occurrences have different tags. Check empty occurrence sets and
  negative literals. Apply coherence only in the original category.
- No custom mathematical axioms, proof holes, `native_decide`, or assumptions
  that restate the conclusion in production proofs. Record published inputs as
  explicit data with typed laws, and record the unproved bridge in coverage.
- Before claiming milestone I, instantiate the complete interface in an
  intended nonthin model or establish the bridge to the intended category.

## Implementation and verification

Use the pinned stable Lean toolchain. Initial modules use only `Init`; add
Mathlib when its API is needed, at the recorded full compatible commit. Do not
import Foundation because the predecessor used it. Commit the generated Lake
manifest when adding dependencies. Do not reuse compiled artifacts across
toolchains or projects.

Use `module` in regular Lean files and keep every source below 10,000 physical
lines. Run `bash scripts/verify.sh`, with one build or kernel replay at a time.
Keep logs in `.codex-work/`; preserve command exit codes. `LEAN_NUM_THREADS=1`
limits concurrency, not total RAM. Inspect WSL memory and swap before large
Comparator jobs; do not copy the predecessor's machine-specific cgroup values.

At each mathematical milestone, apply the hostile-referee and mathematical-
writing reviews to the actual argument and correspondence map. Keep process
reports outside mathematical prose. Never report an unavailable review as done.

## Reports and delivery

Retain required repository copies of reports under `docs/` and review reports
under `docs/reviews/`. After finalizing a report, copy it to
`/mnt/c/Users/fleng/Downloads` in WSL2. This delivery step is part of task
completion for every report, including mathematical and writing reviews.

Verify that each Downloads copy matches the repository copy byte for byte or
by SHA-256. If a destination filename already contains different material,
preserve it and use a dated or commit-suffixed filename for the new report;
do not silently skip delivery or overwrite an unrelated file.

The final response must identify the delivered Downloads paths and the retained
repository paths. Report any copy or verification failure explicitly.

## Git and publication

The initial private repository and bootstrap commits are authorized. Respect
later task-specific branch/commit/push scope. Keep this repository private unless
publication is explicitly authorized. Do not submit to Palomar or arXiv, contact
authors, choose a distribution license, or change repository visibility as part
of an ordinary proof task.

Before a future Palomar submission, recheck the official verifier, policy, and
service instructions. Require independent Challenge/Solution builds, exact
statement and shared-definition correspondence, complete proof-dependency and
source-closure audits, focused negative controls, and immutable-source evidence.
Keep local build, Comparator, official preflight, service verification, automated
review, and publication as separate statuses.

