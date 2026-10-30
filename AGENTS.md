# Project instructions

## Division of work

ChatGPT research/review sessions prepare Codex instructions, check and referee
Codex's work, investigate the mathematics and literature, check the manuscript,
and assist with arXiv and Palomar preparation. Local WSL Codex implements and
builds the Lean source. This division, clarified by the author on 25 October
2026, does not alter the full-paper endpoint or the local verification duties
below. The concrete W6 construction is in `docs/CODEX_W6_CONSTRUCTION.md`;
its proposed equalities and ranks remain implementation targets until checked.

Before issuing a successor implementation handoff, ChatGPT must wait for the
active local Codex run to finish and review its resulting source and evidence.
Then reconcile the instructions with what that run actually proved. This is
a sequencing requirement for the reviewer, not a stop or approval condition
for local Codex. Current compiled scope is recorded in the latest continuation
and claim maps; historical construction instructions do not reset that scope.

## Local implementation

Work in `/home/flengyel/src/Dosen-Petric-Maximality` under WSL2. Inspect Git
status and the current task before editing. Preserve unrelated work and all
other checkouts, including FailureOfComposition and Categorical_Rice_Shapiro.

Read `docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md`,
`docs/CODEX_NEXT_SESSION.txt`, `docs/MANUSCRIPT_STATEMENTS.md`,
`docs/MANUSCRIPT_COVERAGE.md`, and
`docs/PALOMAR_REQUIREMENTS.md`. The current manuscript in `manuscript/` is v8;
v4, v5, v6 and v7 remain preserved. V8 updates only the formalization status,
date and immutable proof-source citation; the full mathematical contract is
all v7 content unchanged. Preserve the text, diagrams, and Appendix A references
unless revision is requested. On 28 October 2026 the author requested that the
two verified source errata appear in the arXiv paper. The exact Appendix C
addition has been built and inspected in v7, preserving v6; its source and PDF
anchors and remaining Lean correspondences are recorded in the active maps.

## Full-paper objective

Formalize the complete mathematical content of manuscript v7 (all v6 content
and the authorized Appendix C addition): the short q_A/e_A
proof, maximality for the actual equation-generated presentation with every
required input proved, the model corollary, all unnumbered mathematical claims,
and all three appendices' constructions, equations, examples and diagram identities.
Maintain exact claim-to-declaration correspondence. Preserve the existing
symmetric-fold proof as an alternative route.

`docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md` governs this overall endpoint;
`docs/CODEX_NEXT_SESSION.txt` records the completed endpoint and preservation
requirements after 811eceeb integration. The active complete ledger is
`docs/MANUSCRIPT_COMPLETE_CLAIM_MAP.md`.
The concrete successor is `docs/CODEX_AFTER_77199AC_LOGICAL_BINARY_CUTS.txt`;
read its two 77199AC reviews and the current completed binary report/reviews.
All twelve mix/conjR/disjL branches have actual native/selected equations and
instantiated original-rank steps. BlockedL.gammaMix, BlockedR.gammaMix,
BlockedL.gammaConj, BlockedR.gammaDisj, BlockedL.gammaDisj and BlockedR.gammaConj
are complete through
actual source equations and rank steps. Appendix C p.260 is matched by both
original-child strict inequalities and the actual gammaDisj source equation.
BlockedL.conjunction and BlockedR.disjunction also have their actual sequential
source equations and original-rank steps. BlockedL.disjunctionFirst also has its
actual sequential source/rank proof, closing the concrete Appendix C p.262 row
with fresh right-premise rho.left=1 and total h.rho.right+1≥2. BlockedL.disjunctionSecond
also has its actual source/rank construction. BlockedL.disjunctionBoth now has
the actual left3 source equation, both original descents and three instantiated
rank calls. Every BlockedL family is complete. BlockedR.conjunctionFirst now has its actual
source equation and both instantiated original-rank calls. BlockedR.conjunctionSecond
now has the same complete original-source/rank contract. BlockedR.conjunctionBoth
now has its actual right3 source equation, both original descents and three
instantiated rank calls. All fourteen blocked families are complete. Exhaustive constructor/tag dispatch,
original-rank induction, strong degree induction and arbitrary-G normalization
now prove actual CutElimination P and AtomizedCutElimination P inhabitants.
Actual PositiveCoherence, Reduced faithfulness and Boolean coherence now
instantiate Presentation.interpretation P with signed labels in the intended
category. Actual full proof-congruence correspondence, substitution closure,
both actual
maximality routes, original isolation, complete whole-arrow block/label squares,
negation/substitution compatibility, Appendix B, categorical consequences and
exact symmetric-fold correspondence are now proved. Full-source model
interpretations, substitution composition, universal agreement and the model
corollary are now proved and instantiated. General substitution-action transports,
all Appendix A profile/ordinal/renaming/example/skeleton claims, every unnumbered
mathematical assertion and the final manuscript scope/citation refresh are now
proved and locally verified. The full-paper mathematical endpoint is complete;
local Comparator and independent kernel verification of the selected Palomar
family are now complete. The author has approved Apache-2.0 public release,
including the original manuscript and retained history, and the repository is
public. Official preflight and service/registration remain separate stages. Preserve both proof routes and every
completed result. Reuse all
completed binary, unary, structural,
principal, cleaning and descent results. Retain earlier source/rank/atomization decisions.
The existing three milestones remain distinct;
even actual-presentation maximality alone does not certify the entire paper.
Published dependencies used in the proof must be proved or supplied by verified,
compatible Lean results, not left as uninstantiated fields or mathematical axioms.

Any necessary mathematical, correspondence, citation or prose correction
established during the work is part of the task. Maintain
`docs/MANUSCRIPT_CORRECTIONS.md` and verify repairs before
closing affected claims. Preserve the tagged-block and typed-diagram account
of occurrence substitution and prove its exact ordinal-coordinate correspondence;
it is required content, not optional formatting.

Carry accepted corrections across sessions. Apply each correction to every
affected passage, declaration, diagram and linked record in one pass, search
for parallel occurrences, and verify the full affected scope before reporting
completion. Record the decision and its resolution outside the manuscript so
the author need not repeat it. Treat later user messages as steering the active
task unless they explicitly replace it.

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

## Palomar registration phase — 30 October 2026

The author has requested the work needed for Palomar registration. Read
`docs/CODEX_PALOMAR_REGISTRATION.txt` and `docs/PALOMAR_REGISTRATION_STATUS.md`.
The full-paper mathematical endpoint remains complete. The independent
Challenge/Solution package, correspondence, local kernel verification and
metadata are complete and merged into main. The author explicitly approved
Apache-2.0 publication of the repository, original manuscript and retained history;
the repository is now public. Verified submission source: 2e771844077fd8cebfbe365230f13d4dd13a75b1.
Keep Lean at 4.35.0 and reuse the completed local verification. Official full
preflight passed at https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41129351329.

Preserve the verified source commit; later reports/evidence do not replace it.
The author approved the exact service intake. Submission `wy75d6nipd4e` passed service
verification at https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41137470993. Final registration requires the author to see and approve the actual
service review and digest. Do not automate browser sign-in or treat release
approval as consent to an unseen review.

The author clarified the publication order: Palomar Registry registration first,
then arXiv submission, then work on Local connectedness in recursion categories
and essential incompleteness. Do not submit to arXiv before Palomar registration.
Do not reopen the completed proof-development or local packaging sequence.
