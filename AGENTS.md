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
`docs/PALOMAR_REQUIREMENTS.md`. The current manuscript in `manuscript/` is v21, dated November 2, 2026;
v4–v20 remain preserved. V8
updated the formalization status/date/source citation. V9 adds the author-requested
Codex disclosure, author-responsibility sentence and verified Palomar citation,
and updates the date. MSC 2020 Primary 03G30; Secondary 03F07, 18A32 is preserved.
The full mathematical contract is all v7 content unchanged. Preserve the text,
diagrams, and Appendix A references
unless revision is requested. On 28 October 2026 the author requested that the
two verified source errata appear in the arXiv paper. The exact Appendix C
addition has been built and inspected in v7, preserving v6; its source and PDF
anchors and remaining Lean correspondences are recorded in the active maps.

## Manuscript versioning — author instruction, 31 October 2026

Every manuscript revision must increment the version number. Never leave the
version number unchanged when releasing revised text. Preserve the preceding
source/PDF and upload package; put revised text in the next numbered files and
refresh the date, PDF metadata, package fields and active links together.
V10 contains the first 31 October terminology revision. V11 incorporates that
revision and the exact supplied Palomar BibTeX entry, explains terminology, and
removes empty qualifiers and progress narration. V12 incorporates the completed
line-by-line hostile/writing review and primary-source comparisons. It preserves
v11, all theorem statements, displayed equations, typed diagrams and the exact
supplied Palomar BibTeX. See docs/MANUSCRIPT_V12_REPORT.md.
V13 repeats the full mathematical/prose review and broadens the literature
search. It corrects the omitted negation-free hypothesis in the Lemma 6
comparison, adds the CCC and proof-net references and the zero-identity
distributive antecedents, and expands the existing symmetric-fold deduction.
The previous v12 review missed that citation qualification. The manuscript's
own signed-literal isolation and registered proof are unchanged. See
docs/MANUSCRIPT_V13_REPORT.md and its three review records.
V14 applies the author-requested hostile-reviewer and mathematical-writing
plugins to the complete preprint. It uses the source's dissociativity terminology,
literal and occurrence map; gives the operation/functor/witness types; and expands
the two computations through v_A and w_A in the alternative proof. The seven
mathematical statements retain their hypotheses and conclusions, with a literal
synonym and lemma-caption changes. Numbered displays, diagrams, labels and the
supplied Palomar BibTeX remain byte-identical. See docs/MANUSCRIPT_V14_REPORT.md
and its two review records. Carry these accepted repairs across future revisions.
V15 adds Appendix D with the exact mathematical statements of the five registered
Lean entry points, their assumptions, and the correspondence between relations
on terms and arrows. It defines the generated equality, gives the typed
substitution square, explains the derivation of negation preservation, and
identifies the existing coherence, model and expanded collapse proofs. All v14
text is preserved except the version/bibliography suffixes and a Section 6
pointer. See docs/MANUSCRIPT_V15_REPORT.md and its two review records.
V16 incorporates all seven accepted reverse-audit additions and explains how
to read the Lean statement and the steps of the short maximality proof.
The purpose is translation for mathematicians unfamiliar with proof assistants;
the formal proof supplies explicit terms and equations improving the paper.
Seventeen footnotes and the proof table link to 49 distinct declarations at
the cited version-1 source. Appendix D.5 explains coherence; Appendix E gives
the q/e inverses and split comparisons. The 23-page source/package builds
match, all v15 text is preserved apart from suffixes, and both frozen sources
remain. See docs/MANUSCRIPT_V16_REPORT.md and its two review records.
V17 puts the u_A path on one line and names Appendix E's two isomorphisms:
q_A and e_A. At the author's request, replace the adjective “structural” by
the specific maps, equations or construction meant. The seven visible uses
are replaced throughout; write “induction on the formula” when that is the
argument. Preserve unprinted reference keys and immutable Lean identifiers.
The author confirmed that Appendix A is required and must remain, with its
main-text references and exact tagged-occurrence/ordinal correspondence.
See docs/MANUSCRIPT_V17_REPORT.md and its focused writing review.
V18 revises only the abstract, apart from version/bibliography suffixes.
The author requested consultation of Knuth–Larrabee–Roberts about abstracts.
The official PDF supplies van Leunen's abstract exercise (§36, printed p.87)
and Wilf's guidance on stating the subject plainly (§27, p.59). The new
nine-sentence abstract gives context, the exact main result and significance,
a short proof outline, the model consequence and the formalization's scope.
All body text, Appendix A references and constructions, both proof routes,
the supplied bibliography and disclosure remain. All abstract representations
in the upload package are updated together. See docs/MANUSCRIPT_V18_REPORT.md
and its focused writing review. No arXiv upload has occurred.
V19 uses the exact version-2 Palomar BibTeX supplied by the author on
1 November. Current citations, the registered-source note, all 49 declaration
links and submission fields now agree on version 2, source
5dbee39bea09539bd130f729e82636419f71f920. Two declaration line targets changed.
This explicit author instruction supersedes the earlier current-v1 citation
preference; preserve earlier manuscripts and their supplied v1 entry.
V19 also reviews qualifiers throughout, removes redundant adjectives and
names the constructions meant. Omit “particular” from Appendix E's opening
and its Section 5 pointer; its heading already names q_A/e_A. Each D.5 c-arrow
definition and type fits on one line at the existing font size. Preserve
qualifications specifying quantifiers, types, signs, coordinates, naturality
or universal properties. See docs/MANUSCRIPT_V19_REPORT.md and its writing review.
V20 states the result as collapse to a preorder after adding any equation
between parallel arrows that does not follow from the defining equations,
with closure under arrow operations and uniform formula substitution. State
this universal condition directly; “a proper extension” alone hides it.
Section 2 explains the quotient, thinness/totality equivalence and the name
maximality. Theorem 2.1 has the equivalent quotient conclusion; its proof,
the model proof and Appendix D.4 use that conclusion. Preserve the quantifier,
nonempty-variable hypothesis and both closure conditions. See
docs/MANUSCRIPT_V20_REPORT.md and its focused writing review.
V21 restores the earlier result-first abstract and states the disproved
Došen–Petrić conjecture explicitly: this category is not maximal. The descriptive
collapse result remains. The author removed the categorical-proof-theory opening and
the redundant sentence explaining preorder as equality of parallel arrows,
from both abstract and introduction. The model-corollary summary also says
simply “is a preorder”. Restore the earlier result-first opening “We prove that ... is maximal”,
replacing “We study ...”, as the author subsequently requested. Do not restore
elementary paraphrases or replace the conjecture by a pointer to the book. The precise citation remains in
the introduction. See docs/MANUSCRIPT_V21_REPORT.md and its writing review.
The author requests that manuscript prose avoid empty qualifiers, unexplained
terms and process updates. Keep mathematically meaningful qualifications, such
as induction on a specified formula or arrow term; keep process reports outside
the manuscript. Follow Došen and Petrić's direct manner of exposition: define
the objects, state the equations and hypotheses, and give the deductions.
Replace vague English by a mathematical assertion or delete it. Apply corrections
throughout affected passages and linked records.
The original v9 source/PDF/package are restored from 678ea6d; the briefly reused
v9 editorial snapshot remains in Git history at fd29c0c. All mathematical claims,
both proof routes and the immutable registered proof source are preserved.

## Reverse content audit — 1 November 2026

The author requested a Lean-to-paper audit after v15. Read
`docs/FORMALIZATION_TO_MANUSCRIPT_AUDIT_2026-11-01.md` and its two reverse-audit reviews.
It identified seven candidate additions. The author accepted all seven and
requested footnotes and a reader's guide. They are incorporated in v16;
v15 and its package remain preserved.
Do not describe omitted written results as missing Lean proofs. Distinguish
named source statements, transfer from Reduced through recovery, and further
mathematical deductions. DNF/CNF expansions are retracts, not distributivity
isomorphisms. The union theorem is named in Reduced, not Presentation.
The accepted additions are resolved in docs/MANUSCRIPT_CORRECTIONS.md and mapped
in docs/MANUSCRIPT_COMPLETE_CLAIM_MAP.md. Any further text revision must be v22
or later. Preserve the fixed source links and explain their mathematical role.
The audit does not reopen the completed mathematical contract or frozen inputs.

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

Synchronization rule clarified by the author on 1 November 2026: within the
authorized branch and push scope, push completed public work before reporting
it ready or delivered. Do not silently choose local-only completion. Honor an
explicit local-only instruction, and report a failed or unavailable push as
unsynchronized. Preserve unrelated work and keep private staging excluded.
Before a future Palomar intake or registration, verify that the exact submitted
commit and intended input paths are available from the public remote, and that
completed relevant work on main is synchronized. Compare local and remote tips;
do not change a frozen submission merely to make it equal a later documentation
tip. Verify the push by reading the remote ref before closing the task.

Distinguish omitted written deductions from missing Lean proofs when reporting
review findings. Name a missing theorem or declaration before claiming a formal
gap. The five Palomar selections are entry points, not the extent of the full
Lean development. The v14 expansions already occur in the registered source:
ContextualCollapse.second_block, terminal_retraction, fold_top and
equal_projections. Their exposition repairs do not establish a missing Lean proof.

Before a future Palomar submission, recheck the official verifier, policy, and
service instructions. Require independent Challenge/Solution builds, exact
statement and shared-definition correspondence, complete proof-dependency and
source-closure audits, focused negative controls, and immutable-source evidence.
Keep local build, Comparator, official preflight, service verification, automated
review, and publication as separate statuses.

## Publication phase — 1 November 2026

Palomar registration is complete: PALOMAR-2026-10-30-000014, version 2.
https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000014&version=2
The exact version-2 source is 5dbee39bea09539bd130f729e82636419f71f920, root
comparator.json, Lean 4.35.0. Submission txdu0y3got1o is registered. The author
separately authorized the exact delivered review after seeing its digest and
publication explanation; the agent's digest-bound request was accepted, and
authenticated service and public readback confirm completion. Version 1 and its
source 2e771844077fd8cebfbe365230f13d4dd13a75b1 remain preserved. Both versions'
full preflight and service verification passed. Do not repeat intake,
registration or successful verification. The publication monitor has completed.

Read docs/CODEX_NEXT_SESSION.txt, docs/PALOMAR_V2_REGISTRATION_REPORT.md and
docs/ARXIV_PREPARATION_REPORT.md. V21 and its four-file arXiv source package are
prepared and locally compiled; every earlier release is preserved. No arXiv upload has occurred. Keep mathematical
proof development closed, retain all previous manuscripts and the stash, and
reuse verification. Do not change the immutable registered source or its frozen
submission inputs when refreshing documentation.

Version-2 public evidence hashes, all 13 served render files, the rendered opening
and statement correspondence, and the native source tag were verified. The
version-1 diagnostic about two served HTML pages with added Cloudflare analytics
remains historical evidence about version 1; retain it. No version-2 served-render
mismatch was found. The current v21 manuscript cites version 2 using the exact
entry subsequently supplied by the author. Keep citation, source links and
submission fields consistent. Both registrations and frozen sources remain;
the manuscript update does not repeat registration or successful checks.

Credentials, private API responses, the original author-facing review and consent
digest remain in ignored private staging and out of public Git. Only the publicly
registered archived review is retained in public provenance. Preserve differing
Downloads copies and deliver reports from committed bytes. Palomar registration
precedes arXiv submission; the later Local connectedness project follows arXiv.
