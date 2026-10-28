# Došen–Petrić maximality in Lean

Both full Gentzen Reducibility theorems now compile for the existing syntactic
Reduced presentation, with every addressed rebuilt eligible descendant covered.
Terminal-source W6, unrestricted same-side exchange, and all remaining unary
inputs are implemented. Typed outside-site replacement transport also compiles.
The next result is containing-blocked preservation, followed by full finite-site
multiset descent and Blocked-w. Cut elimination, coherence and the full-paper
endpoint remain open.

The [reviewed successor instruction](docs/CODEX_AFTER_5B8A199_BLOCKED_W.txt)
specifies the containing-blockedness theorems, complete eligible-site
correspondence, multiset descent and Blocked-w. Its
[source/evidence review](docs/reviews/GENTZEN_5B8A199_REVIEW.md) and
[writing review](docs/reviews/GENTZEN_5B8A199_WRITING.md) introduce no new
Lean result or manuscript revision.

The maintained [validation record](docs/VALIDATION.md) reports **398 screened
Lean files and 10,606 audited project declarations**, including generated
helpers. The [checkpoint report](docs/GENTZEN_FULL_REDUCIBILITY_REPORT.md),
[author-side hostile review](docs/reviews/GENTZEN_FULL_REDUCIBILITY_HOSTILE.md),
[writing review](docs/reviews/GENTZEN_FULL_REDUCIBILITY_WRITING.md),
[correspondence](docs/PRESENTATION_CORRESPONDENCE.md) and
[continuation](docs/CODEX_NEXT_SESSION.txt) give exact hypotheses and remaining
obligations. Historical reports remain available; the preceding README and its
full checkpoint/link history are preserved in
[README_434AA77.md](docs/history/README_434AA77.md).

## Full-paper formalization target

The authorized target is the complete mathematical content of manuscript v6:
the short q_A/e_A proof, maximality for the actual equation-generated category
with all inputs proved, the model corollary, unnumbered claims and both
appendices. Full local Reducibility is one prerequisite. Keep the three
milestones below separate and preserve the existing symmetric-fold alternative.
See the [full-paper contract](docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md),
[statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[correction record](docs/MANUSCRIPT_CORRECTIONS.md). Tagged substitution and its
ordinal-coordinate correspondence remain required content. No manuscript
revision or new publication claim is implied by this checkpoint.

## WSL2 setup

The intended directory is `/home/flengyel/src/Dosen-Petric-Maximality`, on the
WSL2 Linux filesystem. With GitHub SSH authentication configured and Elan installed:

```bash
mkdir -p /home/flengyel/src
git clone git@github.com:flengyel/Dosen-Petric-Maximality.git /home/flengyel/src/Dosen-Petric-Maximality
cd /home/flengyel/src/Dosen-Petric-Maximality
bash scripts/setup-wsl.sh
```

If that directory already exists, inspect its Git status and origin before
updating it. See [WSL2 instructions](docs/WSL2_SETUP.md) for prerequisites.
The setup installs only the pinned project toolchain and runs verification;
it does not change Elan's global default. Local build and audit outcomes are recorded in validation.

Initial modules use Lean core only. The matching Mathlib release is recorded
at full commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; it is not an active
dependency. The committed Lake manifest therefore has no dependency packages.

## Proof scope and continuation

1. Contextual collapse relative to explicit structural and faithful-interpretation data.
2. Maximality relative to explicit coherence, normalization, presentation, and substitution inputs.
3. Maximality for the actual Došen–Petrić presentation after those inputs are established.

The conditional theorems do not complete the intended-presentation milestone
gates. Many syntactic bridges above are constructed, while coherence and
remaining congruence/substitution interfaces are still required. Coherence
applies in the original category; zero arrows require a witness that the
hom-set is inhabited.
The [statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[coverage map](docs/MANUSCRIPT_COVERAGE.md) record the precise boundary.
Use [the next-session prompt](docs/CODEX_NEXT_SESSION.txt) to continue in WSL2.

The current manuscript is v6: [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v6.pdf).
It gives a shorter contextual-collapse proof from the published structural
isomorphisms, distinguishes the result from Joyal's theorem, and describes the
conditional Lean formalization. No earlier explicit statement of the same
maximality theorem was found; derivability from older results does not establish
prior publication. The v6 manuscript is unchanged; the Lean proof work is recorded above and its coherence obligations remain open.
See the [corrected novelty review](docs/DOSEN_PETRIC_MAXIMALITY_NOVELTY_REVIEW_2026-10-25.md),
[v6 hostile review](docs/reviews/V6_HOSTILE_REVIEW.md),
[writing review](docs/reviews/V6_WRITING_REVIEW.md),
[Lean scope check](docs/reviews/V6_LEAN_SCOPE.md), and
[validation](docs/V6_VALIDATION.md).
MSC2020: primary 03G30; secondary 03F07 and 18A32.
The v4 [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.pdf)
remain preserved, as do the v5
[TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex) and
[PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.pdf).
[SHA-256 checksums](manuscript/SHA256SUMS) cover all three versions.
The [v5 literature review](docs/LITERATURE_REVIEW_V5_2026-10-23.md),
[manuscript hostile review](docs/reviews/V5_HOSTILE_REVIEW.md),
[writing review](docs/reviews/V5_WRITING_REVIEW.md), and
[manuscript validation](docs/V5_VALIDATION.md) accompany v5.
The [earlier literature comparison](docs/LITERATURE_REVIEW.md) remains available.
The literature searches are bounded and make no exhaustive priority claim.
The current [author-side hostile review](docs/reviews/GENTZEN_FULL_REDUCIBILITY_HOSTILE.md)
and [mathematical-writing review](docs/reviews/GENTZEN_FULL_REDUCIBILITY_WRITING.md)
cover both full local Reducibility statements and outside transport; they are
not independent certification. See the [current report](docs/GENTZEN_FULL_REDUCIBILITY_REPORT.md),
[governing full-target instructions](docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
[current continuation](docs/CODEX_NEXT_SESSION.txt),
[historical classification report and case ledger](docs/GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md),
[superseded mixed-W5-only continuation](docs/CODEX_GENTZEN_MIXED_W5_DISPATCH.txt),
[preceding integration report](docs/GENTZEN_PROOF_REPLACEMENT_REPORT.md),
[preceding W5 report and track/drift audit](docs/GENTZEN_W5_OTHER_PREMISE_MIX_REPORT.md),
[preceding W5 report](docs/GENTZEN_W5_SINGLE_PREMISE_MIX_REPORT.md),
[preceding W4 report](docs/GENTZEN_W4_SELECTED_LOGICAL_REPORT.md),
[preceding W2 report](docs/GENTZEN_W2_SELECTED_THINNING_REPORT.md),
[preceding W3 report](docs/GENTZEN_W3_SHARED_SELECTED_CONTRACTION_REPORT.md),
[preceding terminal-tail report](docs/GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_REPORT.md),
[preceding disjoint-contraction report](docs/GENTZEN_W1_DISJOINT_CONTRACTION_REPORT.md),
[preceding same-side logical report](docs/GENTZEN_W1_SAME_SIDE_LOGICAL_REPORT.md),
[preceding same-side exchange report](docs/GENTZEN_W1_SAME_SIDE_EXCHANGE_REPORT.md),
[preceding same-side thinning report](docs/GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md),
[preceding logical report](docs/GENTZEN_W1_LOGICAL_REPORT.md),
[preceding contraction report](docs/GENTZEN_W1_CONTRACTION_REPORT.md),
[contraction review](docs/reviews/GENTZEN_W1_CONTRACTION_HOSTILE.md),
[preceding exchange report](docs/GENTZEN_W1_EXCHANGE_REPORT.md),
[exchange review](docs/reviews/GENTZEN_W1_EXCHANGE_HOSTILE.md),
[preceding thinning review](docs/reviews/GENTZEN_W1_THINNING_HOSTILE.md),
[historical contextual-collapse review](docs/reviews/CONTEXTUAL_COLLAPSE_HOSTILE.md)
and [initial review](docs/REVIEW.md) remain available.

## Verification and Palomar

Run `bash scripts/verify.sh`. CI uses the hash-checked official Lean release,
a strict build, source screening, and transitive axiom collection. Evidence
and its limitations are in [validation](docs/VALIDATION.md).

The [Palomar requirements](docs/PALOMAR_REQUIREMENTS.md) adapt the
FailureOfComposition procedure to the current toolchain and kernel policy.
Upstream policy snapshots and exact commits are in `provenance/`.
`bash scripts/fetch-palomar.sh` fetches the pinned verifier source for inspection.
Comparator packaging, independent kernel replay, and registry verification
remain to be implemented for a substantive theorem.

The repository is private. Public release, license selection, and registry
submission are later decisions. No submission has been made.
