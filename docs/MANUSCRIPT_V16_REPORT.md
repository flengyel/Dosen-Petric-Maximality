# Manuscript v16: mathematical exposition from the Lean proof

1 November 2026. Input: v15 and the accepted reverse audit at
216bca6e7765eae7a494b712facde55f8311e7cf. Output: v16, 23 pages.
The author approved all seven additions and requested footnotes locating their
proofs. The subsequent instruction explains their purpose: help mathematicians
unfamiliar with proof assistants translate between the paper and Lean, and use
the formal proof to improve the written argument.

The [PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v16.pdf),
[TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v16.tex) and
[four-file arXiv archive](../submission/arxiv-v16/Dosen-Petric-Maximality-v16-arxiv-source.tar.gz)
are prepared. No arXiv upload has occurred.

## Mathematical additions

| Accepted item | Printed content and location |
| --- | --- |
| R1: substituted occurrence relation | Section 3, pp.5–6: the relation on dependent blocks compares pairs in E_sigma; a typed square gives the whole relation of f[sigma]. The induction explains the composition step, repeated occurrences and empty blocks. |
| R2: explicit inverses | Appendix E.1–E.2, pp.20–21: structural terms for q_A inverse and e_A inverse, their occurrence graphs and all four inverse equations. The zero in the second construction has an explicit existing-arrow witness. Lemma 5.1's cited proof is preserved. |
| R3: union | Section 6, p.10: the arrow expression, relational union, associativity, commutativity, idempotence, composition laws, order and witnessed empty union. The footnote distinguishes the named Reduced laws from their transfer to B(P). |
| R4: substitution action | Section 3, p.6: identity, composition and extensionality, including identification of both arrow endpoints by the formula equalities. |
| R5: retract transport | Section 4, p.7: for i:A→B and r:B→A with r∘i=1_A, the equation K_B modulo a proof congruence gives K_A. The transported composite and zero absorption are displayed. |
| R6: signs and negation | Section 3, pp.4–5: signed labels at arbitrary formulas and the converse relation of negation, with proofs by term induction and normalization transport. |
| R7: coherence | Appendix D.5, pp.18–20, and E.3, pp.21–22: direct union equations, split comparison arrows, normal-form retracts, finite-union positive forms, positive coherence, common atomic factorization and transfer to the original category. |

The coherence account needs the union equations before faithfulness. It gives
their source-equation derivations separately from Section 6's shorter proof by
faithfulness. The normal-form expansions satisfy one retraction equation;
they are not asserted to be distributivity isomorphisms. Appendix E.3 gives
explicit structural terms for both split comparisons and the component
equations proving their splitting. It does not use the quotient negation
functor, whose equality-respect proof already depends on coherence.

The extra deductions recorded in the reverse audit—constant substitutions
suffice, empty-P thinness and finite hom-set bounds—are not added to v16 or
represented as newly selected declarations. No new source erratum or missing
Lean proof was established. The additions expand the mathematical exposition
of existing proofs.

## Translating the paper and Lean

Appendix D.2, pp.16–17, explains types, propositions and proofs; indexed arrow
terms and quotient arrows; implicit arguments; nonempty variable types;
namespace and field notation; and the conclusion of a theorem declaration.
It prints the selected maximality statement, explains each binder, and expands
R.Total into its universal quantifiers. The statement matches the registered
type after expanding Not notation and ignoring whitespace.

A table then follows the short proof through raw inequality, literal isolation,
all K_A and the q_A/e_A collapse. The accompanying text explains R.fragment,
interpretation, normalization, substitution and double negation as the
mathematical structures used in those steps. It also explains intro, obtain,
rw and exact, the proof term they construct and the kernel's type check.
The composition convention is explicit: Term.comp f g denotes [g]∘[f].
The official Lean manual is cited for general syntax.

There are 17 footnotes and 49 distinct clickable declaration references.
Each source path, line and declaration opening was checked against the
immutable version-1 source
2e771844077fd8cebfbe365230f13d4dd13a75b1, matching the supplied bibliography.
All 49 URLs occur in the PDF's link annotations. These links locate source
declarations; they do not mean that 49 statements were separately selected
for Palomar registration. The five selected statements are unchanged.

## Review, preservation and verification

The [hostile review](reviews/V16_HOSTILE_REVIEW_2026-11-01.md) and
[mathematical-writing review](reviews/V16_WRITING_REVIEW_2026-11-01.md) are
author-side AI-assisted reviews of the added argument and its correspondence,
with a continuous source reading and preservation checks on the preceding
paper. They are not independent peer review or a new audit of every Lean
proof body. Knuth, Larrabee and Roberts's Mathematical Writing governs the
prose review; Došen and Petrić provide the author's model for exposition.

Removing the 13 recorded additions and restoring the version/bibliography
suffixes recovers v15 byte for byte. All seven numbered statement bodies,
twelve numbered displays, eleven prior diagrams and 31 prior labels remain.
The totals are thirteen diagrams and 34 labels. Appendices A–C, both proof
routes, all thirteen bibliography entries, the exact supplied Palomar BibTeX,
MSC codes and authorized AI disclosure are preserved. All 97 preceding
manuscript/package files are byte-identical to the input commit.

The final manuscript passes and all three separately extracted archive passes
returned zero. The archive has exactly main.tex, main.bbl, references_v16.bib
and palomar_v16.bib. Its PDF layout text matches the manuscript. Final logs
contain no citation/reference, box or duplicate-destination warnings.
All 23 rendered pages were inspected on six contact sheets; pages 6, 16, 17,
19, 20, 21 and 22 were additionally inspected individually. No clipping or
overlapping text was found. The retained stash is unchanged.

The 857 production proof/input blob identities match the registered version-2
source 5dbee39bea09539bd130f729e82636419f71f920. Lean source, frozen inputs and
verification scripts have no changes. No Lean build, kernel replay, Palomar
intake, preflight, service verification or registration was repeated.
Credentials and unregistered reviews remain outside public Git.

Exact hashes, exits, source links, text preservation and review records are
under [release provenance](../provenance/manuscript-v16-review-20261101/validation.json).
The active claim map, correction ledger, continuation, preparation report and
README are updated together. The preceding preparation report is retained at
[the v15 checkpoint](history/ARXIV_PREPARATION_V15_2026-11-01.md).

## Delivery

Release files and every report/review are copied from committed bytes to
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v16-20261101/`.
The [delivery receipt](../provenance/manuscript-v16-review-20261101/delivery-receipt.json)
records the source commit, exact destination paths and byte/SHA-256 checks.
Differing earlier copies are preserved. Completed main and its receipt commit
are pushed and the remote ref verified before readiness is reported.
