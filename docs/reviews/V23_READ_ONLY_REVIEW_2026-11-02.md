# (A) Kill-shots / hard blockers

**Review of Maximality of the Došen–Petrić Boolean Category, manuscript v23.**
Review date: 2 November 2026. Manuscript date: 2 November 2026. Length: 23 pages.
Reviewed repository snapshot: `e9ff41162e8520d1cc7784dfa570a485f90074f3`.
The v23 manuscript was introduced by
`fa02603cb5933bf52c1aed5691be56bf4451dadf`; the reviewed source and PDF are
byte-identical to those files in that commit.

- [Reviewed LaTeX](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.tex)
- [Reviewed PDF](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.pdf)
- LaTeX SHA-256: `b34afdb82b1f36731ef9c1d8cb6a369b07fc40a71e3189cf3c093677f3b303c2`
- PDF SHA-256: `732ce3d7886fc837b8297273ca1d33a50346ebc5b0e74a55d2b047cf52dce0c1`

**No fatal or major mathematical defect was established.** This is a review
of v23, including its revised introduction and expanded Appendix C. It does
not treat v22 as the current manuscript. Two minor exposition/navigation
issues remain in Appendix D.5; they are described in C and D below.

The review is an author-side AI-assisted audit using HostileRefereeGPT — Cat/Rec
and the mathematical-writing skill. It is not independent peer review.
Correctness, exposition, definitions, typing, correspondence with selected Lean
declarations, and the changed source comparisons were examined. No manuscript
change is made or authorized by this report.

# (B) Major weaknesses

None established. The following records the argument examined and the changes
verified; it is not a list of additional defects.

## Actual outline and dependencies

The existing organization works. No replacement outline is proposed.

| Part, in manuscript order | Mathematical function |
| --- | --- |
| Abstract | State maximality, collapse after an additional equation, the disproved conjecture, the proof method, the model corollary and the formalization. |
| §1 Introduction | State the problem and contribution, describe the proof, distinguish other Boolean categories, and locate the appendices. |
| §2 The Boolean proof category | Define formulas, arrow operations, zero identity, congruences and maximality; state Theorem 2.1. |
| §3 Occurrences and substitution | Define occurrence coordinates, state Boolean Coherence, explain signs and normalization, and construct uniform substitution on formulas and arrows. |
| §4 Isolating an occurrence | Isolate one pair in the difference of two occurrence relations and derive every equation K_A. |
| §5 Equality of the product projections | Identify the two isomorphisms, prove collapse, finish maximality, and prove the model corollary. |
| §6 A second proof and the Lean formalization | Give the symmetric-fold proof using mix, explain union, and identify the Lean correspondence. |
| A.1 Occurrence maps and their fibres | Construct occurrence blocks and the maps between them. |
| A.2 The finite-ordinal presentation | Prove the coordinate formula and compute an example. |
| A.3 Shared variables and the maximality argument | Prove compatibility with renaming and connect substitution to Proposition 4.2. |
| B Diagrams for three defining equations | Display and type the first-injection, zero-identity and zero-law equations. |
| C Corrections to the cut-elimination argument used in Boolean Coherence | Identify two published typographical errors and justify the strict rank decreases. |
| D.1 Arrow terms and equations | Relate terms, derivability, quotient arrows, substitution and term congruences. |
| D.2 Reading a Lean declaration | Translate types, hypotheses and proof steps into mathematical statements. |
| D.3 The five declarations | State the registered entry points in mathematical notation. |
| D.4 Congruences on terms and on arrows | Prove their correspondence and identify the model and contextual-collapse declarations. |
| D.5 The proof of coherence | Explain positive coherence, retractions, atomic factorization and passage to the original presentation. |
| E.1 The inverse of q_A | Construct the inverse arrow and verify its equations by occurrence relations and coherence. |
| E.2 The inverse of e_A | Construct the inverse arrow and verify its equations. |
| E.3 The split comparisons used in coherence | Construct the section and retraction and derive the split identities from presentation equations. |
| Use of AI tools; references | Give the authorized disclosure and identify the sources. |

The central question is whether adjoining any nonderivable parallel-arrow
equation, with closure under the specified operations and uniform substitution,
forces a preorder quotient. The first proof uses coherence, literal isolation,
substitution and double negation, followed by the q_A/e_A argument. The second
proof replaces the final isomorphism argument by the symmetric-fold calculation.

## Numbered results

| Claim | Hypotheses and deduction examined | Review result |
| --- | --- | --- |
| Theorem 2.1 | P is nonempty and a substitution congruence identifies distinct parallel arrows. Lemma 4.1 isolates a literal, Proposition 4.2 gives every K_A, and Lemma 5.2 makes the quotient a preorder. | No defect established. Maximality quantifies over every additional equation with these closure conditions. |
| Theorem 3.1, Boolean Coherence | Faithfulness of the occurrence functor is attributed to Došen–Petrić. | It is an input to the main paper proof; D.5 explains the formal development of that input. The paper does not infer coherence from maximality. |
| Lemma 4.1 | Distinct parallel arrows have different occurrence relations. Normalization preserves inequality. A differing pair joins equal literals, and the typed induction supplies selecting arrows. | No defect established, including repeated occurrence tags and negative literals. |
| Proposition 4.2 | A substitution congruence identifies distinct parallel arrows. Substitute A for a positive literal; for a negative literal substitute neg A and transport through double negation. | Both endpoint types and the zero equation are preserved. |
| Lemma 5.1 | Nonempty P supplies a variable. The cited isomorphism types and coherence identify the particular q_p and e_p; uniform substitution preserves their inverse equations. | No defect established. Appendix E supplies the inverse terms, including formulas with empty occurrence sets. |
| Lemma 5.2 | A proof congruence contains every K_A. In the quotient, q_A makes A vee top terminal; e_A then makes a product projection invertible. The diagonal gives equal projections, and pairing proves collapse. | Coherence is used in the original category, before passing to the quotient. No use of coherence in the quotient was found. |
| Corollary 5.3 | P is nonempty and the extra equation holds under every interpretation. Agreement under all interpretations is substitution closed by composition with substitution. | No defect established. A kernel of one fixed interpretation is not used as a substitute for that argument. |

The subsidiary equations and constructions were read, including substitution
identity and composition, retract transport of K_A, union and witnessed zeros,
the ordinal-coordinate calculation, term/arrow congruence correspondence, the
inverse paths and the split comparisons. The D.5/E.3 derivations use presentation
equations before faithfulness, avoiding a circular proof of coherence.

## V23 changes verified

The introduction states the conjecture and the result directly. Its proof
outline now includes uniform substitution and double-negation transport.
The detailed literature comparisons occur next to the constructions they
compare. The abstract's repeated “also” has been removed while preserving
the accepted sentence introducing the formalization. Section 6's title names
both its proof and the formalization. The empty-union sentence specifies a
nonempty hom-set. D.5 identifies the equations used in the union-zero law.

The expanded Appendix C was checked against the retained complete primary PDF
of Došen–Petrić, [Proof-Theoretical Coherence, September 2007 revision](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
Printed pp.249 and 253 define the one-sided ranks and lexicographic induction.
The actual reductions on printed pp.260 and 262 were inspected visually:

- At p.260, case (w gamma 3), the recursive cuts retain the left premise.
  Each new right cluster is properly contained in the original cluster.
  Hence R_f < R and R_g < R give L + R_f < L + R and L + R_g < L + R.
- At p.262, case (w vee 1), after eliminating the first cut the new right
  principal cluster has rank 1; the unchanged left premise has rank L.
  The new total rank is L + 1. Since the original contracted right cluster
  has R > 1, the stated inequality 2 <= L + 1 < L + R follows.

These are strict decreases at unchanged cut degree. The appendix corrects
the comparisons without altering the displayed reductions. The explanation
agrees with `BlockedLeftDisj.gamma_first_descent`,
`BlockedLeftDisj.gamma_second_descent`, the instantiated original-rank steps
in `CutCommutation.blockedL_gammaDisj_rank_step` and
`CutCommutation.blockedL_disjunctionFirst_rank_step`, and the fresh-right
rank calculations in `GentzenAppendixCFreshRight.lean`.
The three relevant rank files were compared byte for byte with registered
commit `5dbee39bea09539bd130f729e82636419f71f920` and match.

Independent source comparison also confirmed that all seven numbered
statement bodies, six proof environments, twelve numbered equations,
thirteen TikZ diagrams and 34 labels are identical between v22 and v23.
This is a preservation check, not a substitute for the mathematical review.

# (C) Minor issues

| Location | Issue | Basis | Recommended action |
| --- | --- | --- | --- |
| D.5, p.19 | The role of atomization is unexplained. | KLR §1, points 10–12, applied to the intended reader of the Lean guide. | Identify the representation and thinning transformations locally. |
| D.5, p.20 | “Recovery maps of Section 3” does not identify the maps. | The referenced section states the equivalence but does not use that name. | Refer directly to the equivalence and its occurrence interpretation. |

## C1. The role of atomization is not explained in the Lean guide

- **Anchor:** p.19, Appendix D.5, source lines 1581–1586:
  “Gentzenization, cut elimination and atomization express the given arrow
  as a finite union of these paths”.
- **Failure mode:** `ambiguous`; severity **minor**, compressed exposition.
- **Evidence:** `absence_in_text` and source inspection. The text states the
  combined consequence without explaining the three transformations.
  `Reduced.Gentzen.gentzenization` in `PositiveGentzenization.lean` represents
  a positive term by a Gentzen derivation. `Reduced.Gentzen.G.atomize` in
  `PositiveThinningAtomization.lean` replaces weakening on compound formulas
  by weakening on literals and constants and preserves denotation and
  cut-freeness. `Reduced.Gentzen.G.mix_normal_form` in
  `GentzenMixNormalForm.lean` gives the union of literal paths in the mix
  fragment. These names omit the namespace prefix `DosenPetric.`.
- **Why it matters:** a mathematician using D.5 to read the formalization
  must consult Lean to discover what “atomization” means here. This is a
  local omission in the translation guide, not a missing Lean theorem or
  an exhibited gap in maximality. The main proof cites published coherence.
- **Editorial rationale:** Knuth–Larrabee–Roberts,
  [Mathematical Writing, §1, points 10–12](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
  concerns connected explanation and what the reader knows at each stage.
  Applying that advice here does not require teaching elementary category
  theory or reproducing every cut-elimination case.
- **Suggested local replacement, not implemented:**
  “Represent the arrow by a Gentzen derivation, eliminate its cuts, and
  replace weakening on compound formulas by weakening on literals and
  constants. At these endpoints, the denotation of the resulting derivation
  is a finite union of the paths \(j_y\circ p_x\).”
  The existing sentence about an empty union can follow unchanged.

# (D) Cross-section consistency failures

## D1. “Recovery maps of Section 3” has an insufficiently identified referent

- **Anchor:** p.20, Appendix D.5, source lines 1625–1626:
  “The normalization and recovery maps of Section 3 then transfer
  faithfulness from R(P) to B(P).”
- **Failure mode:** `ambiguous`; severity **minor**.
- **Evidence:** `absence_in_text`. Section 3 defines the normalizing
  isomorphisms and states that the equivalence with the normal-form
  presentation preserves the occurrence interpretation. It does not name
  maps “recovery”. The named `Reduced.reduceHom` and `Reduced.recoverHom`
  occur in Section 6's footnote, source lines 887–890.
- **Impact:** the transfer has the needed mathematical basis, but the reader
  cannot immediately match the name used in D.5 to the cited passage.
  No false transfer or missing proof is established.
- **Suggested local replacement, not implemented:**
  “The equivalence of Section 3 preserves the occurrence interpretation
  and therefore transfers faithfulness from \(\mathcal R(P)\) to \(\mathrm B(P)\).”
  This is an editorial correction to the reference, not a new assertion.

## Definition order, notation and terminology

| Item | Locations and status |
| --- | --- |
| B(P), arrow operations and composition | Defined in §2. The convention that g composed with f applies f first agrees with the Lean explanation in D.1. |
| Proof congruence, substitution congruence, maximality | Defined before Theorem 2.1 and used with the same closure conditions thereafter. The abstract and introduction may preview them. |
| Occurrences, tags, signs and literals | Occurrence sets and tags begin §3; signs and literals are introduced before their proof use. Repeated occurrences remain distinct. |
| Substitution and Appendix A | §3 gives block substitution and refers to A.1/A.2; A.3 connects shared-variable substitution to Proposition 4.2. Appendix A has a stated use in the main argument. |
| Zeros and empty unions | Zero arrows require an existing-arrow witness; the empty union is restricted to a nonempty hom-set. No blanket inhabitation of hom-sets is asserted. |
| Normal forms and split comparisons | D.5 uses retractions; it does not claim distributivity is an isomorphism. E.3 proves the split identities from defining equations. |
| Terms, arrows and Lean types | D.1 distinguishes terms and quotient classes. D.2 explains the declaration syntax; the five registered selections are entry points, not the full scope of the development. |
| “genuine”, “actual”, “structural” | No such adjective remains in the mathematical prose. “structural” occurs only in internal LaTeX labels/references. There is no reason to rename those labels. |
| “natural”, “canonical”, “raw” | Naturality is a mathematical assertion about the named negation isomorphisms. The two comparison arrows called canonical are given by explicit formulas. “raw” occurs in the exact Lean identifier `raw_distinct_iff`, not as unexplained prose. |

No further cross-section failure was established. In particular, the review
found no drift in substitution hypotheses, the original-category application
of coherence, the distinction between a term and its class, or the model
corollary's quantification over all interpretations.

# (E) Acceptance conditions, non-negotiable

No unmet mathematical condition was established. The conditions examined
are present: substitution closure in maximality, coherence in the original
category, witnessed zeros, and agreement under all interpretations in the
model argument. Appendix C gives the required strict inequalities for the
two identified reductions.

C1 and D1 are local clarifications. Neither warrants withdrawing a theorem,
reconstructing the main proof or claiming that the registration omitted
necessary Lean results. No manuscript revision is made by this review.

# (F) Not checked / uncertainty log

The complete v23 LaTeX source and bibliography were read, together with the
v22-to-v23 diff. All 23 PDF pages were inspected on six contact sheets;
pp.15, 20 and 23 were also inspected individually. Appendix E's u_A path
fits on one line. The comparison-arrow displays in D.5 fit within the margins.
The bibliography's pinned Notation URL wraps within the margins.

The governing mathematical-writing source was consulted from the retained
copy of Knuth–Larrabee–Roberts, including §1's discussion of connected
explanation, reader expectations and notation. C1 applies that advice; D1
is an independent local reference diagnosis. The report format is not
attributed to that book.

Fresh primary-source checking concentrated on the expanded Appendix C:
printed pp.249, 253, 260 and 262 of the September 2007 revised
Proof-Theoretical Coherence. These are PDF pages 261, 265, 272 and 274.
The web screenshot interface did not render that PDF; the retained complete
primary PDF was rendered locally and the four pages were inspected instead.
No source-access gap remains for those comparisons.

Selected Lean inspection covered the two rank reductions and fresh-right
ranks listed in B, the positive Gentzenization and thinning-atomization
declarations, and the mix normal-form argument used to assess C1. This is
not a new audit of every transitive proof dependency. The manuscript's
registered proof source is `5dbee39bea09539bd130f729e82636419f71f920`,
distinct from the manuscript snapshot identified in A.

Existing v23 release evidence records successful source/archive compilation,
matching text and coordinates, and one underfull bibliography paragraph.
Those checks were reused, not rerun. The present review performed no Lean
build, kernel replay, Comparator run, Palomar check or registration, or arXiv
upload. It did not independently reconstruct every cut-elimination reduction
or conduct an exhaustive new literature/priority search.

One harmless provenance qualification: the v23 implementation report and
validation flag describe the supplied Palomar BibTeX as byte-identical.
The entry fields are unchanged, but `palomar_v23.bib` has one additional
trailing newline: 298 bytes versus v22's 297. The whole files are therefore
not byte-identical. This affects neither the citation nor the mathematics;
it is not counted as a manuscript defect.

Only this report and its delivery receipt are to be added for this review.
The manuscript, PDF, upload package, Lean files, frozen registration inputs
and earlier releases remain unchanged. No v24 is created.

Retained report: `docs/reviews/V23_READ_ONLY_REVIEW_2026-11-02.md`.
Delivery target:
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-V23-Review-20261102/V23_READ_ONLY_REVIEW_2026-11-02.md`.
Delivery uses committed bytes and byte/SHA-256 verification, with a separate
receipt. Any conflicting existing Downloads file is preserved.

Strongest confirmed blocker: **none established**.
Strongest suspected unconfirmed blocker: **none supported by evidence**.
Most important unchecked item: independent reconstruction of the entire
cut-elimination dependency. No unavailable material is treated as verified.
Final formal referee recommendation: **unknown**; this author-side audit
does not supply an independent journal decision.
