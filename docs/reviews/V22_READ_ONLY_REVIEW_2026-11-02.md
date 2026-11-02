# (A) Kill-shots / hard blockers

**Review of Maximality of the Došen–Petrić Boolean Category, manuscript v22.**
Review date: 2 November 2026. Manuscript date: 2 November 2026. Length: 23 pages.
Reviewed repository snapshot: `5b515365f5d5164ba65c91ab3571fd2f475a0b66`.
The v22 release itself was introduced by `61ac9e08623b7c46db4e761c07e33ec436eccf41`;
the subsequent receipt commit did not change the manuscript.

While this report was being delivered, a fetch revealed remote commit
`fa02603`, which introduces manuscript v23. **This report reviews v22 only;
it is not a review of v23.** The version, snapshot and hashes above fix its scope.

- [Reviewed LaTeX](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v22.tex)
- [Reviewed PDF](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v22.pdf)
- LaTeX SHA-256: `14c2514bce1665feacc846a4127862f196b9e32374367c02585d4c281b901ffb`
- PDF SHA-256: `42eeddd5d3c447d15ccb0d5ea5b8b78a92785b0f9495c3f1ba5f71cfd5594433`

This records the read-only review requested after v22 was delivered. It is
distinct from the earlier [focused v22 writing review](V22_WRITING_REVIEW_2026-11-02.md),
which accompanied the abstract revision. This report does not revise the
manuscript, create v23, or implement any recommendation below.

The review is an author-side AI-assisted audit using HostileRefereeGPT — Cat/Rec
and the mathematical-writing skill. It is not independent peer review. The
axes examined were correctness, exposition, self-containedness, correspondence
with the formalization, and selected source comparisons.

**No fatal or major mathematical defect was established.** The written
argument proves maximality and the model corollary; neither proof is deferred
to Lean. The abstract now states the conjecture and introduces the formalization
as a formalization of the written proofs and their dependencies. The conjecture
agrees with Došen–Petrić, [Proof-Theoretical Coherence, September 2007 revision,
§14.2, printed p.322](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf#page=334).

# (B) Major weaknesses

None established in the inspected argument. The following records what was
examined; it is not a list of additional defects.

## Actual outline and mathematical dependencies

The existing order is appropriate. No replacement outline is proposed.

| Part | Function |
| --- | --- |
| Abstract | State maximality, descriptive collapse, the disproved conjecture, proof method, model corollary and formalization scope. |
| §1 Introduction | Identify the problem, compare related results and describe the proof and appendices. |
| §2 The Boolean proof category | Fix formulas, arrow types and operations, zeros, congruences and the main theorem. |
| §3 Occurrences and substitution | Give occurrence coordinates, coherence, signs, normalization and substitution on formulas and arrows. |
| §4 Isolating an occurrence | Select a differing pair, construct the isolation arrows and derive every equation K_A by substitution. |
| §5 Equality of the product projections | Identify q_A and e_A, prove collapse, finish the main theorem and prove the model corollary. |
| §6 Lean formalization | Relate the presentation to Lean and give the symmetric-fold proof and union laws. |
| A.1–A.3 | Give occurrence maps and fibres, ordinal coordinates and shared-variable substitution. |
| B | Display three defining equations as typed diagrams. |
| C | State two corrections to the cited cut-elimination proof. |
| D.1–D.5 | Explain terms and equations, reading a Lean declaration, the five registered statements, term/arrow congruences and the coherence proof. |
| E.1–E.3 | Construct q/e inverses and the split comparisons used in coherence. |
| Disclosure and references | Record the authorized AI disclosure and identify sources. |

The central question is whether adding any nonderivable parallel-arrow
equation, with the stated closure conditions, forces a preorder quotient.
The proof uses Boolean Coherence, literal isolation, uniform substitution,
double negation and the two isomorphisms. The model corollary uses agreement
under every interpretation, rather than the kernel of one fixed interpretation.

## Numbered claims examined

| Claim | Hypotheses and deduction checked | Result of review |
| --- | --- | --- |
| Theorem 2.1 | P is nonempty; a substitution congruence identifies distinct parallel arrows. Lemma 4.1 isolates a literal, Proposition 4.2 supplies every K_A, and Lemma 5.2 gives a preorder quotient. | No defect established. The quantifier concerns every such congruence. |
| Theorem 3.1, Boolean Coherence | Faithfulness of G is attributed to the published theorem, not inferred from maximality. D.5 explains the formal proof's architecture. | Attribution agrees with §14.2, printed p.321 of the cited book. No new independent reconstruction of the entire coherence proof was performed. |
| Lemma 4.1 | Distinct parallel arrows have different occurrence relations. Normalization preserves inequality; a pair in the difference has one literal at both endpoints. The displayed induction constructs the selecting arrows with the required types. | No defect established, including the negative-literal case and repeated occurrence tags. |
| Proposition 4.2 | The relation is a substitution congruence. A positive literal uses p mapped to A; a negative literal uses p mapped to neg A and the displayed double-negation square. | Both endpoint formulas and zero absorption are respected. |
| Lemma 5.1 | Nonempty P supplies a variable p. The cited object isomorphisms and coherence identify the particular q_p and e_p arrows; substitution preserves their inverse equations for arbitrary A. Appendix E supplies inverse terms. | No defect established. The cited isomorphism types match the book, §12.5, printed p.294. |
| Lemma 5.2 | A proof congruence contains every K_A. The quotient preserves products, coproducts and inverse equations. q_A makes A vee top terminal; e_A then makes the first product projection invertible. The diagonal equates the two projections, and pairing equates arbitrary parallel arrows. | No use of coherence in the quotient was found. Coherence is used in the original category before passing to classes. |
| Corollary 5.3 | P is nonempty and the extra equation holds under every interpretation. Agreement under all interpretations is substitution closed because composing an interpretation with substitution gives another interpretation. Totality equates projections at every object. | No defect established. The proof does not assume that the kernel of one interpretation is substitution closed. |

The subsidiary constructions were also read: substitution identities and
composition, retract transport of K_A, union and witnessed zeros, the ordinal
coordinate calculation, term-to-arrow congruence correspondence, and the typed
inverse and split-comparison paths. No ill-typed composite or loss of an
inhabited-hom condition was exhibited.

# (C) Minor issues

## C1. Consecutive “We also” sentences in the abstract

- **Anchor:** p.1, abstract, source lines 35–38: “We also prove ...” followed
  by “We also give ...”.
- **Failure mode:** local repetition; severity **minor**, optional stylistic polish.
- **Evidence:** the two consecutive sentences as printed. Knuth–Larrabee–Roberts,
  [Mathematical Writing, §1, point 9](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf#page=4),
  advises varying sentence structure and avoiding repeated “also” in consecutive
  sentences. This is contextual advice, not a prohibition.
- **Impact:** rhythm only. The introduction of the formalization and the
  relationship to the written proofs are now clear.
- **Possible repair:** remove the first “also”, retaining the accepted
  formalization sentence. No repair is implemented or required for correctness.

## C2. Three transformations are named without explanation in the Lean guide

- **Anchor:** p.19, Appendix D.5, source lines 1567–1575: “Gentzenization, cut
  elimination and atomization express the given arrow as a finite union of
  these paths”.
- **Failure mode:** compressed exposition / ambiguous terminology for the
  intended reader; severity **minor** relative to the main result.
- **Evidence:** the sentence supplies the conclusion and links source
  declarations, but the manuscript does not explain the individual transformations.
  Selected source inspection confirms the distinction: PositiveGentzenization
  represents a positive term by a Gentzen derivation; PositiveThinningAtomization
  replaces weakening on compound formulas by weakening on literals and constants;
  GentzenMixNormalForm constructs finite unions of literal paths in the mix fragment.
- **Impact:** a reader unfamiliar with these transformations must consult Lean
  to discover what the three names contribute. This weakens D.5's stated role
  as a translation guide. It does **not** establish a missing Lean proof or
  a defect in the main theorem, which invokes the published coherence theorem.
- **Possible repair:** briefly identify the transformations and state what
  “atomization” means here before invoking their combined consequence. A
  reproduction of every cut-elimination reduction is not required by this finding.

# (D) Cross-section consistency failures

## D1. The reference to “recovery maps of Section 3” is insufficiently identified

- **Anchor:** p.20, Appendix D.5, source lines 1611–1614: “The normalization
  and recovery maps of Section 3 then transfer faithfulness ...”.
- **Failure mode:** ambiguous cross-reference; severity **minor**.
- **Evidence:** Section 3 introduces normalization isomorphisms and states the
  equivalence with the normal-form presentation, but does not identify maps
  under the name “recovery”. The named reduction/recovery maps appear in
  Section 6's footnote, at source lines 889–892. This is a referent/navigation
  issue, not evidence that the equivalence or transfer is false.
- **Impact:** the reader cannot immediately match the maps named in D.5 with
  the data at the cited location.
- **Possible repair:** identify the normalizing equivalence and its occurrence
  compatibility directly, or point precisely to the reduction/recovery explanation.

No other cross-section failure was established. In particular, the review
found no drift in the composition convention, substitution hypotheses,
term/quotient distinction, original-category use of coherence, or restriction
of zeros and empty unions to inhabited hom-sets. Positive normal expansions
are used as retracts, not asserted to be distributivity isomorphisms. The
source-equation derivations in D.5/E.3 are distinguished from consequences
of coherence in Section 6.

# (E) Acceptance conditions, non-negotiable

No unmet mathematical condition was established. The necessary conditions
examined are already present: uniform substitution closure in the maximality
claim; coherence applied in the original category; existing-arrow witnesses
for zeros; and all-interpretations agreement in the model argument. Their
loss would invalidate the relevant deduction, but no such loss was found.

C1, C2 and D1 are local exposition or navigation points. None warrants
rewriting the theorem or its proof. This review does not impose additional
mathematical reconstruction as a condition of the present manuscript.

# (F) Not checked / uncertainty log

The complete v22 LaTeX source and bibliography were read. The review examined
the main arguments, all appendices, selected Lean declarations and relevant
primary-source passages. The existing PDF was consulted for page locations;
the abstract and relevant appendix layouts were inspected, including freshly
rendered pp.19, 20 and 22. Temporary renders were kept outside the repository.

Primary-source comparisons included:

- The conjecture and definition of B: Proof-Theoretical Coherence, September
  2007 revision, §14.2–§14.3, printed p.322.
- Boolean Coherence: the same source, §14.2, printed p.321.
- The q/e isomorphism types: the same source, §12.5, printed p.294.
- The negation-free hypotheses and constructions in
  [Isomorphic Formulae in Classical Propositional Logic, Lemmas 6–7](https://arxiv.org/html/0912.1271v3).
- The governing mathematical-writing advice cited under C1 and the previously
  consulted context in §1 on connected exposition and reader expectations.

The review did not reconstruct every cut-elimination reduction, audit every
production Lean module, or conduct an exhaustive new literature search. It
did not repeat compilation, kernel verification, Comparator, Palomar preflight,
service verification or registration. Existing successful checks were not
represented as new review work. The Lean source cited by the manuscript is
the separately registered commit `5dbee39bea09539bd130f729e82636419f71f920`;
that is distinct from the reviewed manuscript snapshot identified in A.

The initial read-only review changed no repository files. This report is a
subsequent written record requested by the author; its creation does not
implement C1, C2 or D1. Source/PDF identity is checked against the hashes above
when the report is delivered. No manuscript version is incremented.

Retained report: `docs/reviews/V22_READ_ONLY_REVIEW_2026-11-02.md`.
Delivery target:
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-V22-Review-20261102/V22_READ_ONLY_REVIEW_2026-11-02.md`.
Delivery is from committed bytes, with byte/SHA-256 verification and a separate
receipt. Any conflicting existing Downloads file is preserved.

Strongest confirmed blocker: **none established**.
Strongest suspected unconfirmed blocker: **none supported by evidence**.
Most important unchecked item: independent reconstruction of the entire
cut-elimination dependency. No unavailable material was treated as verified;
an independent journal acceptance judgment would require further assessment.
Final formal referee recommendation: **unknown**.
