# V27 abstract: focused hostile review

Date: 17 November 2026. Manuscript: *Maximality of the Došen–Petrić Boolean Category*. Scope: the final v27 abstract, compared with the v26 theorem, its two proof routes, the formalization account, and the registered Palomar v3 description retained in `docs/PALOMAR_V3_REGISTRATION_REPORT.md`. The abstract in `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v27.tex` matches `submission/arxiv-v27/abstract.txt`, whose SHA-256 is `bdbaa29879e1a8989e629845aa8107985b80e2958e29f65214f5d0b1e3d4937f`. This is an author-side review of the abstract, not a new audit of the complete proofs.

## (A) Kill-shots / hard blockers

None established.

## (B) Major weaknesses

None established. The opening retains the freely generated zero-identity Boolean category and the nonempty variable set. The dichotomy applies to congruences preserved by the presentation's operations on morphisms and uniform formula substitution. This is precisely the class defined in v26, Section 2. Theorem 2.1 and the immediately following equivalence identify its only members as equality and the total congruence. The registered v3 description states the same dichotomy. The abstract neither removes substitution closure nor asserts collapse from an arbitrary kernel of one interpretation.

The proof-outline sentence reviewed is:

> We give two proofs that use Boolean Coherence and uniform formula substitution to derive equality of the product projections from an identification of distinct parallel morphisms.

This is supported by Sections 4–6 and by `PresentationShortMaximality.lean`, `PresentationMaximality.lean`, and `PalomarMaximality.lean`. Both routes use occurrence isolation and the passage to all formula instances before their respective collapse arguments. The identification refers to the congruence in the preceding sentence; the projection equality holds modulo that congruence. Omitting the details of occurrence isolation from this outline changes no hypothesis or conclusion. Evidence: derivation and explicit source correspondence.

## (C) Minor issues

Two local issues in the initial candidate were resolved in the agreed wording.

- The dichotomy's grammar now reads “either is equality or identifies every pair of parallel morphisms.” The opening “Every congruence preserved by” attaches both closure conditions directly to the congruence.
- The formalization account uses separate sentences for the proofs and their dependencies, and for the inclusion of Boolean Coherence and the occurrence-coordinate correspondence. This avoids describing the Appendix A correspondence as necessarily a dependency of the maximality argument.

The replacement proof-outline sentence above explicitly retains distinctness and parallelism. No unresolved minor issue was identified in the agreed text.

The separately inspected, unchanged Palomar v3 abstract retains the grammatical mismatch “is either equality or identifies.” Moving “either” before “is” would repair its parallelism. This is a wording blemish, not a mathematical ambiguity affecting the stated dichotomy. The v27 abstract already uses the repaired order.

## (D) Cross-section consistency failures

None established. “Every pair of parallel morphisms” preserves the hom-set typing and does not assert the existence of a morphism in an empty hom-set. The first sentence's nonempty-variable hypothesis governs the following dichotomy. The conjecture sentence agrees with the introduction's stated conjecture and its citation. Both proof routes and both occurrence-coordinate descriptions are present in the manuscript and formalization account. The shorter abstract omits the model corollary without contradicting or deleting it from the paper.

### Exact registered abstract comparison

The `abstract` field of `provenance/palomar-v3-registration-20261103/entry.json` equals the `project.description` in `formalization.yaml` after whitespace normalization. It was also checked against `PalomarMaximality.lean`, `PalomarCorrespondence.lean`, Section 2 and Appendix D.3. No mathematical error was established:

- The nonempty-variable hypothesis governs maximality and the congruence dichotomy. Morphism congruences are families of equivalence relations on existing hom-sets; the explicitly retained closure conditions agree with the manuscript. The passage from the registered term formulation to morphisms is justified by the quotient correspondence.
- The identity and zero endomorphism of each variable are distinct, exactly as `identity_ne_zero` states. The supplied variable itself witnesses nonemptiness; applying this under the paragraph's initial nonempty assumption is valid.
- `no_top_to_bot` proves absence of a term from `top` to `bot` for every variable type. Since the category's morphisms are represented by terms, the registered categorical wording is correct. The initial nonempty assumption makes this summary weaker than the declaration, not false.
- Maximality and the equality-or-totality dichotomy are equivalent formulations here. Listing both is repetitive as a mathematical summary, but accurately records the separately registered declarations; it does not assert an additional independent result.

The registered abstract and the paper's abstract emphasize different results but make compatible mathematical claims. This check provides no mathematical reason that their formulations needed to differ. No registry metadata was edited.

## (E) Acceptance conditions, non-negotiable

Retain the nonempty-variable hypothesis, the specified free zero-identity Boolean category, closure under the operations on morphisms and uniform substitution, and the restriction to parallel morphisms. Retain the distinction between the proofs' dependencies and the additional occurrence-coordinate correspondence. The agreed text meets these conditions; no further repair is required by this review.

## (F) Not checked / uncertainty log

No new Lean build, kernel replay, complete mathematical proof reconstruction, or visual inspection of the v27 PDF was performed in this abstract review. The conjecture attribution was checked against the manuscript's cited statement, not independently re-audited in Došen–Petrić's book.

- Strongest confirmed blocker: none.
- Strongest suspected unconfirmed blocker: none supported.
- Most important unchecked item: the complete earlier proof dependency chain, unchanged by this abstract revision.
- Dependence on unavailable material: none for the comparison of the abstract with the inspected manuscript and registration description.
- Formal journal recommendation: unknown and outside the scope of this abstract check. Focused disposition: no confirmed blocker or unresolved correction in the final abstract.
