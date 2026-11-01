# Mathematical-writing review of manuscript v15

1 November 2026. Author-side AI-assisted review applying the mathematical-writing
plugin to the new Appendix D, its Section 6 pointer and correspondence records.
Input: v14 at 9e46cdca7f2fe2f59983ecf324e08a80ad09c81a. Output: v15, 16 pages.
The preceding argument is preserved by an exact inverse text comparison;
its complete v14 review is not represented as newly repeated research.

## Governing source and actual outline

The governing source is Knuth, Larrabee and Roberts, Mathematical Writing,
especially Section 1 and Sections 4–5. The consulted
[Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)
and the locally retained retypeset copy are recorded in
provenance/manuscript-v14-review-20261101/source-review-record.json.
This revision uses those consulted passages: introduce variables and definitions
before use, connect formulas to sentences, make theorem statements complete,
and provide enough explanation to read the argument. No new quotation or
unverified page attribution is introduced. The author's preference for
Došen–Petrić's direct exposition governs terminology; it is not attributed to Knuth.

The existing organization is retained. The appendix answers a specific
question: what do the five registered Lean statements assert, and why do
their relations on terms give the theorem on arrows?

| Part | Mathematical function |
| --- | --- |
| Abstract and Introduction | State maximality, the literal equation and its relationship to the conjecture and literature. Unchanged. |
| Sections 2–3 | Define the category, congruences, occurrence relations and substitution; state maximality and coherence. Unchanged. |
| Sections 4–5 | Isolate a literal, obtain every K_A, prove equal projections via q_A/e_A and deduce the model corollary. Unchanged. |
| Section 6 | State the formalization's inputs and symmetric-fold proof; add the precise pointer to Appendix D. |
| Appendices A–C | Give occurrence/ordinal coordinates, typed defining diagrams and the two source-rank corrections. Unchanged. |
| D.1 | Define term sets, generated equality, quotient, substitution and the primitive relation's laws. |
| D.2 | State all five selected theorems, identify the two proof routes and explain the two consistency conclusions. |
| D.3 | Give quotient descent and pullback, derive negation preservation after the dichotomy and identify the other named proofs. |
| Disclosure and bibliography | Preserve the authorized disclosure and all bibliography entries verbatim. |

No alternative outline is needed. D.1 supplies every new object used in D.2;
D.3 then proves the correspondence rather than referring to an unexplained
bridge. Review and release reporting remain outside the manuscript.

## Source comparison and implemented wording

| Governing advice | Application in v15 |
| --- | --- |
| Section 1 point 5: complete theorem statements | Each entry gives its assumptions on P, R, terms and equality before its conclusion. |
| Section 1 points 10–11: formulas as parts of sentences; variables introduced | P,Q,A,B,R and σ are introduced before the displays. Consequences follow the equations in prose. |
| Section 1 points 14–15: consistent notation and indices | R_A,B and E_A,B have the same endpoints; substituted endpoints are printed. The equality of term classes is distinguished from their relation. |
| Section 1 point 17: unambiguous assertions | Closed means self-substitution; the arbitrary-Q square is separately typed. Totality does not assert existence. |
| Sections 4–5: explanations proportionate to the argument | Representative independence is proved with equivalence and E⊆R; both directions of the main theorem's correspondence are written out. |

The source uses standard mathematical terms: equivalence relation, quotient,
composition, substitution, pairing, copairing, Boolean evaluation and total
relation. PrimitiveCongruence, Closed and Total are quoted Lean identifiers
whose conditions are defined explicitly. They do not become new undefined
mathematical terminology. Code references are used only to identify proofs.
The text contains neither “actual” nor “genuine.” Their absence is a check,
not a claim that they were removed from v14.

The final paragraph replaces a general announcement about “other theorems”
with direct references: Presentation.coherence proves Theorem 3.1 and
PresentationSemantics.model_corollary proves Corollary 5.3. The collapse
paragraph states its common namespace once and identifies the two equations
and terminal retraction. This also resolves the preliminary overfull lines.

## Definition and typing audit

| Object or assertion | Definition and checked type |
| --- | --- |
| T_P(A,B), E_A,B, [f] | D.1: arrow terms with source/target in Form(P), generated equivalence on parallel terms, and quotient class. |
| id_A,z_A | Terms in T_P(A,A); their classes are the identity and the zero endomorphism in equation (2). |
| g∘f | f applied first, matching Term.comp f g. |
| f[σ], F_σ([f]) | σ:P→Form(Q); both have endpoints A[σ],B[σ] over Q. The typed square commutes by quotient substitution. |
| PrimitiveCongruence | A family of equivalence relations containing the defining equations; the comp and both tensor laws have their endpoints displayed. |
| Closed | σ:P→Form(P), changing both endpoints in R. |
| Total | Every pair of existing parallel terms is related. Empty term sets remain empty. |
| The five selected types | Three declarations require P nonempty; identity_ne_zero takes p:P; no_top_to_bot allows empty P. |
| Boolean evaluation | τ:Form(P)→{0,1}, τ(p)=1; term induction gives τ(A)≤τ(B), forbidding top→bottom. This is the retained Truth invariant. |
| R-bar and R-theta | Descent through E and pullback through f↦[f]; representative independence and totality correspondence are stated. |
| Negation | Preserved after equality-or-totality is proved, without assuming it in PrimitiveCongruence. |

The eleven diagrams consist of the ten identical prior diagrams and the new
typed term/quotient substitution square. No endpoint, sign convention,
empty-hom qualification or existing-arrow condition is removed. The review
of the new claim-map row corrected a nonexistent draft identifier to the
existing fold_manuscript/fold_symmetric declarations.

## Verification and limits

Removing the appendix and its pointer, then restoring the version and
bibliography suffixes, recovers the complete v14 source byte-for-byte.
All seven previous statement bodies, twelve numbered displays, ten prior
diagrams and thirty prior labels are unchanged. One square and one label are
added. Both bibliographies, the supplied Palomar entry and the authorized
disclosure are identical. The archive contains exactly four root files.

The manuscript and independently extracted archive compile to matching
16-page layout text with thirteen bibliography entries and no final warnings.
All sixteen rendered pages were inspected on contact sheets; pages 13–15
were additionally inspected individually. The source-check record identifies
the existing Lean declarations consulted. The registered proof/input blobs
and all 83 preceding release files are preserved.

This is a review of the added mathematical exposition and its correspondence,
with preservation checks on the previously reviewed argument. It is not an
independent peer review, new literature search, reproof of published coherence,
Lean/kernel replay or new Palomar verification. The prepared archive has not
been uploaded to arXiv. Report delivery and remote synchronization are recorded
separately in the release provenance.
