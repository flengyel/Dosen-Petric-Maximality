# Manuscript v15: the registered Lean statements

1 November 2026. V15 adds Appendix D, “The registered Lean theorems,” on
pages 13–15. It states the five registered declarations in mathematical
notation and explains their correspondence with the paper. The manuscript
has 16 pages. V14 and every preceding source, PDF and package are preserved.

## Mathematical content

The appendix defines the typed sets of arrow terms, their generated equality,
quotient classes, primitive zero endomorphisms and substitution. A typed
commutative square relates term substitution to the functor on the quotient.
It defines the precise conditions on PrimitiveCongruence, Closed and Total;
totality quantifies over existing parallel terms and does not create arrows.

It states both maximality theorems, their equality-or-totality dichotomy,
the inequality between a variable's identity and zero, and the absence of a
top-to-bottom term. The first three selected declarations require a nonempty
variable set. The identity statement takes a variable as an argument; the
empty-hom statement also holds for the empty variable set.

The final subsection explains why a relation containing generated equality
descends to quotient arrows, why the dichotomy supplies preservation under
negation, and how pulling back a substitution congruence on arrows yields the
main theorem. It distinguishes arbitrary substitution P→Form(Q) from the
self-substitution required by Closed. It also names the existing coherence,
model-corollary and intermediate collapse proofs. The five selections do not
exhaust the Lean development. No missing Lean proof was identified or repaired.

## Review and validation

The [hostile review](reviews/V15_HOSTILE_REVIEW_2026-11-01.md) and
[mathematical-writing review](reviews/V15_WRITING_REVIEW_2026-11-01.md) apply
the requested plugins to the added argument and correspondence map. They are
author-side AI-assisted reviews. Unchanged mathematical and literature material
retains the documented v14 review scope; no independent certification is claimed.

The [validation record](../provenance/manuscript-v15-review-20261101/validation.json)
records an exact inverse comparison: removing Appendix D, its Section 6 pointer
and the version/bibliography suffix changes recovers v14 byte-for-byte.
All seven previous statement bodies and twelve numbered displays are identical.
The ten prior diagrams and thirty prior labels remain; one typed square and
one appendix label are added. Both bibliographies, the supplied Palomar entry,
Appendices A–C and the authorized AI disclosure are unchanged.

The manuscript and independently extracted four-file archive compile to
identical 16-page layout text with thirteen bibliography entries. Final logs
contain no reference/citation, box or duplicate-destination warnings. All
sixteen pages were inspected on contact sheets; pages 13–15 were also viewed
individually. Build exits, final logs and the exact diff are retained in
provenance/manuscript-v15-review-20261101/.

All 83 preceding release files are byte-identical to the input commit.
All 856 registered proof/input blob identities match the immutable version-2
source, 5dbee39bea09539bd130f729e82636419f71f920. The source inspection checks
the existing declarations, not a new proof replay. No Lean code, registered
input, toolchain, dependency or stash is changed. Successful proof builds,
kernel replay, preflight and service verification are reused. Neither Palomar
intake/registration nor an arXiv upload is performed.

## Files and delivery

- [V15 PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v15.pdf)
- [V15 TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v15.tex)
- [Four-file archive](../submission/arxiv-v15/Dosen-Petric-Maximality-v15-arxiv-source.tar.gz)
- [Package and submission fields](../submission/arxiv-v15/README.md)
- [Current arXiv preparation](ARXIV_PREPARATION_REPORT.md)

The reports, both reviews, PDF and package are delivered from committed bytes to
/mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v15-20261101/.
The corrected v14 hostile review is included; earlier differing copies are
preserved. Exact paths and byte/SHA-256 checks are recorded in
provenance/manuscript-v15-review-20261101/delivery-receipt.json after delivery.
The preceding preparation report is retained under docs/history/.
Completed main is pushed and the remote ref verified before readiness is
reported; the delivery receipt records its source commit.
