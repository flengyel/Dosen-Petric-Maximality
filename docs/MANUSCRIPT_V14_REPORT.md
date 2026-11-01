# Manuscript v14: terminology, typing and proof exposition

1 November 2026. The requested HostileRefereeGPT — Cat/Rec and
mathematical-writing plugin reviews have been applied to the complete arXiv
draft. The release is v14, 14 pages; v13 and all earlier sources, PDFs and
packages remain preserved.

## Changes

The revision states the literal equation in the abstract and names the
double-negation step needed in its negative case. It uses “literal” for p or
¬p throughout. The phrases “actual” and “genuine” were already absent from v13;
their absence is verified rather than reported as a new deletion.

The arrow d:A∧(B∨C)→(A∧B)∨C is now called the dissociativity arrow, following
Došen–Petrić's September 2007 book, printed p.234. This correction is applied in
the structural definition, interpretation requirements and Appendix B.
Appendix A calls the defined functions occurrence maps, describes the two
bijections as consecutive numbering and gives the inequality defining the
block index. Unused names of external proof-net axiom systems are removed
from the literature comparison while the reference and its mathematical
relationship are retained.

The paper gives explicit types for the product/coproduct arrow operations,
the contravariant negation action, the relation Gf, substituted arrows and
the normal-form witnesses. The model proof names I_v and the assignment
p↦I_v(σ(p)) inducing its composite with substitution.

The alternative proof now defines typed v_A and w_A, shows both calculations
previously compressed into references to coherence and the first-injection
equation, and displays the inverse equations establishing terminality.
These deductions agree with the existing Collapse.lean and
PresentationSymmetricFold.lean proofs. The Section 5 heading states the
conclusion, “Equality of the product projections.” No formal proof is changed.

## Review records and limits

- [Hostile review](reviews/V14_HOSTILE_REVIEW_2026-11-01.md): anchored findings,
  the checked deductions, seven-claim audit, edge cases, conditions and
  uncertainty log. No fatal or major mathematical defect was established.
- [Mathematical-writing review](reviews/V14_WRITING_REVIEW_2026-11-01.md):
  source-based diagnosis, actual outline, definition/notation audit, concrete
  replacements, preservation checks and scope.
- [Exact decisions](../provenance/manuscript-v14-review-20261101/editorial-decisions.json),
  [full diff](../provenance/manuscript-v14-review-20261101/v13-to-v14.diff),
  [paragraph functions](../provenance/manuscript-v14-review-20261101/paragraph-functions.json)
  and [source record](../provenance/manuscript-v14-review-20261101/source-review-record.json).

Both reviews are author-side AI-assisted work, not independent peer review or
mathematical certification. The complete source and the rendered document were
examined. The Stanford writing source and the relevant Došen–Petrić passages
were consulted. The official Lamarche–Straßburger PDF returned HTTP 403 to the
web tool; a mirrored primary-paper result supplied its freeness theorem text.
Unchanged literature comparisons retain the scope of the documented v13
review. No exhaustive priority search or independent reproof of the
published coherence theorem is claimed.

## Preservation and validation

The [validation record](../provenance/manuscript-v14-review-20261101/validation.json)
confirms that all seven statement bodies are unchanged after normalizing the
literal synonym and lemma captions. All twelve numbered displays, ten diagrams
and thirty labels are byte-identical to v13. All bibliography entries, the exact
supplied Palomar entry, Appendix C and the author-authorized AI disclosure are
byte-identical. Appendix B's mathematical content is unchanged; its explanation
uses the corrected name of d. Both proof routes and all three appendices remain.

The manuscript and the independently extracted four-file arXiv archive compile
to identical 14-page layout text, with thirteen bibliography entries. Final
logs contain no citation/reference, box or duplicate-destination warning.
All fourteen rendered pages were inspected on contact sheets; the expanded
proof on p.8 was also viewed as a full page. Exact command exits and compressed
final logs are retained with the validation record.

No Lean source, dependency, toolchain, comparator or registered input is changed.
No successful proof build, kernel replay, preflight or service check is repeated.
Registry versions 1 and 2 remain bound to their immutable sources. The manuscript
retains the supplied version-1 citation. No arXiv upload or new license choice
was made.

## Files and delivery

- [V14 PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v14.pdf)
- [V14 TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v14.tex)
- [Four-file upload archive](../submission/arxiv-v14/Dosen-Petric-Maximality-v14-arxiv-source.tar.gz)
- [Package and form fields](../submission/arxiv-v14/README.md)
- [Current arXiv preparation](ARXIV_PREPARATION_REPORT.md)

The report, both reviews, manuscript and package are delivered from committed
bytes to /mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v14-20261101/.
Different earlier files are preserved. The exact paths and byte/SHA-256 checks
are recorded in provenance/manuscript-v14-review-20261101/delivery-receipt.json
after delivery. The repository retains these reports under docs/ and
docs/reviews/. Local commits record the revision; no remote publication or
external submission is part of this editorial task.

