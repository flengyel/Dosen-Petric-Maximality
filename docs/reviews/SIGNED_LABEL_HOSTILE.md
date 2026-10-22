# Signed-label preservation: hostile-referee review

## (A) Kill-shots / hard blockers

This is an author-side, AI-assisted self-audit of the actual signed-label
proof and source map, not independent peer review. No confirmed hard blocker
was found for the requested signed-edge invariant. Boolean Coherence still
blocks an unconditional actual-maximality claim.

Anchor: manuscript v4 §3, `thm:coherence`, and the coverage map, milestone I.
The missing assertion is `occurrenceMap f = occurrenceMap g → f = g` for all
parallel arrows in the published-equation quotient. Failure mode: **unproved**;
evidence: **absence_in_text**, no faithful `OccurrenceInterpretation` is
constructed. Severity: fatal for claiming completed actual maximality;
not a defect in the stated edge invariant. Repair: prove the source coherence
theorem and remaining bridges. No counterexample to coherence is alleged.

## (B) Major weaknesses

No major defect was confirmed in the scoped theorem. The following checks
address its possible failure points, with exact code anchors in
`DosenPetric/PresentationSignedLabels.lean`:

| Anchor and claim | Explicit hypotheses and proof evidence | Finding |
| --- | --- | --- |
| `Term.relation_signedLabel`, lines 17–70 | Arbitrary P, formulas, term, two occurrences and one edge. Induction covers all 31 primitive constructor schemas. Composition uses the intermediate occurrence; tensor branches use only the matching child invariant. Evidence: derivation. | No nonemptiness, decidable equality, coherence, or hidden preservation input. |
| Same theorem, n/r branches, lines 59–64 | Double negation uses `Literal.flip_flip`; both De Morgan directions preserve the full flipped child label by a tag split. Evidence: derivation. | A full literal equality, not just letter equality or outermost-sign comparison. |
| Same theorem, constant/zero/eta/epsilon branches | Unit/rho positions are Empty; zero/eta/epsilon relations are False. Evidence: structural_argument. | No dummy position or fabricated zero arrow. |
| `occurrence_signedLabel`, lines 73–80 | Every quotient arrow; quotient induction explicitly rewrites by `occurrence_ofTerm`. Evidence: derivation. | Reuses existing well-definedness; equality remains the source-generated `Derives` quotient. |
| `occurrence_literal` and transport theorems | Normal-form literal agreement follows from `signedLabel_eq_literalAt`; transport uses `transport_apply`, `literal_fromOcc`, and `transport_coordinates`. Evidence: derivation. | No faithful interpretation or arrow-equality inference from relations. |

The prior normalization review's global-label gap is closed by the first two
theorems above, not by an editorial downgrade. Its separate coherence and
derived-arrow-negation obligations remain open.

## (C) Minor issues

The term “signed label” means the letter with parity of every negation on the
path to a tagged position. The report states that definition before using it.
“Global” quantifies over all existing terms/arrows; it does not assert that
every pair of endpoint formulas has an arrow.

The new counterexample declarations take a supplied `p : P`. That local
witness is needed to exhibit copying/merging, while the preservation theorem
itself needs no inhabitant. These quantifiers are kept distinct.

## (D) Cross-section consistency failures

No remaining scope drift was found in the new theorem, correspondence table,
report, and current maps. `SignedLabelPreservation` in `NormalForm.lean` is
unchanged: it still takes a faithful `OccurrenceInterpretation`. The direct
theorem establishes its edge conclusion for `occurrenceMap`; it does not
fabricate the missing interpretation instance.

Anchor: `diag_copies` and `codiag_merges`, lines 137–152. For any supplied p,
one position has edges to two distinct target tags under the diagonal, and
two distinct source tags have edges to one position under the codiagonal.
Evidence: **counterexample**, these explicit kernel-checked witnesses show
why label agreement supplies neither functionality nor injectivity of an
individual relation. This also distinguishes relation injectivity from
faithfulness, which concerns distinct arrows. No claim that equal labels
identify occurrence tags is made.

Composition is covariant and applies the first Lean argument before the
second. No new functor, naturality, contravariant negation, or equivalence is
claimed. The argument applies directly to the original syntactic quotient,
not a quotient by an additional proof congruence. The generic two-object,
one-arrow test introduces no backward arrow or missing hom-set inhabitant.

## (E) Acceptance conditions, non-negotiable

Each condition is required for the signed-label report's narrow claim;
failure would require withdrawing that claim until repaired.

1. Compile the raw invariant for arbitrary P with every actual primitive
   constructor covered. Met by `Term.relation_signedLabel`.
2. Descend through quotient induction and the existing occurrence assignment.
   Met by `occurrence_signedLabel`; no presentation equations were changed.
3. Prove complete normal-form literal equality, its letter/polarity consequences,
   opposite-sign exclusion in both directions, and normalized transport.
   Met by the named declarations in the main report.
4. Preserve tags and empty hom-sets, and exhibit the copying/merging boundary.
   Met by the unchanged types and `diag_copies/codiag_merges`.
5. Retain strict compilation/audit and both control scripts' actual outcomes.
   Met: 26 source files, 1616 audited declarations, all five negative controls
   rejected, manuscript checksums unchanged; hashes are retained.
6. Keep coherence, derived negation/naturality, full congruence/substitution
   bridges, and actual maximality open. Met by the current maps.

## (F) Not checked / uncertainty log

The review inspected the new module, reused sign/normalization definitions,
the relevant manuscript §3 passage, and the current correspondence/coverage
claims. Evidence is in `provenance/wsl-signed-label/` and the runtime logs.
The full inherited source transcription, the book's coherence reduction,
and the manuscript's global novelty were not independently audited. No
independent kernel replay, Challenge/Solution comparison, Comparator,
official preflight, service review, publication, or whole-document layout
review ran. The source-grounded writing follow-up is separate editorial work.

Strongest confirmed blocker: unproved Boolean Coherence for an unconditional
actual-maximality claim; none found for signed-label preservation. Strongest
suspected unconfirmed blocker: none substantiated for the scoped theorem.
Most important unchecked item: normal-form faithfulness in the actual
published presentation. The narrow assessment does not depend on unavailable
material. Final recommendation: **unknown** as a publication decision; the
scoped signed-label endpoint passes this author-side audit. Reject a claim
that actual maximality is already fully formalized.
