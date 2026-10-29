# Local hostile review: the short q_A/e_A proof

This author-side review applies
[HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe)
to the six new source modules, actual argument, public checks and claim map.
Genre: formal mathematical proof. Axes: correctness, correspondence and
reproducibility. This is not independent peer review.

## (A) Kill-shots / hard blockers

Anchor: PresentationShortMaximality.lean, “short_maximality”. No confirmed blocker
was found in the stated short-route theorem. Whole-paper completion would remain
unproved: model, further substitution/operation laws, original isolation witnesses
and remaining appendix claims are not supplied by this theorem. Failure label:
unproved for that stronger completion claim; evidence: absence_in_text; severity:
major for whole-paper acceptance; repairable by the remaining constructions.
That stronger claim is not made.

## (B) Major weaknesses

1. Anchor: PresentationShortQ.lean, q_definition/q_qInverse/qInverse_q;
PresentationShortE.lean, e_definition/e_eInverse/eInverse_e. Claim: the particular
manuscript q_A and e_A have explicit two-sided inverses in the original source
quotient. Failure mode tested: unsupported_generalization from bijective relation
to invertibility. Evidence: derivation and structural_argument. Both inverse
terms are constructed using the unchanged primitive grammar, and all four actual
inverse equations are proved by original coherence and explicit relation
calculations. The e inverse kills its unused branch by an existing-arrow zero
witness fst;diag. Distribution is not presumed invertible. Downstream impact
would invalidate Lemma 5.1 and the short route. Severity: major; resolved.

2. Anchor: PresentationShortSubstitution.lean, qInverseTerm_subst and
eInverse_substitute. Claim: all particular arrows and their inverses commute
with whole-arrow substitution, including endpoint types. Failure mode tested:
unproved transport inferred only from object substitution. Evidence: derivation.
All ten equations are checked directly for arbitrary substitutions between
variable types in independent universes. Downstream impact would miss the
manuscript's structural-isomorphism correspondence. Severity: major; resolved
for these particular constructions, without claiming general negation/substitution
compatibility.

3. Anchor: PresentationShortTerminal.lean, q_terminal/terminal_id/terminal_pair.
Claim: the all-K hypotheses make E=A∨top terminal modulo the congruence.
Failure mode tested: inconsistent_use of original equality and quotient equality.
Evidence: derivation and structural_argument. Original through-top equality
identifies the witnessed zero, closure gives the copair equation, and the actual
q inverse gives the quotient retraction. Only congruence laws and original
terminal uniqueness are then used. Downstream impact would be circular use of
the earlier symmetric-fold collapse. Severity: major; resolved independently of
that route. The missing-all-contexts control rejects replacing every K_A by one.

4. Anchor: PresentationShortProjection.lean, r_i/projection_id/diagonal_u/projections/
total. Claim: quotient-terminal E and the original e isomorphism equate the
projections, then all parallel arrows. Failure mode tested: unsupported_generalization
by canceling j_A or applying coherence in a quotient. Evidence: derivation and
toy_test. Pair extensionality modulo Q follows from original product eta and
Q.pair. Conjugation uses proved original inverse equations; diag is identified
with the constructed inverse, and pair(f,g) completes collapse. No quotient
faithfulness, injection cancellation or arrows in empty hom-sets are used. The
corresponding cancellation and inverse-direction controls reject those shortcuts.
Downstream impact would invalidate Lemma 5.2. Severity: major; resolved.

5. Anchor: PresentationShortMaximality.lean, “ShortProof.total”. Claim: the distinct
short route reaches actual maximality under the original full-congruence and
uniform-closure hypotheses. Failure mode tested: unproved final bridge.
Evidence: derivation. Actual isolation, signed labels, source normalization,
substitution and double negation supply all K_A, then the new collapse is invoked.
The old symmetric-fold theorem remains unchanged. Severity: major; resolved for
the stated endpoint; full-paper acceptance still requires the listed obligations.

## (C) Minor issues

The e inverse relation calculation takes longer to elaborate than the surrounding
categorical argument. Its actual successful log and development failures are
retained. No extracted algorithm or complexity assertion is made. No manuscript
correction was established.

## (D) Cross-section consistency failures

No new inconsistency was found. The report distinguishes the exact particular
isomorphisms, one-sided distributive section and quotient inverse equations.
Execution-order composition and both original inverse directions are explicit.
P is arbitrary; the manuscript's nonempty case is included. Earlier maximality
and all cut/coherence results are preserved. Local verification, delivery,
independent review and full-paper completion retain separate statuses.

## (E) Acceptance conditions, non-negotiable

1. Retain all four original inverse equations and their concrete terms. Failure
   withdraws Lemma 5.1 correspondence and the short-route claim.
2. Retain direct congruence reasoning, all-K scope, witnessed zeros and exact
   substitution/public checks. Failure withdraws the affected correspondence.
3. Retain full strict source/dependency verification and committed-byte delivery
   of the reviewed reports and changed maps.
4. Finish the model, remaining operation/substitution/isolation/appendix claims
   before whole-paper acceptance.

## (F) Not checked / uncertainty log

Strongest confirmed blocker to whole-paper completion: the remaining claims
(unproved; absence_in_text). Strongest suspected unconfirmed blocker in the short
proof: none established. Most important thing not checked here: the future
universal-model and remaining appendix constructions. Independent replay,
Comparator, official/service verification and publication were not done; no
unavailable review is reported complete. Recommendation: accept the stated local
short-proof scope when FINAL_VERIFICATION.json records passing checks; whole-
paper acceptance remains unknown.
