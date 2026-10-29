# Local hostile review: Positive and Boolean coherence

This author-side review applies
[HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe)
to eighteen actual source modules, their correspondence map and verification
records. Genre: formal mathematical proof; axes: correctness, self-containedness,
exposition and reproducibility. It is not independent peer review.

## (A) Kill-shots / hard blockers

Anchor: PresentationCoherence.lean, theorem coherence, “f = g”, and the current
full-paper maps. No confirmed blocker was found in that stated occurrence-
faithfulness theorem. A stronger whole-paper conclusion would be unproved:
the full source congruence/substitution correspondence, actual maximality
instantiation, short proof, model corollary and remaining appendix claims are
continuing obligations. Evidence: absence_in_text for those new endpoints.
Severity: major for a whole-paper completion claim; repairable by the remaining
constructions. That stronger claim is not made here.

## (B) Major weaknesses

1. Anchor: GentzenPurePortCoordinates.lean, position_ofPosition/position_injective;
GentzenPurePortRelations.lean, “PureEdge” and theorem relation. Claim as written:
each literal edge has exactly its independently tagged source and target.
Failure mode tested: inconsistent_use of formula equality for occurrence equality.
Evidence: derivation, structural_argument and toy_test. Signed labels and both
coordinates are typed; constructors distinguish repeated left/right positions;
constants have no ports. Exact relation and position-extensionality proofs detect
each edge. Repeated-port and crossed-target controls reject false identifications.
Downstream impact would be incorrect atomic normal-form equality. Severity: major
if omitted; resolved in actual source, without a label disequality hypothesis.

2. Anchor: ReducedFiniteUnion.lean, finiteUnion; GentzenMixNormalForm.lean,
“mix_normal_form”. Claim: every actual MixOnly proof has a finite atomic normal
form at its original endpoints. Failure mode tested: unproved normalization or
arrows silently added to empty hom-sets. Evidence: derivation and structural_argument.
Every empty union has an existing-arrow witness; zero independence and absorption
are proved. All primitive mix-fragment constructors are exhausted. Structural and
unary comparisons transport actual ports; native mix retains reversed blocks and
is explicitly a union of its two child paths. Identity, zero, top and bottom
bases are constructed. Downstream impact would be a circular restricted-coherence
argument. Severity: major; resolved without a supplied normalizer or reflection.

3. Anchor: GentzenNormalRetracts.lean, “recover : comp forward backward = id A”;
GentzenNormalExpansion.lean, dnf_expansion/cnf_expansion. Claim: represented
one-sided recoveries expand every formula to DNF/CNF. Failure mode tested:
unsupported_generalization to distributive isomorphisms or an assumed proof duality.
Evidence: derivation and verified source §11.3 pp.264–266, §12.5 pp.289–292.
Only the stated one-sided law is stored. Both orientations are constructed from
the existing actual distributive section/retraction equations, tensors, swaps,
sourceConj and mixedDisj. All representation fields are instantiated. Downstream
impact would be invalid cancellation. Severity: major; resolved; no reverse inverse
law or general G duality is assumed.

4. Anchor: GentzenPositiveCoherence.lean, “positive_coherence”; ReducedCoherence.lean,
“faithful”; PresentationCoherence.lean, interpretation. Claim: unrestricted Positive,
Reduced and source occurrence faithfulness, with the actual full interface.
Failure mode tested: unproved bridge hidden in a record field. Evidence: derivation
and exact public signatures. DNF/CNF universal-property induction reaches the
proved atomic base. Represented comparison maps preserve relations, and only the
proved recovery equations are canceled. Existing common atomic factorization
and explicit normalization transport transfer faithfulness. Every intended
interpretation field and signed-label law is constructed. A Nat instance is
nonthin, while Empty constants and empty Hom(top,bot) persist. Downstream impact
would be an invalid milestone-I claim. Severity: major; resolved by actual source
and the required audit in FINAL_VERIFICATION.json.

## (C) Minor issues

The normal forms are existential, and port transport uses Classical.choice in
the existing permitted kernel infrastructure. No extracted decision procedure or
computational complexity claim is made. No new manuscript defect was found.
Historical local checkpoints retain their original scope, superseded by the
current correspondence table. Full-paper completion remains open.

## (D) Cross-section consistency failures

No new failure was found in the active source/report/map scope. Pure means one
binary connective with both constants permitted; port tags and original occurrence
coordinates agree. All normal-form maps have explicit endpoints and left-first
composition. Restricted and unrestricted coherence are distinguished, all actual
bridges are instantiated, and recovery is never described as a two-sided inverse.
Milestone I's intended interface is closed; milestones II/III and the whole-paper
endpoint retain their separate meanings. No fixed-valuation kernel is described
as automatically closed under uniform substitution.

## (E) Acceptance conditions, non-negotiable

1. Retain compiled exact coherence/interface checks and the full allowed-axiom
   source closure. Failure requires withdrawing the verified coherence claim.
2. Retain all existing-arrow zero witnesses and the signed/repeated/empty boundary
   controls. Failure requires withdrawing the affected normal-form claim.
3. Deliver the reviewed reports and changed maps from verified committed bytes.
   Failure leaves this milestone's delivery obligation incomplete.
4. Prove the complete source substitution-congruence bridge, actual maximality,
   short proof, model corollary and all remaining v7 claims before whole-paper
   acceptance. Failure requires dropping the corresponding completion claims.

## (F) Not checked / uncertainty log

Strongest confirmed blocker to whole-paper completion: the listed congruence,
maximality, model and appendix endpoints remain unproved in this milestone.
Strongest suspected unconfirmed blocker in the coherence argument: none established.
Most important thing not checked here: the remaining full-paper constructions.
Independent kernel replay, Comparator, official/service verification, publication
and independent peer review are unavailable/not performed. A whole-paper decision
requires the remaining proof and verification material. Final recommendation:
unknown. The locally verified coherence scope can be retained while work continues.
