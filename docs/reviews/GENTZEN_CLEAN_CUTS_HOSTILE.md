# Author-side review: simultaneous clean cuts and initial elimination equations

This review applies [HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe)
to the actual local source and correspondence map. It is an author-side review,
not independent peer review or a second kernel replay. The input checkpoint is
a006ecdf7ca961f5355a44ed97629f960d5605d2 plus the recorded local changes.

## (A) Kill-shots / hard blockers

No confirmed defect was found in the simultaneous clean-cut theorem.
GentzenCleanCuts.lean:14 constructs the same f',g' for Topmost, both Atomized,
individual Reduced equalities and both AllBlocked predicates at the original
sequents. At line 31, Rules.cut_congr yields cut equality and the statement
expands both universal addressed clauses. Checks/CleanCuts.lean independently
ascribes those full signatures. Evidence: source and the final local type/build logs.

The old atomizer's failure remains a confirmed construction boundary, not a
counterexample to the new existence theorem. Anchor:
GentzenAtomizationBlockedBoundary.lean:58 and GentzenCleanCutChecks.lean:80.
The same negative example now has a positive simultaneous representative.
The original negative file is unchanged. No new manuscript defect follows.

## (B) Major weaknesses

**Global cut elimination is unproved.** Anchors: GentzenCutBase.lean,
GentzenCutConstants.lean, GentzenCutThinning.lean and the report's remaining
contract. Claim tested: every G P Γ Δ has a cut-free same-sequent proof with
equal Reduced denotation. Failure mode: unproved, with no counterexample
established. Evidence: the exported results prove specific equations and
repairs; they do not classify every minimal-rank cut or supply every principal,
parametric and blocked-contraction reduction with the required descent.
Downstream impact: coherence, actual-presentation maximality and full-paper
certification remain open. Severity: major for whole-paper completion;
repairability: complete those reductions and assemble the induction.

This is not a defect in the clean-cut theorem, and no general elimination
interface or caller normalization witness has been installed in production.

## (C) Minor issues

The BA5AF8B writing review's stray plus in the finite occurrence comment at
GentzenFiniteOccurrences.lean:100 is removed. The definition and proofs are
unchanged. All current status records now distinguish proved clean cuts and
initial elimination equations from the remaining global theorem; earlier open
statuses retain their historical scope. No unresolved local prose or type
correction was confirmed in the reviewed new source.

## (D) Cross-section consistency failures

No additional inconsistency was confirmed. The following targeted checks
address the substantive inference.

| Claim | Source/evidence inspected | Result |
| --- | --- | --- |
| Every omitted lower tag is atomic | AtomicOmissions; CleanCutChecks.equal_compound_unused | Quantifies over typed positions. A used equal label does not cover the other compound position. |
| Route realization terminates | GentzenEconomicalRoutes.lean:13 | Structural induction on K. Nonempty fibers are selected together; residual recursion removes the lower head. |
| Residual support is justified | SelectionMask.fixedAt, canonical_fixedAt, Route.factor_preimage; ContractionSelection.factor_route_preimage | Both directions of exact tail preimage correspondence are proved. No label-membership shortcut. |
| Actual unary support | GentzenInputRouteSupport and GentzenAtomizedRouting | Exchange/contraction are surjective; thinning obtains its inserted atomicity from the old Atomized input. |
| Same replacement in all conclusions | GentzenParameterizedRouteRepair; AtomizedReducesL/R; full atomized producers | Concrete h has CutFree, Atomized, equality and the full rebuilt eligible-descendant bound. |
| All input families | GentzenAtomizedAllInputReducers; logical/opposite/binary dispatch and leaf repairs | Actual cases are enumerated. CutFree excludes cut input; basis impossibility is internal. |
| Singleton/right HEAD/source W6 | SelectedLogicalReducer.right_atomized, SourceLeft.reduces_atomized, TerminalOne first/second and native/head-right exports | Existing named source witnesses and atomization laws are used; no new singleton node. |
| Rank descent uses chosen h | GentzenChosenRankReplacement.lean:16,52; atomized blocked normalizers | Accepts that h and full bound, retains inside/outside permutations and multiplicity, then reuses FiniteRank descent. |
| Initial atomization | GentzenCleanCuts.lean:20–27 | Performed before the atomized normalization. No pre/post atomization rank comparison or alternating unproved termination. |
| Constants and zero base equations | CutBase and the two further cut modules | Equations hold in Reduced. Empty list transports are explicit; zero idempotence uses the existing witnessed-zero algebra. |

All categorical calculations remain in the original Reduced quotient. The
product arrow of Route K F has type ante K → ante F; the coproduct arrow has
type succ F → succ K and uses the opposite product category. Category.comp
applies its first argument first. Existing-arrow witnesses and empty hom-sets
are retained; no HasZeroMorphisms, relation reflection, custom mathematical
axiom, new G constructor or coherence premise is introduced.

The clean-cut source anchor is §11.2 p.253 of the September-2007 text. The new
base equations correspond to pp.253–254, the constant additions at §11.5 p.273
and atomic-zero additions at §12.5 p.291. Reading those equations does not
replace the still-missing general elimination proof.

## (E) Acceptance conditions, non-negotiable

1. Preserve the exact unrestricted Reducibility and Blocked-w exports and all
   recorded mathematical boundaries. Their old exact-signature checks pass.
2. Prove actual support and one atomized replacement for each actual input,
   not independent existential witnesses. The new full exports discharge this.
3. Use that h in the rank-list decomposition and preserve Atomized through
   replacement and descent. The supplied-witness decomposition and strengthened
   normalizers discharge this.
4. Export original-sequent simultaneous representatives, with both universal
   tied clauses and no extra global hypotheses. The new exact checks pass.
5. Preserve the negative atomizer example and test the positive theorem on it,
   plus the required positional/empty/constant/signed-literal cases. These compile.
6. Keep global elimination and later paper claims open until their own proofs
   and correspondences are checked. The active maps retain that boundary.
7. Bind final source, dependency closure, five controls and report deliveries
   to committed bytes. Local source/closure/control evidence passes; the
   post-commit delivery/ref comparison is a separate recorded final operation.

These conditions concern mathematics and evidence. They do not add an author
approval checkpoint or authorize publication.

## (F) Not checked / uncertainty log

Reviewed the new route/support/parameterized-repair proofs, every strengthened
producer and dispatch body, supplied-witness rank decomposition, both invariant
normalizers, public theorem, focused examples, the initial elimination equations,
current maps/corrections and the report. The fixed-support well-foundedness,
containing transport and exact outside correspondence are reused from their
completed checkpoint rather than reproved.

The final local strict check records 442 screened Lean files and 11,105
audited project declarations. The full public closure includes all 29 new
production modules. All three exact-signature checks and five expected negative
controls pass. 458 source/configuration/manuscript digests and 62
compressed logs are retained, including 25 nonzero implementation attempts.
Those facts are local evidence; this review does not supply an independent
kernel, Comparator, official/service verification or whole-manuscript reproof.
No TeX source changed and no fresh rendered-manuscript review was performed.

Strongest confirmed blocker to whole-paper certification: the global elimination
and subsequent coherence bridges are still unproved. Strongest suspected but
unconfirmed defect in clean-cut normalization: none established. Most important
unchecked result: global cut elimination with the complete blocked-contraction
commutations. Recommendation: the checked local evidence supports the clean-cut
milestone; whole-paper certification remains unknown. Delivery is certified only
by the subsequent committed-byte receipt, not by this source review alone.
