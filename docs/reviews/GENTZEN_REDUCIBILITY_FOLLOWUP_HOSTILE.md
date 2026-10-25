# Author-side hostile review: Reducibility follow-up

This is an author-side self-audit of the new Lean modules, exact public types,
source correspondence and follow-up report. It is not independent peer review
or certification. Manuscript v5/v4 was preserved and is outside this review.
The supplied 05c6bc8 review remains historical evidence; its confirmed blockers
are reclassified only where the new checked declarations supply the missing proof.

## (A) Kill-shots / hard blockers

**Reject a complete Reducibility claim.** Anchor: follow-up report, “Status and
unchanged target” and “Precise remaining inference”; source §11.2 p.250
Reducibility Lemma and p.252 right analogue. Claim required by the task: a
producer for every ReducibleL/R occurrence with every eligible descendant
strictly bounded. Failure mode: **unproved**. Evidence: **absence_in_text**,
supported by the exact PUBLIC_TYPES inventory and the restricted constructed
old-proof domains at DosenPetric/GentzenReducibilityLogical.lean:37, DosenPetric/GentzenReducibilityRightLogical.lean:14, DosenPetric/GentzenReducibilityMixed.lean:12 and DosenPetric/GentzenReducibilityMixed.lean:33.
Those domains do not cover all G constructors/selection configurations.
Impact: both full lemmata, subsequent Blocked-w and cut elimination remain open.
Severity: major for task completion; repairable by actual missing constructions
and dispatch, not by changing the target. No counterexample to the existential
lemma or new manuscript defect has been established.

## (B) Major weaknesses

1. **Remaining logical producers and dispatch.** Anchor: report, “Precise
   remaining inference”, W6 paragraph; source p.252 W5/W6. Failure mode:
   unproved. Evidence: structural_argument plus absence_in_text. Native
   Route.parallel_conjRight/disjLeft equations do not construct a proof with
   a selected principal C or account for actual disjLLast exchange ancestry.
   extract gives a selection for an ordered list; it does not itself prove
   every classified native/source profile is a covered old proof. Complete
   both selected-principal logical directions, singleton cases, profile
   extraction/transport and all remaining W1 configurations. Severity: major;
   no unsupported coherence assumption can supply these steps.
2. **No global termination inference.** Anchor: report, final ledger and source
   p.253 Blocked-w. Failure mode if promoted to a termination claim:
   unsupported_generalization. Evidence: structural_argument: current addressed
   conclusions quantify descendants inside the inserted proof, not all
   surviving outside occurrences or blocked ancestors in an arbitrary context.
   Outside-site transport and finite multiset induction are absent. Severity:
   major for Blocked-w, not a defect in the limited theorems actually stated.

The two former W4 blockers are now resolved in their exact local families:

- Distinguished-entry uniqueness at DosenPetric/GentzenBlockedEntryFrames.lean:45 uses actual blocked-premise
  frames and typed first separation, including disjLLast exchanges. The
  argument fixes C and side; it makes no global injectivity assertion.
- Left W4 at DosenPetric/GentzenReducibilityLogical.lean:37 uses only ReducibleL and its actual data. No caller
  InjectiveAscend or NoncontractingPath premise remains.
- The two-copy regression at DosenPetric/GentzenRightLogicalRegression.lean:56 supplies all data: Empty,
  A=B=bot, C=bot∨bot, gs=[[],[]], tail=[], existing constRight and opposite
  BlockedExamples.l [C]. Both roots are reducible and their ranks tie. It
  refutes the terminal candidate, not the unchanged existential target.
- Repaired right W4 at DosenPetric/GentzenReducibilityRightLogical.lean:14 uses the actual head disjR and blocked
  contraction. DosenPetric/GentzenRightLogicalRepairRanks.lean:54 proves root rank L+5, while
  DosenPetric/GentzenRightLogicalRepairBounds.lean:74 bounds eligible contractions by L via a constructed structural
  argument. Root nonincrease is neither assumed nor asserted.

Mixed-W5 audit: DosenPetric/GentzenMixedContractionRanks.lean:15 sums the full ordered selected lists from both
premises. The new rank uses the singleton-aware overhead δ(k); no premise is
duplicated and no artificial singleton node is introduced. The explicit
mergeBlock has two selected copies and its actual gammaMix blockedness compiles
for both variances. Both addressed theorems include the entire eligible-
descendant quantifier and derive entry uniqueness from their own hr input.
They are constructed chained-selection families, not a complete profile dispatch.

## (C) Minor issues

The prior report omitted declarations for I,J,v in its prose target. Those
binders are corrected in place; historical proof scope/counts are preserved.
The EntryFrame comment now says contractions of C on side s, matching its
constructor. The new report explicitly declares universes, contexts and all
variables, and separates source labels, proved equations and future targets.
No additional mathematical defect was confirmed in the newly proved claims.

## (D) Cross-section consistency failures

The current maps, README, validation and continuation now identify entry
uniqueness and W4 as proved while keeping full Reducibility open. Historical
reports retain earlier claims under explicit historical labels. The previous
continuation is preserved separately; its former proposed routes no longer
appear as competing active objectives. Both reviews reject a completion claim.
No occurrence-relation equality is used in reverse, no inclusion reflection
is invoked, and the presentation/equation/rank/predicate definitions are unchanged.

## (E) Acceptance conditions, non-negotiable

1. Both general producers must compile from exactly the existing ReducibleL/R
   inputs, with the complete descendant quantifier. Failure rejects full
   Reducibility completion.
2. Complete logical W5/W6, actual native/macro comparisons and selection dispatch;
   a source citation or typed candidate alone is insufficient.
3. Keep all occurrence tags, selected multiplicities, singleton and Empty cases;
   no global injectivity, coherence or rank premise may be added.
4. Prove outside-site/blocked-ancestor transport and finite multiset descent
   before claiming Blocked-w or global termination.
5. Preserve the strict audit, five expected negative-control rejections,
   checked/committed byte identity, SSH ref agreement and verified delivery.

## (F) Not checked / uncertainty log

Inspected all new module statements and the component/entry/bound proofs,
47 exact public queries and the successful 249-source / 8,919-declaration strict
receipt. The complete audit permits only propext, Quot.sound and Classical.choice.
Both boundary scripts, all five negative controls and manuscript hashes pass.
Raw exploratory failures are retained. The checks are local Lean checks;
independent kernels, Comparator, Palomar service, publication and whole-
manuscript correctness/novelty were not checked. Git/delivery receipts are
separate post-commit checks, not assumed by this mathematical review.

Strongest confirmed blocker: the general producers are absent despite the
new completed entry, W4 and constructed mixed-W5 results. Strongest suspected
unconfirmed blocker: a remaining native/source logical case may require a
larger administrative-path argument; no counterexample is known. Most important
unchecked item: full coverage and eligible-descendant bounds for those cases.
The noncompletion finding does not depend on unavailable material.
Recommendation: **reject a full Reducibility completion claim; retain the
verified limited results and continue the unchanged task**.
