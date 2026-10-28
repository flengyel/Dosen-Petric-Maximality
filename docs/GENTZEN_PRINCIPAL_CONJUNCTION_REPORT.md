# Principal conjunction reduction at exact selected positions

The continuation after df2b9ee proves the actual principal conjunction cut
reduction, including arbitrary selected gaps and every canonical fold transport.
Nine new production modules and Checks/PrincipalConjunction.lean are verified.
The v7 errata appendix, all prior proof work and the stash remain preserved.

## Exact result and construction

For arbitrary P, f : G P Γ (A :: Δ), g : G P Θ (B :: Λ), and
h : G P (F ++ A :: B :: U) V, PrincipalConjunction.selected_equation proves
Reduced equality between the positional cut of conjR f g against conjL F U h
and selectedReduction f g h. Both have the exact sequent
(erase selected ++ (Γ ++ Θ)) → (V ++ (Δ ++ Λ)). No faithfulness, coherence,
DecidableEq P, Nonempty P, normalizer, or caller eliminator is assumed.

The reduction routes the two component tags below the logical rule, cuts on A,
then cuts on B, and transports only list association at the outer boundary.
Its cut count is f.cutCount + g.cutCount + h.cutCount + 2. Its Atomized predicate
is equivalent to the conjunction of the three original Atomized predicates.
Both component formula degrees are strictly below the original conjunction's
degree, with no rank hypothesis. This is a reduction equation. It is not yet
a cut-free representative theorem: the outer cut is used after replacing the
inner cut by its smaller-degree normal form in the future global induction.

The native reduction order A then B is an alternative to the displayed p.254
order in the September-2007 source. It is proved directly from the existing
Reduced equations; it is not justified by an unproved interchange, coherence
or cut-elimination theorem. The distinction is recorded outside the manuscript.
No correction to the source theorem or manuscript is asserted by this choice.

## Proof dependencies and exact correspondence

CutDistribution proves the conjunction/disjunction strength-factor equations,
then mixed_strength for the actual Term.mixedDisj. These use the published
Reduced associativity, naturality, dist_conj and dist_disj laws. ProductCalculation
proves the structural adapters by the already established product universal
property. PrincipalConjunction.equation is the resulting categorical identity
between the conjunction principal cut and the two component splices.

ContextAssociativity proves every tag of the canonical list-association script
and join_assoc. TripleContexts packages existing explicit Iso comparisons,
proves their inverses, split_assoc and split_cons, on both product and opposite
coproduct sides. Empty contexts use actual units and equality transports.
PrincipalConjunction.rule_equation instantiates the categorical identity with
actual Gentzen denotations. The intermediate and final source/target indices
are checked by Lean throughout.

LogicalHeadRouting.square proves the actual exchange square at an arbitrary
tagged logical gap, independently for both operations through the common
side notation. It checks both consumed components and every fixed prefix/tail
tag. G.conjL_toHead and G.disjR_toHead give separately typed native rule equations:
the component exchanges occur below a fresh principal rule. The selected
conjunction theorem uses the left equation; no native rank-one value is assigned
to the original exchange wrapper. Equal A and B labels retain separate tags,
as explicitly checked in the public signature file.

The result closes the conjunction principal reduction equation needed after
rank-two classification. It does not close the dual disjunction reduction,
remaining parametric/blocked reductions, degree/rank induction or global cut
elimination. All earlier simultaneous clean normalization, predecessor descent,
atomic rank-two elimination and opposite structural commutations are reused.

## Verification and evidence

The pinned Lean 4.35.0 strict build and full transitive audit pass: 474 screened
Lean files and 11,403 project declarations. All five exact public type files
pass sequentially: PrincipalConjunction, PositionalCuts, CleanCuts, BlockedW and
Reducibility. The three audit and two presentation negative controls reject with
the required messages. Public source closure, v4/v5/v6/v7 manuscript hashes and
whitespace pass. Production remains Init-only, with no custom mathematical
axiom, proof hole, native_decide or new Gentzen constructor.

provenance/wsl-gentzen-principal-conjunction retains the 492-file checked-source
inventory, nine-module/declaration anchors, actual command exits, compressed
logs with raw/gzip hashes, five control sources/logs and final/type verification.
All failed implementation attempts for this phase are retained. The preceding
positional and v7 evidence remains unchanged. Local verification, author-side
reviews, independent kernel, Comparator, official preflight, service verification
and publication remain distinct statuses; only the stated local checks/reviews
were performed.

## Continuation, retention and delivery

Continue with the dual disjunction principal reduction, remaining same-side,
logical and binary commutations, and all seven BlockedL/seven BlockedR reductions.
Use strictly smaller degree for component calls with arbitrary returned rank;
use actual inherited cleanliness and smaller selected rank at unchanged degree.
Complete the all-ranks clean theorem before unrestricted cleaning at that degree,
then assemble topmost/global elimination and every later full-paper obligation.
Appendix C's concrete blocked gammaDisj and sequential disjunction reductions
remain open. The three milestones retain their separately recorded statuses.

Retain this report in docs/ and its two reviews in docs/reviews/. Deliver the
committed bytes to /mnt/c/Users/fleng/Downloads, preserving differing files.
The post-commit receipt records paths/hashes, all checked-versus-committed blobs,
local/origin/live SSH agreement, clean status and the unchanged stash:
.codex-work/gentzen-cut-elimination/PRINCIPAL_POST_COMMIT_DELIVERY.json.
