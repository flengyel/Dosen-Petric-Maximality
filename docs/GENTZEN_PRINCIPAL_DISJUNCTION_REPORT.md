# Principal disjunction reduction and the rank-two degree step

The continuation after dff2994 proves the actual principal disjunction reduction
at every selected gap and both principal branches of the strict degree induction.
Sixteen new production modules and Checks/PrincipalDisjunction.lean are verified.
The v7 errata appendix, intervening source work and existing stash are preserved.

## Exact mathematical results

For arbitrary P, f : G P Γ (F ++ A :: B :: U), g : G P (A :: Θ) Λ and
h : G P (B :: Ξ) Ω, PrincipalDisjunction.selected_equation proves equality in
Reduced of their positional principal disjunction cut and selectedReduction f g h.
Both have source (Θ ++ Ξ) ++ Γ and target
(Λ ++ Ω) ++ erase(At.shift F (here (disj A B) U)). The reduction first cuts B,
then moves the surviving A tag to the second cut. Its cut count is the sum of
the original three counts plus two. Its Atomized predicate is equivalent to
f.Atomized ∧ g.Atomized ∧ h.Atomized. Each component formula has strictly smaller
degree. The equation has no coherence, normalizer or cut-eliminator premise.

PrincipalConjunction.degree_step and PrincipalDisjunction.degree_step construct
actual cut-free atomized witnesses, assuming only DegreeBelow at the compound
formula's degree and CutFree of the three original premises. DegreeBelow is the
explicit outer induction hypothesis: head cuts on strictly smaller degrees,
at arbitrary ranks. Each proof obtains the inner cut-free witness before applying
the hypothesis to the outer cut. No returned-rank inequality is assumed.
PositionalCut.rank_two_degree_step combines these constructions with the completed
atomic elimination and exhaustive classification. It covers all selected
rank-two cuts under that same strict outer induction hypothesis.

DegreeBelow has not been discharged globally. These conditional induction
branches do not prove CutElimination or AtomizedCutElimination. All remaining
parametric and fourteen blocked families, the all-ranks clean theorem and the
outer degree/global induction remain to be assembled. The three maximality and
full-paper milestones retain their separate recorded statuses.

## Construction and correspondence

MirrorCalculus interprets the required diagram equations in the opposite Reduced
category, reindexing objects by the involution mirror and reversing both the
connective and binary order. Its composition, tensor, associativity, naturality,
projection and distribution laws are proved from the existing Reduced laws.
This supplies no assumed operation on quotient arrows. The reflected product
argument is replayed with checked types. MirrorInterpretation.mixed_source proves
that its mixed comparison is the actual Rules.sourceConj; splice_native identifies
its splice with an ordinary cut splice and explicit swaps.

PrincipalDisjunction.reflected_equation and equation then give the original
quotient-category diagram. DiagonalData.dual_inner_route/dual_outer_route are
proved from the existing product laws, with side_unit and side_swap_snd supplying
their law arguments in the intended interpretation. No new law field is left
uninstantiated. HeadRouting.front_arrow, front_split and front_singleton prove
the exact exchange comparisons, including every prefix, selected and tail tag.
split_assoc_inverse checks both context sides and their inverse association.
PrincipalDisjunction.rule_equation instantiates the diagram with actual G rules;
selected_equation reuses the completed logical-head transport below a fresh rule.

The source §11.2 p.255 describes the disjunction principal case by analogy after
the conjunction construction on pp.254–255. The native B-then-A disjunction
construction is a directly proved reduction at the original sequent. It does not
claim an unproved quotient duality or literal equality with an unwritten source
display. The earlier conjunction A-then-B/source-order distinction is preserved.
The primary September-2007 source was consulted at these pages; its retained PDF
has SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.

## Verification and retained evidence

The pinned Lean 4.35.0 strict build and full transitive audit pass: 491 screened
Lean files and 11,561 audited project declarations. Six exact public checks pass
sequentially: PrincipalDisjunction, PrincipalConjunction, PositionalCuts, CleanCuts,
BlockedW and Reducibility. Repeated equal labels remain distinct selected tags;
constant-only Empty atom types are included in the exact checks. All three audit
and two presentation negative controls reject as required. Public import closure,
v4/v5/v6/v7 manuscript SHA-256 checks and whitespace pass. Production remains
Init-only with no new primitive rule, custom mathematical axiom or proof hole.

provenance/wsl-gentzen-principal-disjunction retains the checked-source inventory,
module/declaration anchors, actual command exits, compressed logs and their raw
and compressed hashes, all five control sources/logs and final/type evidence.
Every nonzero implementation build for this phase is retained. One initial
sandbox log-write attempt started no Lean process; its retry used the approved
runner and retained the actual build result. Prior evidence is preserved.

Local build/audit, author-side hostile and writing reviews, independent kernel,
Comparator, official preflight, service verification and publication remain
separate statuses. Only the stated local checks and author-side reviews were done.

## Continuation and delivery

Reuse both principal equations, both conditional degree branches and the complete
rank-two step. Continue the remaining same-side structural, logical and binary
commutations and all seven BlockedL/seven BlockedR families. At unchanged degree,
use inherited cleanliness and a proved strictly smaller original selected rank.
At smaller degree, use arbitrary returned ranks. Complete the clean theorem for
all ranks before unrestricted cleaning at that degree. Then prove global
elimination, coherence and every remaining full-paper bridge, construction and
appendix identity. Appendix C's concrete gammaDisj and sequential blocked
reductions remain open; the authorized manuscript addition itself is complete.

Retain this report in docs/ and both reviews in docs/reviews/. Deliver their
committed bytes to /mnt/c/Users/fleng/Downloads, preserving differing destination
files. The post-commit receipt records exact paths/hashes, checked-versus-committed
source bytes, local/origin/live SSH agreement, clean status and the unchanged stash:
.codex-work/gentzen-cut-elimination/DISJUNCTION_POST_COMMIT_DELIVERY.json.
