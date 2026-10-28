# Structural cut commutations at exact selected positions

The continuation after ef25f48 proves both same-side structural commuting
families, their cut-free reconstruction and their clean selected-rank induction
steps. It extends the opposite structural equations to arbitrary selected gaps.
Eight new production modules and Checks/StructuralCuts.lean are verified.

## Mathematical construction and scope

At.remove deletes a selected tag while retaining the type and order of every
other tag. retain_remove, remove_retain and formula_eq establish its exact ordinal
meaning. Route.tabulate realizes an arbitrary typed map of tags. Route.SingleFiber
requires that the selected lower tag have precisely one upper preimage; uniqueness
is stated for ordinal coordinates across all formula labels. Route.residual deletes
that fiber. residual_get and residual_square prove its exact component map and
head-routing diagram, on both product and opposite coproduct sides.

StructuralProgram.route records the existing program's get map; route_arrow proves
its actual arrow. residual realizes the deleted map by existing structural rules.
CutCommutation.same_right/same_left are independently typed Reduced equalities
between the original positional cut and the smaller selected cut with an explicit
residual program below it. The result has the original sequent, including all
fixed contexts. exchange_singleFiber covers every exchange position, including
empty blocks. thin_singleFiber covers every old thinning position.
contract_singleFiber covers every position other than the contracted lower tag,
using the already proved fixed-copy correspondence. Equal labels remain separate.
The selected lower contraction itself is excluded from this parametric family.

same_right_eliminated/same_left_eliminated replace the child cut by its actual
cut-free witness, apply the residual structural program, and atomize the resulting
cut-free proof. This final use of the existing atomizer imposes no claim about
blockedness or rank of its output; that output is not a recursive subcut here.
The original child, before any residual reconstruction or atomization, receives
the recursive call. The earlier atomization counterexample and simultaneous
clean-cut construction remain unchanged.

StructuralProgram.leftAddress/rightAddress construct the actual proof address
under each program. Their ascent equations recover get on the same side and the
unchanged tag on the opposite side. Address length is exactly steps: identity and
equality transport add zero, every actual exchange/thinning/contraction adds one.
Nonempty programs therefore give strict original selected-rank descent. The
existing address-based CutFree, Atomized and AllBlockedAt inheritance supply the
same child's complete cleanliness. same_right_rank_step/same_left_rank_step apply
the explicit smaller-rank induction hypothesis to that exact child, then rebuild.
They do not clean an unchanged-degree child or substitute its routed native rank.

selected_opposite_left/right extend the completed head-only structural equations
to arbitrary selected positions. Their two descent lemmas provide cleanliness
and strict selected-rank decrease for nonempty programs. All equations are proved
from existing Reduced, product, splice and context-comparison laws. No primitive
G rule, coherence premise, arbitrary arrow inverse or unwitnessed zero is added.

This closes the same-side structural commuting construction and its recursive
obligations, and arbitrary-position opposite structural equations/descent. The
overall constructor dispatcher, logical/binary commutations, fourteen blocked
families and the all-ranks/degree/global induction remain open. Both principal
equations and the conditional exhaustive rank-two step are reused unchanged.
DegreeBelow has not been discharged. The full-paper endpoint is not complete.

## Verification, preservation and delivery

The pinned Lean 4.35.0 strict build and full dependency audit pass: 500 screened
Lean files and 11,626 audited project declarations. Seven exact public type files
pass sequentially, from StructuralCuts through the preceding Reducibility check.
The checks include arbitrary formula universes, equal fixed/contracted labels,
three contracted copies and a real empty exchange over Empty. All three audit
and two presentation negative controls reject as expected. Public source closure,
all v4/v5/v6/v7 manuscript hashes and whitespace pass. Production remains Init-only.

provenance/wsl-gentzen-structural-cuts retains the checked-source inventory,
module/declaration anchors, actual command exits, every failed build attempt,
compressed logs with raw/gzip hashes, five control sources/logs and final/type
verification. Noncomputable address definitions use the structural recursor;
Lean's initial executable-code-generation failure is retained with its correction.
All earlier production and exact-check bytes, manuscript artifacts and the
existing stash are preserved. Local checks and author-side reviews supply no
independent kernel, Comparator, official preflight, service or publication status.

Continue with the remaining logical and binary families and all blocked cases,
then the all-ranks clean theorem, strict degree induction and global elimination.
Keep the three full-paper milestones distinct and all subsequent intended-model,
coherence, substitution, maximality and appendix obligations active. Appendix C's
concrete gammaDisj and sequential blocked reductions remain open; its authorized
manuscript addition is already complete.

Retain this report under docs/ and both reviews under docs/reviews/. Deliver the
committed report bytes to /mnt/c/Users/fleng/Downloads with conflict preservation
and byte verification. The post-commit receipt compares every checked source,
local/origin/live SSH refs, clean status and the unchanged stash:
.codex-work/gentzen-cut-elimination/STRUCTURAL_POST_COMMIT_DELIVERY.json.
