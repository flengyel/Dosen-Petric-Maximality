# Opposite logical cut commutations

The continuation after f4a8da3 proves the opposite conjunction-left and
disjunction-right commuting families at arbitrary selected gaps, with actual
cut-free atomized reconstruction and clean smaller-rank recursive steps.
Nine new production modules and Checks/OppositeLogicalCuts.lean are verified.

## Exact results and dependencies

CutCommutation.opposite_conjL proves equality in Reduced between the positional
cut of conjL F U f against g and PrefixedLogical.conjL applied to the child cut.
It preserves the exact source y.erase ++ (F ++ conj A B :: U) and target
Λ ++ x.erase. opposite_disjR proves the separately typed equality between the
positional cut against disjR F U g and SuffixedLogical.disjR applied to its child
cut; the exact target is (F ++ disj A B :: U) ++ x.erase. Both original selected
tags remain unchanged on the opposite side. No coherence or eliminator premise
occurs in either equation.

The two eliminated lemmas reconstruct cut-free atomized witnesses from the
corresponding child witnesses, preserving the same original sequent and Reduced
equality. opposite_conjL_descent and opposite_disjR_descent reuse the completed
selected-predecessor address inheritance: the actual child is clean and its
original selected-rank sum is strictly smaller. Both rank_step lemmas apply the
explicit strictly smaller-rank induction hypothesis to that child and rebuild.
They neither re-clean the child nor compare a routed native rank with the old rank.

prefixSide lifts an arbitrary side arrow through a fixed list prefix. Its join
and split squares use actual append comparisons, including their unit cases.
prefixSide_logical supplies the two list-association transports around the
original logical rule. PrefixedLogical.conjL/disjR use only native rules and these
transports; their denotation, cut-count and Atomized laws compile.

The suffix comparison is proved directly. DiagonalData.assocL_pentagon follows
from the already proved product-coordinate equations and is instantiated with
the actual side diagonal data and side_unit law. suffixLogicalSide_join/split
prove the full logical suffix diagram on both conjunction and opposite
disjunction sides, with every unit and association explicit. SuffixedLogical.disjR
then constructs the actual native rule used below cut. No uninstantiated
structural-coherence or quotient-duality input is substituted for these proofs.

The source correspondence is the opposite logical unary part of §11.2's
parametric commuting argument, printed p.255 onward in the retained
September-2007 source. The constructions use the actual current G presentation,
not an assumed diagram identity. Its retained PDF SHA-256 is
e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.

## Verification and limitations

The pinned Lean 4.35.0 strict build and complete transitive audit pass:
510 screened Lean files and 11,669 audited project declarations. Eight
exact public type files pass sequentially. They include both commuting equations,
both exact descent types, prefix/suffix comparison types, equal component labels
and a constant-only Empty atom-type instance. All three audit and two presentation
negative controls reject as expected. Public import closure, v4/v5/v6/v7 manuscript
hashes and whitespace pass. The source remains Init-only and adds no primitive
G constructor, custom mathematical axiom or proof hole.

provenance/wsl-gentzen-opposite-logical-cuts retains the checked-source inventory,
module/declaration anchors, actual command exits, every failed implementation
attempt, compressed logs with raw/gzip hashes, five control sources/logs and
final/public-type evidence. Earlier source, checks, reports and evidence remain
preserved. Local build/audit and author-side reviews do not supply independent
kernel, Comparator, official preflight, service or publication status.

The same-side logical and binary commutations, fourteen blocked families,
complete constructor dispatcher and all-ranks/degree/global induction remain
open. DegreeBelow remains the strict outer induction hypothesis. Full-paper
formalization is incomplete. All intended-category, coherence, substitution,
maximality, model and appendix obligations continue under the existing contract.
Appendix C's concrete blocked reductions remain open; the authorized v7 appendix
and all preserved manuscript bytes, diagrams and disclosure remain unchanged.

## Retention and delivery

Retain this report in docs/ and both reviews in docs/reviews/. Deliver their
committed bytes to /mnt/c/Users/fleng/Downloads with conflict preservation and
byte verification. The post-commit receipt records exact paths/hashes, all
checked-versus-committed sources, local/origin/live SSH agreement, clean status
and the unchanged stash:
.codex-work/gentzen-cut-elimination/LOGICAL_POST_COMMIT_DELIVERY.json.
