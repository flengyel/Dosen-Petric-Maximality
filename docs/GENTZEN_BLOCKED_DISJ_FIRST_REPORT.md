# BlockedL.disjunctionFirst and Appendix C p.262

`CutCommutation.blockedL_disjunctionFirst_rank_step` proves the actual sequential
first-disjunction blocked case. All twelve binary branches and nine of fourteen
blocked families are proved. Both concrete Appendix C erratum correspondences
are now proved. Five blocked families, global induction, unrestricted elimination
and the full-paper endpoint remain open; the three milestones stay distinct.

## Original source and exact result

Let A,B be normal forms, C=A∨B, and X,Y,Z,D,E,I,J lists. The original children
are f:G ((X++C::Y)++[A]) D and g:G (Z++[B]) E. The unchanged opposite premise
is h:G I J with z:At J C. BlockedDisjFirst.parent_source identifies the actual
left2 contraction on BlockedSource.disjLLast f g, with its exact association
transports. It contracts the parametric C in f with the terminal fresh C and
retains the last selected copy. The result is precisely
`G (block.keep.erase++I) ((D++E)++z.erase)`.

The two selected Cs and any fixed equal-labelled formulas remain different
tags. Empty contexts and atom types, signed literals and repeated labels add
no assumptions. Composition applies its first argument first.

## Actual native and selected equations

Terminal head/tail script identities, principal_factor_cast and
terminal_source_denote normalize the source to the existing native disjL
construction. firstChild moves the parametric C behind A; child moves that C
to the selected head for the first cut. first_get/second_get/first_fixed compare
the original contraction tags. rawResidue and residue record the exact erased
list comparison. selected_body and selected_parent prove the full source lift;
no general graph reflection or proof duality is used.

The native parent contracts the two leading Cs in
`front [C] (F++U) C .left (G.disjL f₀ g₀)`. The completed binary contraction
equation and the existing disjRightFirstNative_equation first give the child
cut and its binary reconstruction. That reconstruction has input and output
exchange adapters above a fresh disjL. SequentialAdapters.left_equation moves
both adapters through the second cut using the existing unique-fiber and
opposite-side structural equations. The recursive cut is therefore made on
literal `G.disjL k g₀`, before those adapters and duplicate-context repairs.

SequentialDisjFirst.native_equation and BlockedDisjFirst.source_equation prove
the actual Reduced equalities, not only count/rank estimates. rebuild realizes
the complete repair with existing StructuralPrograms; count and congruence laws
are proved. Equality reindexing accounts for every erased-list association.

## Both original-rank calls and the erratum

original_descent crosses the original selected contraction and actual terminal
disjLLast first-child path. It gives all six Clean facts and strict original
rank for f at parametric.before [A], with unchanged h/z. The first ih occurs
there, before routing. Existing structural replacement plus selected_child
adapts the returned cut-free atomized witness. The untouched second child is
proved cut-free and atomized from original Clean.

fresh_clean_and_rank proves full Clean for the next cut on native G.disjL k g₀.
Its principal is a leaf, independently of the returned k's rank. The second ih
has the unchanged opposite rank plus one, strictly below the original contracted
rank. Both calls are instantiated in blockedL_disjunctionFirst_rank_step.
Rebuild preserves cut-freeness; final G.atomize gives Atomized and the actual
equation at the original exact output, without output blockedness/rank promises.

This is the concrete source case corresponding to the book's printed p.262.
In Lean the right cut premise's selected antecedent has `rho .left = 1`;
“right rank” names its role as the right premise, not SequentSide.right.
BlockedDisjFirst.fresh_principal_rank proves that one-sided equality.
fresh_total_rank proves total rank `h.rho .right z+1`, and
fresh_total_rank_ge_two proves it is at least two. The actual source equation,
original descent, fresh full Clean and final rank step discharge the adapters
and sequential-instance correspondence. The source disjLLast wrapper itself
is not assigned native rank one. Positive checks show its terminal principal
rank is two in the empty example; a negative control rejects rank one there.
The total-rank-one error is independently rejected.

Appendix C p.260 stays proved by the earlier gammaDisj source equation and both
strict descents. Both correction rows are reconciled across all live records.
No new manuscript defect was found. All nine manuscript blobs are unchanged;
unchanged TeX is not rebuilt.

## Verification, reviews and delivery

Twelve new modules contain 60 source declarations. The pinned Lean 4.35.0 strict
build, 739-file source screen, transitive audit, all 23 public check files and
31 expected rejections are recorded with actual exits in
provenance/wsl-gentzen-blocked-left-disj-first/FINAL_VERIFICATION.json.
Exact public signatures check source, original descent, fresh full Clean/rank,
all three concrete Appendix C declarations and the final rank step. Four actual
Eliminated smoke witnesses use terminality with witnessed bottom-tail children;
they cover signed literals, negative zero, Empty/constants and populated repeated
X/Y/Z. They do not pretend to instantiate an unavailable global ih. The general
source/rank proofs check the construction itself.

Only propext, Classical.choice and Quot.sound are permitted by the complete
dependency audit. Proof-development failures and actual logs remain separate
from expected negative controls. The source archive is read back and verified,
then checked against committed bytes for delivery. Both required reviews are
local author-side reviews of the actual argument/map. Independent replay,
Comparator, official/service checks, independent peer review and publication
were not performed. The existing stash and all prior receipts are preserved.

Reports, reviews and changed records are delivered from committed bytes to
Downloads with conflict-preserving filenames and byte comparisons. Exact paths,
hashes and any failure are retained in DELIVERY_REGISTER.json.

The current rank-error controls normalize the proved rho formulas before their
false numerical equalities are rejected. Two retained returned-rank controls
are strengthened in this run; historical checkpoint evidence remains unchanged.

## Continuation

Complete BlockedL.disjunctionSecond/Both and
BlockedR.conjunctionFirst/Second/Both, preserving two/three-copy arities,
original Clean/ranks before adapters, fresh native principals and final
structural atomization. Discharge constructor/tag dispatch, fixed-degree
all-ranks Clean under strict DegreeBelow, arbitrary-premise cleaning, strong
degree induction and arbitrary-G normalization. Export actual unrestricted
CutElimination/AtomizedCutElimination, then continue coherence, intended-
presentation and uniform-substitution/congruence bridges, both maximality routes,
the model corollary and every claim in all three v7 appendices.
