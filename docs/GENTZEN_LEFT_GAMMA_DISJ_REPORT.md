# Blocked left gamma-disjunction: local construction report

The actual BlockedL.gammaDisj reduction is proved through
`CutCommutation.blockedL_gammaDisj_rank_step`. All twelve binary branches and the
preceding four blocked reductions are preserved. Five blocked reductions are
complete; nine and the global inductions remain open. This is a local proof
milestone within the unchanged full-paper contract.

## Exact source and result

Let C, A and B be normal forms and let X, Y, Z, T, D, E, I and J be contexts.
Take f : ((X ++ C :: Y) ++ [A]) ⊢ D,
g : ((Z ++ C :: T) ++ [B]) ⊢ E, h : I ⊢ J and an exact selected tag z : At J C.
The source is the terminal disjunction-left macro followed by a two-copy left
contraction. `BlockedLeftDisj.gammaParent_source` identifies it with
`BlockedSource.left2 C X (Y++Z) (T++[A∨B]) (D++E)`, including the actual list
reindexings. The selected lower occurrence is the contraction's retained C,
before the fixed terminal A∨B. Extending the contraction retains that terminal
tag even when its formula equals C.

`gamma_equation` compares the original positional cut with `selectedParallel`
applied to the two original child positional cuts. Its exact output sequent is
((x.before [A∨B]).erase ++ I) ⊢ ((D++E) ++ z.erase), where x is the retained
contraction tag. The first child uses `gammaSecondRoute`, the second
`gammaFirstRoute`, preserving the established gammaBlock parameter order.
The reconstruction exchanges each terminal A/B past I, rebuilds the disjunction
macro, contracts the duplicated I and residual z.erase contexts, and restores
the terminal principal to its original position. No label-based identification
of positions is used.

## Equation derivation

The main derivation uses actual Reduced arrows, with comp p q applying p first.
`Splice.selected` moves an arrow on the selected formula to the other premise.
`ContractionSplice.mixed_diagonal` and `duplicate_output` calculate the diagonal
through the actual mixed disjunction map and the residual codiagonal.
`ContractionSplice.binary` then derives the two-copy contraction equation from
the completed principal conjunction equation, with explicit duplication of the
opposite input and merging of its residual output. This use of principal
conjunction is an arrow calculation; it makes no recursive call on C∧C.

`DoubleDisjSplice.first` commutes the first selected copy into f using the
completed disjL_right_first core. `second` commutes the second copy into g using
disjL_right_second and a proved intervening product-coordinate square. The two
input copies and residual output copies merge through `input_square` and
`output_square`. `DoubleDisjSplice.equation` gives the complete comparison.
`BlockedLeftDisj.canonical_equation` restores terminal A/B order, and
`shared_equation` allows arbitrary residual routes.

`TerminalFold.into_cons`, the terminal exchange component equations and
`terminalExchange_arrow` account for actual singleton folds, append maps and
all exchanges, including empty fixed contexts. `parallel_denote` and
`headParent_equation` specialize the native equation to actual Gentzen proofs.
`Route.selected_get_factor` and `selected_blocks_factor` prove equality of each
selected and retained position; terminal macro naturality then proves
`source_denote`. `selected_equation` explicitly transports the three residual
list equalities. `gamma_equation` instantiates the original contraction.

The checked auxiliary split comparison, projection and SplitPair modules are
preserved. They prove particular split epi/mono and coordinate statements, not
an isomorphism or general equality reflection. The completed canonical equation
also resolves the earlier retained full native diagram target; failed rewrite
attempts remain in the evidence as development failures.

## Original Clean, strict rank and Appendix C

`ContractionBlock.left_cut_descent` supplies full inherited Clean and strict
rank decrease for each original copy in the actual contraction premise.
`UnaryCast.exchangeL_right_cut_descent` and
`BlockedSource.disjLLast_right_first_descent` / `right_second_descent` traverse
the outer exchange, native disjL branch and child exchange. Strict inequalities
compose before any head adapter or reconstruction is introduced.

`gamma_first_descent` and `gamma_second_descent` prove, respectively,
rank(h,z,f,a.before[A]) < rank(h,z,gammaParent f g,x.before[A∨B]) and the
corresponding inequality for g/b.before[B]. C is unchanged, so the formula degree
is unchanged. The two ih applications in `blockedL_gammaDisj_rank_step` use
exactly h/z and the original f or g, with those Clean proofs and inequalities.
These actual source equations and rank statements close the concrete Lean
correspondence for Appendix C's p.260 (w gamma 3) correction r′ < r.
The distinct p.262 fresh-right-principal correspondence remains open.

`selectedParallel_count` proves the reconstruction has the sum of the two
returned cut counts. `selectedParallel_congr` transports their actual Reduced
equalities. `blockedL_gammaDisj_eliminated` first obtains a cut-free exact-output
reconstruction, then uses the completed structural atomization theorems to
produce an Atomized representative with the same equation. It assumes neither
output blockedness nor a bound on the returned proof's rank.

## Local verification and provenance

The public root exports the 32 new modules. `Checks/BlockedLeftDisj.lean` checks
the exact original source equation, source identity, both concrete strict
inequalities and instantiated rank-step signature. Four actual Eliminated
witnesses cover arbitrary signed literals, negative 0, Empty atom type with
constant formulas and empty gaps/opposite input, and populated same-label gaps.
A separate exact-index check retains a terminal principal equal in formula to C.
Sixteen focused malformed constructions are rejected, including the erroneous
identification of that fixed terminal tag with the contraction's retained copy.
Boundary suites contribute their five established controls. Strict build,
complete transitive dependency audit and every public check run sequentially;
command exits, exact counts and source hashes are recorded in
`provenance/wsl-gentzen-left-gamma-disj/FINAL_VERIFICATION.json` and linked logs.
No custom mathematical axiom, proof hole or native_decide is introduced.

The base is ecfe8da951f405c6ee5f2afe7c5ca7194d6b4eab. Successor 811eceeb and all
intervening work remain incorporated. Stash
dedfd8fc8cd49930e9a162d5be585215b062a43c is preserved. Checked sources are
archived with a SHA-256 manifest and compared again against committed Git bytes
before delivery. All nine manuscript blobs match the base, including v7 and
Appendix C; unchanged TeX was not rebuilt. Earlier delivery receipts persist.
Committed-byte conflict-preserving Downloads paths and copy hashes are recorded
in this phase's DELIVERY_REGISTER.json and DELIVERY_RECEIPT.json.

## Continuation

Next prove BlockedR.gammaConj, then the eight sequential logical blocked cases.
Preserve actual two/three-copy arities. For fresh logical principals, put routing
below the native rule and prove the selected leaf, one-sided rank one and full
Clean before its sequential cut. Then discharge constructor dispatch,
fixed-degree all-ranks Clean under strict DegreeBelow, simultaneous cleaning,
strong degree induction and arbitrary-G structural normalization. Export actual
unrestricted CutElimination and AtomizedCutElimination inhabitants, then continue
coherence, intended-presentation and uniform-substitution/congruence bridges,
both maximality routes, the model corollary and all three appendices. The three
milestones and complete paper remain distinct. Independent replay, Comparator,
official/service verification and publication have not been performed here.
