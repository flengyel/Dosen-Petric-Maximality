# Blocked right gamma-disjunction reduction

BlockedR.gammaDisj now has an actual source equation, an exact-output two-cut
reconstruction, an eliminated witness and an instantiated original-rank step.
Together with the three preceding reductions, four of fourteen blocked families
are proved. Ten blocked reductions, global induction and the full-paper endpoint
remain open. All twelve binary commutations are preserved.

## Source and scope

This phase continues b95abc6 / f04b638, after incorporation of successor
811eceebf9991640cf9dcd3923925f75235d4199. The existing stash
dedfd8fc8cd49930e9a162d5be585215b062a43c, predecessor results and deliveries are
preserved. Thirteen production modules contain 67 source declarations. Exact
names, line anchors and source hashes are retained in
provenance/wsl-gentzen-blocked-disj/. The theorems quantify over arbitrary P;
no Nonempty or DecidableEq assumption is added. G, its equations, rho, blocked
predicates, descendant quantifiers and dependency pins are unchanged.

## Construction and correspondence

| Layer | Declaration | Mathematical role |
| --- | --- | --- |
| Particular reflected diagram | BlockedDisj.right_shared_splice; head_right_shared_splice | Shares the unchanged right premise across the two original children |
| Terminal folds | TerminalFold.out/into; toTail_eq/toHead_eq | Retains the singleton terminal unit and exact rotation, including empty contexts |
| Actual source denotation | TerminalFold.disjLLast_denote | Expands all three source exchanges and the native disjL constructor |
| Context repair | BlockedDisj.parallelInput_square; parallel_denote | Duplicates the right premise's input context and merges its output context |
| Native reconstruction | BlockedDisj.headParent_equation | Proves equality of the actual parent cut and the two-cut reconstruction |
| Arbitrary tags | BlockedDisj.source_denote; gamma_equation | Uses selected_factor at both original tags and every retained fixed position |
| Source identity | BlockedDisj.gammaParent_source | Identifies the parent with the existing BlockedSource.right2 term |
| Recursive step | CutCommutation.blockedR_gammaDisj_rank_step | Instantiates both original-child Clean/rank induction calls |

The particular reflected calculation is proved in MirrorCalculus using concrete
opposite arrows. Its lifted_pair proof checks the two coproduct injections,
including the residual branch's mixedDisj_inr and diag_mix_codiag laws. Expanding
those definitions gives right_shared_splice in the original Reduced category.
This construction does not require a general duality of G or of its quotient.

The source has f : F++[A] ⊢ X++C::Y and g : U++[B] ⊢ Z++C::T. Its conclusion is
(F++U)++[A∨B] ⊢ gaps[X,Y++Z]++C::T. The contraction is gammaBlock C Z T X Y:
the first child uses gammaSecondRoute and the second uses gammaFirstRoute.
The route order follows the actual source output, while the existing gammaBlock
is defined in native reversed-mix order. Both selected tags map to keep. Every
other tag is retained through selectedResidual and selected_factor.

The reconstruction takes the two actual cut results, reassociates each input,
applies disjLLast, and uses StructuralPrograms to repair both duplicated fixed
contexts. Its input program leaves the terminal principal in its own tagged
position. TerminalFold.child_into proves the child fold square; parallel_denote
then combines that square with sourceConj naturality and the proved right output
square. The native splice identity supplies headParent_equation. No graph
comparison, supplied diagram or coherence theorem replaces these equations.

ContractionBlock.right_cut_descent first descends through the actual contraction.
BlockedSource.disjLLast_left_first_descent/left_second_descent descend through the
outer input exchange, native disjL and the appropriate child input exchange.
Every stage inherits full Clean and strictly reduces the original selected rank.
The rank step calls ih f firstTag h z and ih g firstTag h z before introducing
head-routing adapters. Both calls use the unchanged h. It requires no bound on
the rank of the returned proof. The finished cut-free reconstruction is atomized,
preserving its exact output and Reduced equation.

## Verification and review

Pinned Lean 4.35.0 strict verification and the transitive axiom/source audit pass.
FINAL_VERIFICATION.json records actual counts, commands, exits and hashes.
All eighteen public check files pass. The new file checks the exact equation and
rank-step types and four actual eliminated witnesses: uniform signed literals,
an explicit negative literal, constants over Empty with empty fixed contexts,
and populated equal-labelled input/output blocks. Five established controls and
fifteen focused controls reject as expected. The three new focused controls
reject omission of either terminal reconstruction contraction and collapse of the
terminal principal tag with an equal-labelled fixed tag.

Development failures are retained separately from expected rejections. They
included associator grouping, opposite-category aliases, redundant tactics and
implicit constant-context inference. The last issue was resolved by specifying
the empty context splits in the concrete public witness. One heavy command runs
at a time. No failed command or unavailable review is represented as successful.

The linked hostile and mathematical-writing reports review this actual source
and correspondence map as local author-side work. Independent kernel replay,
Comparator, official/service verification and publication remain unperformed.
All nine manuscript blobs match f04b638; v7, the authorized Appendix C, preserved
versions and diagrams are unchanged. No new manuscript defect was established,
and unchanged TeX was not rebuilt. Appendix C's left gamma-3 and fresh-right-rank-one
Lean correspondences remain open; this right gamma-disjunction theorem does not
close either row.

## Continuation and delivery

Continue BlockedL.gammaDisj and BlockedR.gammaConj, then the eight sequential
logical blocked cases, preserving two/three-copy multiplicities, native fresh
principals and every original-rank/Clean requirement. Discharge complete
constructor dispatch, fixed-degree all-ranks clean elimination, arbitrary premise
cleaning, strong degree induction and arbitrary-G normalization. Actual
unrestricted CutElimination and AtomizedCutElimination inhabitants are required.
Continue coherence, intended presentation and substitution/congruence bridges,
both maximality routes, the model corollary and every v7 appendix claim under the
unchanged full-paper contract. The three milestones remain distinct.

Reports, reviews, changed records and technical evidence are delivered from
committed bytes. DELIVERY_REGISTER.json records exact repository and Downloads
paths, commit and SHA-256 values. Differing existing files retain their bytes;
new deliveries use commit suffixes where necessary. All earlier receipts,
including the three 811eceeb files, remain effective.
