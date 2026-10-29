# Three source-shaped blocked cut reductions

BlockedL.gammaMix, BlockedR.gammaMix and BlockedL.gammaConj now have actual
Reduced equations, exact-output reconstructions, eliminated witnesses and
instantiated original-rank steps. All twelve binary commutations remain proved.
Eleven blocked reductions, global induction and the full-paper endpoint remain open.

## Source and preserved scope

This phase continues cf3741a / 26e6d8d after incorporation of successor
811eceebf9991640cf9dcd3923925f75235d4199. Every preceding proof, committed delivery
receipt and stash dedfd8fc8cd49930e9a162d5be585215b062a43c is preserved. G syntax,
generating equations, rho, BlockedL/R, descendant quantifiers and dependency pins
are unchanged. No unrelated checkout is modified.

Twenty production modules contain 103 source declarations. Exact names, hashes,
lengths and line anchors are retained in the evidence register. The construction
uses actual quotient-arrow equations in Reduced, for arbitrary P, without
Nonempty or DecidableEq assumptions.

## Concrete construction

| Source family | Equation | Instantiated rank step |
| --- | --- | --- |
| BlockedL.gammaMix | BlockedMix.gamma_equation | CutCommutation.blockedL_gammaMix_rank_step |
| BlockedR.gammaMix | BlockedMix.gamma_right_equation | CutCommutation.blockedR_gammaMix_rank_step |
| BlockedL.gammaConj | BlockedConj.gamma_equation | CutCommutation.blockedL_gammaConj_rank_step |

BlockedMix.gammaBlock has exactly two selected copies. Its positions agree with
the native reversed mix blocks. gammaParent_source and gammaRightParent_source
identify the derived parents with the actual BlockedSource.left2/right2 terms;
BlockedConj.gammaParent_source identifies the actual conjunction parent with the
opposite block order. These are proof equalities, rather than graph comparisons.

Both selected tags map to the contracted tag. Each remaining child tag maps to
a remaining parent tag. selectedResidual and selected_factor prove the exact
head/residual factorization, including equal-labelled fixed positions. The
fixed-tag proofs use positional indices and retain_ne, preserving every occurrence.

The parallel builders receive two actual cut results, apply G.mix or G.conjR,
and realize duplicated fixed-context repairs by finite StructuralPrograms. These
programs include whole-block contraction even when a block is empty. Their
product/coproduct fold squares are proved. The completed cut-free reconstruction
is atomized using the accepted structural atomization theorem, preserving its
exact output and Reduced denotation. No output blockedness or returned-rank bound
is asserted.

The mix core uses the proved union decomposition and splice naturality. The
conjunction core factors both child cuts through one common splice kernel. Its
lifted_pair equation is proved by the two coproduct injections. The selected
summand uses mixedDisj naturality; the residual summand uses mixedDisj_inr and
diag_mix_codiag. Its final associator is explicit. No coherence theorem, supplied
diagram, general duality, graph reflection or assumed normalizer is invoked.

ContractionBlock.left_cut_descent/right_cut_descent inherit full Clean through the
actual contraction predecessor. The appropriate native binary descent then gives
strict original-child rank decrease by transitivity. Both recursive calls have
the original unchanged opposite premise. They occur before every head exchange,
fixed-context duplication and residual repair. These three handlers discharge
all their internal diagram and reconstruction hypotheses; their strict rank
induction hypothesis remains explicit until the global dispatcher is proved.

## Local verification

Pinned Lean 4.35.0 is used with warnings as errors. The strict build and transitive
axiom audit pass for 631 screened Lean files and 12,384 project declarations. The
public check expands all three equation and rank-step types. Twelve actual
eliminated-witness instances cover the three families with uniform signed
literals, an explicit repeated negative literal, constant-only data over Empty,
and nonempty repeated-label fixed blocks. All seventeen public check files, full source closure and the five established
plus twelve focused controls pass; FINAL_VERIFICATION.json records their actual
commands and exits. The three added controls reject omitted
parallel input contraction, omitted output contraction and collapse of an
unselected equal-labelled fixed tag.

All commands, actual exits, development failures and compressed raw logs are
retained under provenance/wsl-gentzen-blocked-cuts/. Failed development attempts
included associator grouping, opposite-category/fold aliases and context split
inference. Two public-check attempts read the earlier file before its regeneration
completed; they exposed missing local namespaces and implicit context splits.
The corrected checks name both explicitly and pass after regeneration. These
failures are separate from expected negative controls. One heavy command runs at
a time under the repository lock. This phase adds no lock rejection.

The hostile-referee and mathematical-writing reports are local author-side
reviews of this actual argument and correspondence map. They do not constitute
independent peer review, independent kernel replay, Comparator, official/service
verification or publication.

All nine manuscript blobs are unchanged from 26e6d8d. V7 and its authorized
Appendix C remain current, preserving older versions and all diagrams. No new
manuscript defect was established; unchanged TeX is not rebuilt. Appendix C's
p.260 gamma-3 and p.262 fresh-right-rank-one correspondences remain open.

## Continuing obligations and delivery

Next construct BlockedL.gammaDisj from its actual disjLLast source, preserving its
terminal principal and actual exchanges. Complete the other ten blocked cases,
including the three-copy cases. Then discharge the complete constructor dispatcher,
fixed-degree all-ranks clean theorem, arbitrary premise cleaning, strong degree
induction and arbitrary-G normalization. Actual unrestricted CutElimination and
AtomizedCutElimination inhabitants are still required. Continue coherence,
intended-presentation/substitution/congruence bridges, both maximality routes,
model corollary and every claim in all three appendices. The three milestones and
the complete-paper endpoint remain separate.

New reports/reviews, changed records and technical evidence are delivered from
committed bytes. DELIVERY_REGISTER.json records exact repository/Downloads paths,
source commit, SHA-256 and byte comparisons. Differing existing Downloads files
are preserved with commit-suffixed filenames. Earlier receipts, including the
three 811eceeb successor deliveries and the 17-entry disjL register, remain complete.
