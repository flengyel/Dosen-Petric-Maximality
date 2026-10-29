# Selected cut constructor and tag coverage

Current construction incorporates 811eceeb. All twelve binary branches and all
fourteen blocked families are proved. Both parametric and blocked dispatchers,
the complete classification, nested rank/degree induction and arbitrary-proof
normalization now supply actual unrestricted CutElimination P and
AtomizedCutElimination P inhabitants. Current report: GENTZEN_CUT_ELIMINATION_REPORT.md.
Both Appendix C rows remain proved; original ranks are measured before adapters.

| Root and selected region | Left cut premise | Right cut premise |
| --- | --- | --- |
| Atomic leaves and rank-two clean cuts | Existing atomic/exhaustive rank-two results | Existing atomic/exhaustive rank-two results |
| Cut root | Excluded by Clean cut-freeness | Excluded by Clean cut-freeness |
| Opposite exchange/thinning/contraction | Equation, descent and elimination/rank-step wrappers checked | Equation, descent and elimination/rank-step wrappers checked |
| Same-side exchange/thinning/contraction, unique predecessor | Existing single-fiber equations, reconstruction and rank steps | Existing single-fiber equations, reconstruction and rank steps |
| Same-side thinning, fresh selected tag | Leaf case in clean_rank_step; rank-two degree step when both sides are leaves | Leaf case in clean_rank_step; rank-two degree step when both sides are leaves |
| Same-side contraction, selected copy cluster | all seven BlockedR families complete, including the three-copy conjunctionBoth case | all seven BlockedL families complete, including the three-copy disjunctionBoth case |
| Unary logical, opposite side | conjL equation, reconstruction and rank step checked | disjR equation, reconstruction and rank step checked |
| Unary logical, same-side prefix | disjR before equation, reconstruction and original-rank step checked | conjL before equation, reconstruction and original-rank step checked |
| Unary logical, same-side suffix | disjR tail equation, reconstruction and original-rank step checked | conjL tail equation, reconstruction and original-rank step checked |
| mix, first child tag | Equation/reconstruction and instantiated rank step checked (BinaryMix.firstRaw/first_equation; mix_left_first_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryMix.rightFirstAt/rightFirstAt_equation; mix_right_first_rank_step) |
| mix, second child tag | Native equation/reconstruction and instantiated rank step checked (BinaryMix.leadingAt; mix_left_second_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryMix.secondRaw/second_equation; mix_right_second_rank_step) |
| conjR, first child parametric tag | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRLeftFirst/conjRLeftFirst_equation; CutCommutation.conjR_left_first_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightFirst/conjRRightFirst_equation; CutCommutation.conjR_right_first_rank_step) |
| conjR, second child parametric tag | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRLeftSecond/conjRLeftSecond_equation; CutCommutation.conjR_left_second_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightSecond/conjRRightSecond_equation; CutCommutation.conjR_right_second_rank_step) |
| disjL, first child parametric tag | Equation/reconstruction and instantiated rank step checked (DisjLogical.disjLLeftFirst; disjL_left_first_rank_step) | Equation/reconstruction and instantiated rank step checked (DisjLogical.disjLRightFirst; disjL_right_first_rank_step) |
| disjL, second child parametric tag | Equation/reconstruction and instantiated rank step checked (DisjLogical.disjLLeftSecond; disjL_left_second_rank_step) | Equation/reconstruction and instantiated rank step checked (DisjLogical.disjLRightSecond; disjL_right_second_rank_step) |
| Fresh principal conjR / conjL pair | Existing conjunction A-then-B degree step | Same pair |
| Fresh principal disjR / disjL pair | Existing disjunction B-then-A degree step | Same pair |

The four same-side unary branches are implemented in
GentzenSameSideLogicalPrefix/Tail/Replacement/Descent. Their actual deletion
squares are LogicalDeletion.before_square and tail_square. They are not
instances of the structural SingleFiber residual theorem.

MixCalculation supplies eight concrete tensor/union, mix/union, splice/union and
native-mix equations. Native mix keeps its reversed child blocks. These inputs
are checked; four mix branches now have actual equations/reconstructions/rank steps;
all four conjR and all four disjL branches are complete; all twelve binary cases are proved.
The eight algebraic inputs are recorded in GENTZEN_MIX_UNION_REPORT.md and
provenance/wsl-gentzen-mix-union/. The four completed mix reductions are recorded
in GENTZEN_BINARY_MIX_CUTS_REPORT.md and provenance/wsl-gentzen-binary-cuts/.

All eight logical reconstructions preserve retained A/B and selected C as
separate tags. Their exact equations and count/Atomized/congruence laws are
proved. All earlier native/selected candidates are resolved. Current evidence:
provenance/wsl-gentzen-disjl-cuts/. Actual sourceConj/disjPair symmetries and
particular reflected diagrams are proved; no general G/arrow duality is assumed.
The fourteen completed blocked families have separate actual contraction/source
proofs; parametric commutation alone does not supply them.

| Blocked constructor family | BlockedL | BlockedR |
| --- | --- | --- |
| gammaMix | Actual source equation/reconstruction; blockedL_gammaMix_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaMix_eliminated/rank_step |
| gammaConj | Actual source equation/reconstruction; blockedL_gammaConj_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaConj_eliminated/rank_step |
| gammaDisj | Actual source equation/reconstruction; blockedL_gammaDisj_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaDisj_eliminated/rank_step |
| conjunction / disjunction | Actual source_equation, reconstruction and blockedL_conjunction_rank_step | Actual source_equation, reconstruction and blockedR_disjunction_rank_step |
| disjunctionFirst / conjunctionFirst | Actual source_equation, fresh full Clean/rank and blockedL_disjunctionFirst_rank_step; Appendix C p.262 closed | Actual source_equation, fresh full Clean/rank and blockedR_conjunctionFirst_rank_step |
| disjunctionSecond / conjunctionSecond | Actual source_equation, fresh full Clean/rank and blockedL_disjunctionSecond_rank_step | Actual source_equation, fresh full Clean/rank and blockedR_conjunctionSecond_rank_step |
| disjunctionBoth / conjunctionBoth | Actual left3 source_equation, both original descents, fresh full Clean/rank and blockedL_disjunctionBoth_rank_step | Actual right3 source_equation, both original descents, fresh full Clean/rank and blockedR_conjunctionBoth_rank_step |

The paired names give BlockedL / BlockedR constructors. Actual source/native
adapters are proved for all six gamma entries, both unary logical entries and
all three BlockedL disjunction entries and all three BlockedR conjunction entries.
All fourteen local blocked reductions are proved and instantiated by the two
complete blocked dispatchers and global induction. Neither blockedness alone nor a generic rank estimate completes
an entry.

Completed induction assembly: PositionalCut.clean_rank_step exhausts all selected
classes, clean_elimination proves all original ranks at a fixed degree,
cutFree_degree_step applies simultaneous cleaning afterward, head_cut_elimination
discharges strict DegreeBelow, and G.cut_free_normalization handles arbitrary
proof trees. cut_elimination and atomized_cut_elimination supply both unrestricted
interfaces. Exact signatures and actual global witnesses are in
Checks/GlobalCutElimination.lean. Coherence and full-paper maximality remain open.

## Actual coherence continuation (29 October 2026)

All unrestricted elimination interfaces remain complete. The actual positive,
Reduced and Boolean coherence argument and intended occurrence interpretation
are now proved; see GENTZEN_COHERENCE_REPORT.md. Finite atomic mix normal forms,
DNF/CNF comparison maps and one-sided recovery are constructed. Full source
congruence/substitution correspondence, maximality, model and remaining full-paper
claims continue; constructor coverage is not the full-paper certificate.

## Actual source maximality continuation (29 October 2026)

All constructor/tag/rank and coherence results persist. Actual quotient reduction,
derived negation/naturality, full proof-congruence/closure correspondence and
Presentation.maximality/congruence_dichotomy/raw_maximality are now proved; see
SOURCE_MAXIMALITY_REPORT.md. The separate short proof, model and remaining full-
paper claims continue. Constructor coverage remains a discharged prerequisite.

## Distinct short-proof continuation (29 October 2026)

All completed constructor/rank/coherence/source-main results persist. The exact
q_A/e_A inverses, direct short congruence collapse and actual short_maximality
are now proved; see SHORT_QE_REPORT.md. Both maximality routes are retained.
Remaining model, substitution/operation/isolation and appendix duties continue.
