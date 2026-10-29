# Selected cut constructor and tag coverage

Current construction incorporates 811eceeb. All twelve binary branches, all six
gamma blocked families, BlockedL.conjunction and BlockedR.disjunction are complete.
Each has an actual source equation and instantiated original-rank step. Six
First/Second/Both logical blocked families and global induction remain open.
Current report: GENTZEN_BLOCKED_DISJUNCTION_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Appendix C p.260 is proved; its p.262 BlockedL.disjunctionFirst correspondence
remains open. Measure original selected rank before adapters.

| Root and selected region | Left cut premise | Right cut premise |
| --- | --- | --- |
| Atomic leaves and rank-two clean cuts | Existing atomic/exhaustive rank-two results | Existing atomic/exhaustive rank-two results |
| Cut root | Excluded by Clean cut-freeness | Excluded by Clean cut-freeness |
| Opposite exchange/thinning/contraction | Equation, descent and elimination/rank-step wrappers checked | Equation, descent and elimination/rank-step wrappers checked |
| Same-side exchange/thinning/contraction, unique predecessor | Existing single-fiber equations, reconstruction and rank steps | Existing single-fiber equations, reconstruction and rank steps |
| Same-side thinning, fresh selected tag | Existing rank-two/leaf classification; dispatcher pending | Existing rank-two/leaf classification; dispatcher pending |
| Same-side contraction, selected copy cluster | all three gamma families and disjunction complete; three sequential BlockedR reductions pending | all three gamma families and conjunction complete; three sequential BlockedL reductions pending |
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
The eight completed blocked families have separate actual contraction/source
proofs; parametric commutation alone does not supply them.

| Blocked constructor family | BlockedL | BlockedR |
| --- | --- | --- |
| gammaMix | Actual source equation/reconstruction; blockedL_gammaMix_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaMix_eliminated/rank_step |
| gammaConj | Actual source equation/reconstruction; blockedL_gammaConj_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaConj_eliminated/rank_step |
| gammaDisj | Actual source equation/reconstruction; blockedL_gammaDisj_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaDisj_eliminated/rank_step |
| conjunction / disjunction | Actual source_equation, reconstruction and blockedL_conjunction_rank_step | Actual source_equation, reconstruction and blockedR_disjunction_rank_step |
| disjunctionFirst / conjunctionFirst | Pending sequential actual cut reduction | Pending sequential actual cut reduction |
| disjunctionSecond / conjunctionSecond | Pending sequential actual cut reduction | Pending sequential actual cut reduction |
| disjunctionBoth / conjunctionBoth | Pending sequential actual cut reduction | Pending sequential actual cut reduction |

The paired names give BlockedL / BlockedR constructors. Actual source/native
adapters are proved for all six gamma entries and both unary logical entries;
the six First/Second/Both entries remain open. Neither blockedness alone nor a generic rank estimate completes an entry.

Remaining induction assembly: fixed-degree all-ranks clean theorem under the
strict outer DegreeBelow hypothesis; only then arbitrary-premise cleaning;
strong degree induction; arbitrary-proof structural normalization; actual
CutElimination and AtomizedCutElimination inhabitants. No new global inhabitant
is asserted by this table.
