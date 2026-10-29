# Selected cut constructor and tag coverage

Current construction incorporates 811eceeb. Four mix and all four conjR branches
have actual native/selected equations, exact-output reconstructions, eliminated
witnesses and instantiated original-rank steps. Four disjL and fourteen blocked
reductions remain open. Global elimination and the full-paper endpoint remain
open. Original selected rank is measured before adapters. See current report
GENTZEN_CONJR_LEFT_SECOND_REPORT.md and CODEX_NEXT_SESSION.txt.

| Root and selected region | Left cut premise | Right cut premise |
| --- | --- | --- |
| Atomic leaves and rank-two clean cuts | Existing atomic/exhaustive rank-two results | Existing atomic/exhaustive rank-two results |
| Cut root | Excluded by Clean cut-freeness | Excluded by Clean cut-freeness |
| Opposite exchange/thinning/contraction | Equation, descent and elimination/rank-step wrappers checked | Equation, descent and elimination/rank-step wrappers checked |
| Same-side exchange/thinning/contraction, unique predecessor | Existing single-fiber equations, reconstruction and rank steps | Existing single-fiber equations, reconstruction and rank steps |
| Same-side thinning, fresh selected tag | Existing rank-two/leaf classification; dispatcher pending | Existing rank-two/leaf classification; dispatcher pending |
| Same-side contraction, selected copy cluster | BlockedR reductions pending | BlockedL reductions pending |
| Unary logical, opposite side | conjL equation, reconstruction and rank step checked | disjR equation, reconstruction and rank step checked |
| Unary logical, same-side prefix | disjR before equation, reconstruction and original-rank step checked | conjL before equation, reconstruction and original-rank step checked |
| Unary logical, same-side suffix | disjR tail equation, reconstruction and original-rank step checked | conjL tail equation, reconstruction and original-rank step checked |
| mix, first child tag | Equation/reconstruction and instantiated rank step checked (BinaryMix.firstRaw/first_equation; mix_left_first_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryMix.rightFirstAt/rightFirstAt_equation; mix_right_first_rank_step) |
| mix, second child tag | Native equation/reconstruction and instantiated rank step checked (BinaryMix.leadingAt; mix_left_second_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryMix.secondRaw/second_equation; mix_right_second_rank_step) |
| conjR, first child parametric tag | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRLeftFirst/conjRLeftFirst_equation; CutCommutation.conjR_left_first_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightFirst/conjRRightFirst_equation; CutCommutation.conjR_right_first_rank_step) |
| conjR, second child parametric tag | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRLeftSecond/conjRLeftSecond_equation; CutCommutation.conjR_left_second_rank_step) | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightSecond/conjRRightSecond_equation; CutCommutation.conjR_right_second_rank_step) |
| disjL, first child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Clean/rank descent checked; equation, reconstruction and rank step pending |
| disjL, second child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Clean/rank descent checked; equation, reconstruction and rank step pending |
| Fresh principal conjR / conjL pair | Existing conjunction A-then-B degree step | Same pair |
| Fresh principal disjR / disjL pair | Existing disjunction B-then-A degree step | Same pair |

The four same-side unary branches are implemented in
GentzenSameSideLogicalPrefix/Tail/Replacement/Descent. Their actual deletion
squares are LogicalDeletion.before_square and tail_square. They are not
instances of the structural SingleFiber residual theorem.

MixCalculation supplies eight concrete tensor/union, mix/union, splice/union and
native-mix equations. Native mix keeps its reversed child blocks. These inputs
are checked; four mix branches now have actual equations/reconstructions/rank steps;
all four conjR branches are complete; four disjL branches remain open.
The eight algebraic inputs are recorded in GENTZEN_MIX_UNION_REPORT.md and
provenance/wsl-gentzen-mix-union/. The four completed mix reductions are recorded
in GENTZEN_BINARY_MIX_CUTS_REPORT.md and provenance/wsl-gentzen-binary-cuts/.

All four conjunction reconstructions preserve the retained A/B and selected C
as distinct tags, cut count and Atomized through actual native folds and routing.
The former conjunction candidates are resolved. Current evidence:
provenance/wsl-gentzen-conjr-left-second/. Earlier reports retain checkpoint
scope. The next actual native candidate is open/next-disjl-left-second.lean;
its sourceConj/disjLeft equation is open. No blocked family is closed by these
commutations, and no general G duality is assumed.

| Blocked constructor family | BlockedL | BlockedR |
| --- | --- | --- |
| gammaMix | Pending actual cut reduction | Pending actual cut reduction |
| gammaConj | Pending actual cut reduction | Pending actual cut reduction |
| gammaDisj | Pending actual cut reduction | Pending actual cut reduction |
| conjunction / disjunction | Pending sequential actual cut reduction | Pending sequential actual cut reduction |
| disjunctionFirst / conjunctionFirst | Pending sequential actual cut reduction | Pending sequential actual cut reduction |
| disjunctionSecond / conjunctionSecond | Pending sequential actual cut reduction | Pending sequential actual cut reduction |
| disjunctionBoth / conjunctionBoth | Pending sequential actual cut reduction | Pending sequential actual cut reduction |

The paired names give BlockedL / BlockedR constructors. Actual source/native
adapters remain to be implemented with their reductions. No family is closed
by the already proved blockedness predicate or by a generic rank estimate.

Remaining induction assembly: fixed-degree all-ranks clean theorem under the
strict outer DegreeBelow hypothesis; only then arbitrary-premise cleaning;
strong degree induction; arbitrary-proof structural normalization; actual
CutElimination and AtomizedCutElimination inhabitants. No new global inhabitant
is asserted by this table.
