# Selected cut constructor and tag coverage

Current checkpoint: 77199ac, the delivery receipt following proof 9af0a8a.
Four mix branches and conjR_right_second have equations, reconstructions and
instantiated rank steps. Seven logical binary branches and fourteen blocked
reductions remain open. A checked branch is a local input to the intended clean
selected-rank dispatcher; global elimination and the full-paper endpoint are open.

The active successor is CODEX_AFTER_77199AC_LOGICAL_BINARY_CUTS.txt. Start with
conjR_right_first and the retained native equation, then the remaining six logical
branches. Original selected rank is measured before adapters. The swapped mix
branches use firstRaw/secondRaw and post-elimination atomization; the separately
typed direct leftFirst macro is not the builder used by first_equation.

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
| conjR, first child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Clean/rank descent checked; equation, reconstruction and rank step pending |
| conjR, second child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightSecond/conjRRightSecond_equation; CutCommutation.conjR_right_second_rank_step) |
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
conjR_right_second is now complete; seven logical binary branches remain open.
The eight algebraic inputs are recorded in GENTZEN_MIX_UNION_REPORT.md and
provenance/wsl-gentzen-mix-union/. The four completed mix reductions are recorded
in GENTZEN_BINARY_MIX_CUTS_REPORT.md and provenance/wsl-gentzen-binary-cuts/.

The right-second conjunction reconstruction preserves the retained B tag,
cut count and Atomized condition, with actual native fold/unit and head-routing
diagrams. mixedDisj_swap is a proved Reduced interchange available for later
cases, not a native first-child equation or a general G duality. Exact next native
first-child candidate/equation: current evidence open/next-native-first.lean.
Report/evidence: GENTZEN_LOGICAL_BINARY_CUTS_REPORT.md and
provenance/wsl-gentzen-logical-binary-cuts/.

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
