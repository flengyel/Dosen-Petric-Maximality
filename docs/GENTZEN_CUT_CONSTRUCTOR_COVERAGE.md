# Selected cut constructor and tag coverage

This live table records source construction after ad95fb7. A checked branch
is a local input to the intended clean selected-rank dispatcher. The global
dispatcher, unrestricted cut elimination, coherence and full-paper endpoint
remain open. Native predecessor rank is measured before adapters.

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
| mix, first child tag | Clean/rank descent checked; equation/reconstruction pending | Clean/rank descent checked; equation/reconstruction pending |
| mix, second child tag | Clean/rank descent checked; equation/reconstruction pending | Clean/rank descent checked; equation/reconstruction pending |
| conjR, first child parametric tag | Clean/rank descent checked; equation/reconstruction pending | Clean/rank descent checked; equation/reconstruction pending |
| conjR, second child parametric tag | Clean/rank descent checked; equation/reconstruction pending | Clean/rank descent checked; equation/reconstruction pending |
| disjL, first child parametric tag | Clean/rank descent checked; equation/reconstruction pending | Clean/rank descent checked; equation/reconstruction pending |
| disjL, second child parametric tag | Clean/rank descent checked; equation/reconstruction pending | Clean/rank descent checked; equation/reconstruction pending |
| Fresh principal conjR / conjL pair | Existing conjunction A-then-B degree step | Same pair |
| Fresh principal disjR / disjL pair | Existing disjunction B-then-A degree step | Same pair |

The four same-side unary branches are implemented in
GentzenSameSideLogicalPrefix/Tail/Replacement/Descent. Their actual deletion
squares are LogicalDeletion.before_square and tail_square. They are not
instances of the structural SingleFiber residual theorem.

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
