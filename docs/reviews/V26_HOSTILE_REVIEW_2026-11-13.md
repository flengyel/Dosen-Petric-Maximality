# V26 focused hostile review

Date: 13 November 2026. Manuscript: *Maximality of the Došen–Petrić Boolean Category*, v26. Scope: the added construction paragraph in Appendix D.5 and the proof-dependency sentence opening Appendix E, checked against the retained Lean sources. The remainder of the paper is outside this review.

## (A) Kill-shots / hard blockers

None established in the two additions.

## (B) Major weaknesses

None established. The construction paragraph matches the following typed derivation.

1. `Reduced.atomicFactor` in `AtomicFactorization.lean` extracts one occurrence of an eta or epsilon constructor at each recursive call. Eta extraction changes a source `C` to `C ∧ (¬p ∨ p)`; epsilon extraction changes a target `D` to `D ∨ (p ∧ ¬p)`. The remaining constructor count decreases by one. The two outer morphisms recover the original quotient morphism.
2. `Reduced.commonAtomicFactor` in `CommonAtomicFactorization.lean` applies this construction to `f ∧ g : A ∧ A → B ∧ B`. Lifting `Δ_A : A → A ∧ A` through the added conjunction factors and each `π_i : B ∧ B → B` through the added disjunction summands produces two positive middle terms with common endpoints. `AtomicFactor.remap`, using prefix and suffix naturality, supplies common outer morphisms.
3. `AtomicPorts.masked` in `AtomicPortOccurrences.lean` precomposes and postcomposes the middle terms with positive endomorphisms. Their components are identities on the original formulas and zero endomorphisms on the added formulas. Such zeros have inhabited endomorphism sets; no zero between arbitrary objects is assumed. `AtomicPorts.prefix_mask` and `mask_suffix` preserve both factorizations. `masked_support` proves the entire direct-image relation, including absence of pairs incident with added occurrences. Preservation of the factorizations alone would not establish that support assertion.

Evidence: derivation from `AtomicExtraction.lean`, `AtomicFactorization.lean`, `AtomicPorts.lean`, `AtomicPortOccurrences.lean`, and `CommonAtomicFactorization.lean`. These steps use the defining equations and occurrence interpretation, not faithfulness of that interpretation.

## (C) Minor issues

No unresolved minor issue. One local ambiguity in the first inspected draft called both `A` and `B` “original factors,” although `B` is a disjunction summand in the expanded target. The final wording specifies endomorphisms formed from $1_A$ and $1_B$, respectively, and zero endomorphisms on the added conjunction factors and disjunction summands. The earlier phrase describing both kinds together now says “added formulas.” Both corrections were checked in the final source.

## (D) Cross-section consistency failures

None established. `PresentationShortQ.lean` and `PresentationShortE.lean` explicitly apply Boolean Coherence to the inverse identities. `GentzenDistributiveEpi.section_comparison` and `GentzenDistributiveMono.comparison_retraction` instead derive the split identities from the presentation equations. `GentzenNormalExpansion.lean` uses these comparisons to construct the expansions used in positive coherence. The new Appendix E sentence correctly distinguishes these dependencies; it does not claim that equational derivations of the two inverse identities are impossible.

## (E) Acceptance conditions, non-negotiable

The inspected source retains the endpoint zero-endomorphism step, distinguishes factorization preservation from relational support, and incorporates the terminology repair in (C). No further change is required by this focused check.

## (F) Not checked / uncertainty log

No new Lean build, kernel replay, full cut-elimination reconstruction, bibliography audit, or PDF-layout review was performed in this focused mathematical check.

- Strongest confirmed blocker: none.
- Strongest suspected unconfirmed blocker: none supported by the inspected additions.
- Most important unchecked item: the complete earlier proof dependency chain, which these edits do not change.
- Dependence on unavailable material: none for the findings above.
- Final referee recommendation: unknown; this focused check supports the two additions as inspected.
