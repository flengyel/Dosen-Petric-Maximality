# Contextual factorization: hostile-referee review

## (A) Kill-shots / hard blockers

This is an author-side, AI-assisted self-audit of the new Lean argument,
report and correspondence table. It is not independent peer review.
No confirmed blocker remains for the unconditional contextual factorizations.

Anchor: correspondence section “Contextual factorizations”, final row; source
p.321, appeal to Zero-Identity Distributive Dicartesian Coherence; and
ReducedOccurrences.lean, `Faithful`. Claim checked: no completed coherence is
claimed. Failure mode for a stronger claim: **unproved**; evidence:
**absence_in_text** and **structural_argument**. No reduced faithfulness proof,
common atomic factorization, equality-reflection result or faithful interface
instance is supplied here. Severity: fatal to claiming Boolean Coherence or
unconditional maximality, not to the stated contextual theorem. Repair: prove
the common atomic factorization and the required §12.5 positive-core theorem.
No counterexample to coherence is alleged.

## (B) Major weaknesses

One source defect is confirmed and explicitly contained. Anchor: printed
p.319, displayed g-disjunction hole case, compared with its preceding general
type and Table 2 p.49. Claim as displayed: B → top ∨ B, named sigma-disj-left-in.
Failure mode: **ill_typed** relative to that named primitive and the general
recursion. Evidence: **citation**, rendered PDF inspection and exact source
hash; Table 2 gives B → bot ∨ B. Severity: major if transcribed literally into
the recursion; repaired in this construction by the correctly typed named
unit map, with the printed discrepancy preserved in the map. No claim is made
that the displayed typo is itself a source equation or a new generator.

The following possible circularities were checked against the actual proofs:

| Anchor | Typed claim, evidence and checked law | Status |
| --- | --- | --- |
| ReducedContexts, `Context/plug/mapTerm` | One selected position, arbitrary fixed NormalForm objects, four binary placement cases via Op. Evidence: structural_argument. Identical surrounding formulas do not trigger replacement. | Unconditional construction. |
| `map_derives`, `map`, `map_id/map_comp`, `mapTerm_id/mapTerm_comp` | Generated congruence preservation precedes Quotient.liftOn. Raw id/comp laws are Derives via Quotient.exact of this same syntactic quotient. Evidence: derivation. | No inclusion or relation kernel defines equality. |
| ReducedLaws / ReducedStructure | Only inherited schemas are lifted. Product eta/terminality and coproduct duals reuse generic proved DiagonalData. Unit/pentagon/triangle/hexagon and mixed d/dR composites have explicit inverse cancellations. Evidence: derivation and unchanged grammar/equation hashes. | No new equation, medial substitution, or assumed positive coherence. |
| `zero_top/zero_bot/fromTop_unique/toBot_unique` | Existing top-domain/bottom-codomain arrows are equal from unit uniqueness plus zero_law. Evidence: derivation. | Inside Reduced, no inference from empty relations or full uniqueness. |
| ContextualMaps, `gConj/gDisj` | Five cases each, exactly source paths and endpoints. Naturality: `gConj B ; K[f] = (id K[top] ∧ f) ; gConj D`; dual square for gDisj. Evidence: derivation. | Covariant naturality in B; no arrow-negation operation. |
| `gConj_top/gDisj_bot`, `gEta/gEpsilon` | Unit components are rightOut/rightIn; naturality plus unit inverses gives the contextual path, with zero absorbed by proved parallel-arrow uniqueness. Evidence: derivation. | Arbitrary P, any existing h : top → B or B → bot. No theorem-restating hypothesis. |
| `gEta_comp/gEpsilon_comp` | Naturality of right units plus tensor composition proves composed forms, with f applied first/last as typed. Evidence: derivation. | Both are unconditional equalities in Reduced.Hom. |
| ContextOccurrences | encode/decode inverse laws, injective disjoint fixed/hole embeddings; context relation is identity on fixed tags and supplied relation on hole tags. Empty constants are eliminated explicitly. Evidence: derivation. | Equal labels never identify tags. |
| `gEta_comp_relation/gEpsilon_comp_relation` | Comparisons use Sum.inl on changed domain/codomain. Evidence: derivation from already proved syntactic identities and forward interpretation preservation. | No ill-typed relation equality and no reverse inference to arrow equality. |

## (C) Minor issues

The actual source uses opposite disjunctive symmetry index notation. The map
therefore specifies both the source convention and Lean's typed swap arguments.
Execution-order semicolons are defined before the recursion and factorization
tables. Explicit endpoints replace any reliance on the order of prose.

A local unused-simp-argument linter setting covers constructor branches of the
relation proof. It does not disable Lean's proof checking or the axiom audit.
All reported mathematical endpoints compile without proof holes.

## (D) Cross-section consistency failures

No remaining drift was found between the new code and current scope maps.
Historical reports are retained. Both reduced and full generating signatures
are byte-identical to the starting commit; manuscript v4, toolchain and
manifest are preserved. The context functor has source and target
Reduced.category P, object map plug, and covariant arrow map map. Identity,
composition and quotient descent are all proved, rather than inferred from a
matching object operation. MonoidalData instances supply only proved laws.

For the two-object one-arrow test, the construction never chooses an arrow
in an arbitrary hom-set. Every zero is an endomorphism; generalized
factorizations require an existing h and composed forms an existing f.
Neither the object dual operation, full representation theorem nor the
conditional faithfulness transfer is used as a reverse equality rule.

## (E) Acceptance conditions, non-negotiable

1. Source types and all recursive intermediates, including the printed typo,
   must be recorded. Met by the correspondence tables and source metadata.
2. Context action must preserve Derives before quotient use. Met by
   map_derives; raw and quotient id/comp laws compile.
3. Required structural and zero laws must be reduced derivations. Met by
   ReducedLaws/ReducedStructure; 21/61 signatures remain unchanged.
4. Both contextual and composed identities must be unconditional. Met by the
   four gEta/gEpsilon declarations; source atomic instances are special cases.
5. Fixed/hole tags and endpoint coordinates must be explicit. Met by inverse
   coordinates, disjointness/injectivity and the two composed relation lemmas.
6. Coherence and common atomic factorization must remain open. Met by all
   current reports/maps; no new Reduced.Faithful instance.
7. Strict verification, standard-axiom bounds, five rejected controls and
   manuscript integrity must have retained evidence. Met by the report and
   provenance/wsl-contextual-factorization.

Failure of conditions 1–5 or 7 would require withdrawing the corresponding
construction claim. Failure of condition 6 would require withdrawing the
promoted coherence/maximality claim.

## (F) Not checked / uncertainty log

No independent kernel replay, full independent source-transcription audit,
Challenge/Solution comparison, Comparator, official preflight, service
verification, novelty survey or whole-manuscript layout audit was performed.
The cached source passages, exact generated equation boundary and new argument
were inspected; this is not mathematical certification by an independent party.

Strongest confirmed blocker: §12.5 positive-core faithfulness and common atomic
factorization remain unproved for the later coherence target. Strongest
suspected unconfirmed blocker: none identified for the contextual theorem.
Most important unchecked item: an independent replay/source audit. The scoped
conclusion does not depend on unavailable review material. Final recommendation:
**unknown** as an independent certification; the stated contextual endpoints
pass this author-side audit, and coherence remains open.
