# Mathematical-writing review of the conditional checkpoint

The map and theorem names distinguish proved conditional arguments from the
unproved actual-presentation bridge. Retain the manuscript's organization and
its unchanged text. This is an author-side editorial review, not correctness
or novelty certification.

The supplied work is Florian Lengyel, *Maximality of the Došen–Petrić Boolean
Category*, v4, dated 21 October 2026. Its complete TeX was read; the PDF text
was consulted for printed locations, especially §§4–5, pp.4–7. The detailed
formal correspondence review covers those sections and the current map.

The governing source consulted is Knuth, Larrabee, and Roberts,
[*Mathematical Writing*, official Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1 points 5, 10–15, 17, and §§4–5. The source advises self-contained theorem
statements, connected explanations, introducing variables, and consistent
notation; the later discussion permits context-sensitive definition placement.
The report's workflow and judgments below are our editorial application, not
a report format prescribed by that source. No source quotation is used.

## Existing outline and dependencies

| Existing section | Function and principal prerequisites |
| --- | --- |
| 1 Introduction | States maximality question and two-part proof route; motivates the distributor collapse. |
| 2 Boolean proof category | Defines operations, zero identities, congruences, and main Theorem 2.1. Uses the specified published presentation. |
| 3 Occurrences and substitution | Defines tagged positions, coherent interpretation, normal forms, and block substitution. Supplies prerequisites for isolation and transport. |
| 4 Isolating an occurrence | Lemma 4.1 constructs selectors/coselectors; Proposition 4.2 propagates the contextual equation. Uses coherence, normalization, signed labels, and substitution. |
| 5 Contextual collapse | Lemma 5.1 constructs the symmetric fold; Lemma 5.2 proves collapse; concludes Theorem 2.1 and model Corollary 5.3. Uses the structural laws and all-context equation. |
| A Substitution in occurrence coordinates | A.1 profiles/fibres; A.2 finite-ordinal coordinates; A.3 shared variables. Explains repeated blocks and coordinate changes. |

The central question is whether every additional substitution-stable arrow
equation makes B(P) thin. The new Lean contribution is the conditional
collapse/isolation/transport argument with explicit primitive inputs; the
actual presentation bridge is not included.

## Comparison and concrete actions

| Anchor | Issue / rationale | Action |
| --- | --- | --- |
| Map, `lem:collapse` and `thm:main` rows | Readers need the hypotheses and exact scope of a formal counterpart; application of §1 point 5. | Name `ContextualCollapse.total` and `relative_maximality`, and state the intended bridge remains open. Implemented in the map. |
| §5 Lemma 5.1, pp.5–6; `OccurrenceLaws` | Relation computation and categorical equality are different assertions. Editorial typing rationale. | Explain that operation images are calculated before original-category faithfulness. Retain the manuscript proof. |
| §5 Lemma 5.2, p.6; `Collapse` | A long sequence of formulas needs prose identifying each transition; application of §1 points 10–13. | Preserve the manuscript's terminality and pairing explanations. The correspondence map lists those proof steps in order. |
| §4 Proposition 4.2, p.5; `Substitution` | Substitution changes endpoint formulas, while double negation requires inverse arrows. Application of §1 points 11 and 14 plus explicit typing. | Map `map σ f : Hom (A.subst σ) (B.subst σ)` and the proved retract square. Preserve the existing TikZ diagram. |
| Model paragraph in coverage | A generated fragment and the intended category have different signatures. Independent editorial rationale: avoid an ambiguous completion claim. | State the omitted Boolean operations and limited truth invariant explicitly. Implemented in coverage. |

## Definition order and notation

In §2, products/projections, coproducts/injections, terminal/initial maps, and
composition are introduced before the distributor and zero-identity formula.
Zero arrows are defined only for inhabited hom-sets. Congruence and
substitution congruence precede maximality. In §3, positions precede labels,
relations, coherence, signed literals, normal forms, and substitution blocks.
In §4, j_A and K_A precede isolation. In §5, u and h precede their symmetry
and collapse. These definitions are present; no missing-definition defect is
claimed. Previewing familiar terms in the abstract does not require a glossary.

The Lean order matches its prerequisites: category/formulas/relations;
structural records; interpreted equations; collapse; signed normal forms;
selectors; typed substitution; relative maximality. Names `fold A B` keep the
auxiliary formula explicit, and `fold_independent` proves its irrelevance.
Lean comp f g reverses the manuscript's written g ∘ f, with the same operational
order. Sum tags distinguish occurrences with equal labels. Congruence equality
is a relation on Hom and is not confused with original-category arrow equality.

## Prioritized wording

The consequential wording is confined to process/coverage documents. The map
now says: “The actual-presentation theorem remains open.” The coverage says:
“The actual Došen–Petrić presentation, its coherence theorem, its normalization
and substitution bridges, and the every-interpretation model corollary remain
open.” Retain these qualifications until the corresponding instances compile.
No manuscript replacement text or reorganized outline is recommended.

## Scope

The manuscript was not revised, recompiled, or graphically re-audited. Its
TeX/PDF hashes were checked. This review does not independently verify the
book's mathematical claims, literature priority, or the missing presentation
bridge. The source-grounded editorial review is complete within the stated
scope; it does not certify the formal theorem's intended-model applicability.
