# V26 mathematical-writing review

13 November 2026. Manuscript: *Maximality of the Došen–Petrić Boolean Category*, v26. Comparison: v25. Scope of requested revision: the common factorization in Appendix D.5 and one sentence distinguishing the proof dependencies in Appendix E.

The two additions explain the construction and its dependencies without changing the theorem statements. No necessary prose correction remains in the passages examined. The complete source was read for definition order, terminology, paragraph functions, and continuity; the detailed recommendations below concern the authorized additions.

## Governing source

Consulted Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*, Stanford report, using the supplied PDF `review-v13-sources/writing.pdf`: §1, printed pp. 1–6, and §§4–5, printed pp. 9–13. The relevant advice is §1 points 10–13 (connect exposition and explain constructions in complementary ways), point 17 (unambiguous sentences), and point 26 (avoid unnecessary jargon). Section 4 qualifies the timing of definitions; §5, printed p. 12, discusses clear paragraph boundaries. The factor/summand distinction is a mathematical terminology judgment, not a separately attributed rule of that source.

## Existing outline and functions

| Location | Function |
| --- | --- |
| Abstract | States maximality, the disproved conjecture, proof method, model consequence, and formalization scope. |
| 1. Introduction | States the problem and result, introduces the proof, distinguishes related category presentations, and gives the roadmap. |
| 2. The Boolean proof category | Defines operations, zero morphisms, congruences, and the quotient; states the main theorem. |
| 3. Occurrences and substitution | Defines occurrence coordinates and their interpretation; states coherence and proves the substitution formulas used later. |
| 4. Isolating an occurrence | Isolates a differing relation pair and extends the context equation by substitution. |
| 5. Equality of the product projections | Uses two isomorphisms to prove collapse and the model corollary. |
| 6. A second proof and the Lean formalization | Gives the mix proof, union laws, and correspondence with Lean declarations. |
| A.1. Occurrence maps and their fibres | Defines the tagged blocks and their label maps. |
| A.2. The finite-ordinal presentation | Translates the block construction to ordinal coordinates and computes an example. |
| A.3. Shared variables and the maximality argument | Explains renaming and its use in both literal cases. |
| B. Diagrams for three defining equations | Displays and types the first-injection equation, zero identity, and zero law. |
| C. Corrections to the cut-elimination argument used in Boolean Coherence | Identifies the dependency and proves the corrected rank comparisons for the two specified cases. |
| D.1. Arrow terms and equations | Defines term equality and primitive congruences. |
| D.2. Reading a Lean declaration | Explains the syntax and the short-proof correspondence. |
| D.3. The five declarations | States both maximality results, the dichotomy, nonzero identity, and empty hom-set. |
| D.4. Congruences on terms and on morphisms | Proves the quotient correspondence with the substitution-closure hypothesis explicit. |
| D.5. The proof of coherence | Explains positive coherence, the common factorization, and the transfer to the original presentation. |
| E.1–E.2. The inverses of q and e | Constructs the inverses and verifies their identities by coherence. |
| E.3. The split comparisons used in coherence | Proves the section and retraction identities from presentation equations. |
| Use of AI tools; bibliography | Preserves the authorized disclosure and source attribution. |

The principal dependencies remain: occurrence interpretation and coherence imply isolation; substitution gives all context equations; either collapse argument yields maximality. The new paragraph belongs at the passage from positive to arbitrary terms. No reorganization is needed.

## Findings

| Anchor | Assessment | Source principle or rationale | Action |
| --- | --- | --- | --- |
| D.5, “To construct these data” | The count of eta/epsilon constructors supplies the induction parameter; the sentence identifies the source and target extensions. | KLR §1, points 10–13; mathematical explanation at its point of use. | Retain. |
| D.5, diagonal and projections | Their types and the index range are explicit. Extension by identities explains the two common-endpoint middle terms. | KLR §1, points 11 and 17. | Retain. |
| D.5, endpoint endomorphisms | The final text distinguishes conjunction factors from disjunction summands and identifies the identity and zero components. This explains the full direct-image equations, not merely agreement on old occurrences. | Mathematical terminology and correspondence with `masked_factor` and `masked_support`. | Retain. |
| D.5, paragraph boundaries | The assertion, construction, and faithfulness deduction have different functions. | KLR §5, printed p. 12. | Applied: paragraphs start at “To construct these data” and “Thus equality”. No wording replacement is required. |
| E opening, “The inverse identities below” | The sentence distinguishes coherence-dependent inverse equations from the equations used to establish coherence. “It” refers to Boolean Coherence. | KLR §1, points 12 and 17. | Retain. |

## Definition order and notation

The category operations and composition convention precede the additions. The morphisms eta and epsilon are typed in Section 2; the reduced presentation is described in Section 3 and recalled in D.5. Positivity is defined at the beginning of D.5. The symbols A', B', u, v, f₀, g₀, a, and b are declared immediately before the new construction. The diagonal and projections receive explicit types in that construction. The terms “prefix” and “suffix” refer to the extracted outer composites rather than introducing a new mathematical object class.

The additions preserve the distinction between terms and quotient morphisms. They introduce no new global zero-morphism assumption: all added zeros are endomorphisms. The Appendix E sentence refers to the already defined q and e morphisms and to the split comparisons of D.5. It neither asserts a new equational proof of the inverse identities nor changes the dependency order.

## Disposition and scope

Retain both additions. The optional paragraph breaks have been applied. The source introduces no review attribution or revision narrative. The prior authorized disclosure remains unchanged.

This report covers prose, definitions, notation, and targeted correspondence with `CommonAtomicFactorization.lean` and `AtomicPortOccurrences.lean`. It does not claim a new Lean build, independent kernel replay, complete reconstruction of cut elimination, or fresh verification of every external reference. Compilation and rendered-page inspection belong to the accompanying build record.
