# v27 abstract: mathematical writing review

The six-sentence abstract below states the result first, gives the exact meaning of maximality, introduces both proofs, and separates the Lean development's contents from the dependencies of the maximality theorem. No further prose change is required within this scope.

## Source and scope

Reviewed the abstract of *Maximality of the Došen–Petrić Boolean Category*, v26, for its replacement in v27. Checked its claims against the introduction, the definitions and theorem in Section 2, the two collapse arguments in Sections 5–6, the account of occurrence coordinates, and the Palomar v3 description reproduced in `docs/PALOMAR_V3_REGISTRATION_REPORT.md`. This is an abstract review, not a new whole-paper audit.

Applied the mathematical-writing plugin's complete instructions and its two supporting references. Consulted the supplied original of Knuth, Larrabee, and Roberts, *Mathematical Writing*, at `review-v13-sources/writing.pdf`: Section 1; Herbert Wilf's discussion in Section 27 and its paired examples in Sections 28–29 (printed pp. 59–65); and Mary-Claire van Leunen's précis exercises in Section 36 (printed p. 87). Page references here are printed page numbers.

Wilf's Section 27 supports placing the result before technical preparation and avoiding convoluted references. Sections 28–29 present the same necklace-counting argument in compressed and expanded forms; the end of Section 27 explicitly declines to rank either form as superior. Their application here is to retain explanation useful to the intended reader, not to minimize the word count mechanically. Van Leunen's reduction and abstract exercises support testing economy without changing meaning; the ten-sentence exercise is not a prescribed journal abstract limit.

## Existing abstract outline

| Sentences in v26 | Function |
| --- | --- |
| 1 | State maximality and the nonempty generating-set hypothesis. |
| 2 | Explain maximality by adjoining an equation and taking closure. |
| 3 | State the consequence for Došen and Petrić's conjecture. |
| 4–5 | Describe occurrence selection and the first collapse argument. |
| 6 | State the semantic corollary for all variable interpretations. |
| 7–8 | Announce Lean proofs, their dependencies, and the coordinate correspondence. |

The central contribution is the dichotomy between equality and the total congruence under morphism operations and uniform formula substitution. The proof outline needs the identification of distinct parallel morphisms as its premise and equality of the product projections as its conclusion. Boolean Coherence and substitution are shared ingredients; the two subsequent collapse arguments differ.

## Findings and repairs

| Anchor | Actual difficulty | Source principle or editorial rationale | Action |
| --- | --- | --- | --- |
| Opening two sentences | Combining the named result with its full meaning would make a long opening sentence. Deleting the explanation would leave the relevant meaning of maximality implicit. | Section 1, points 11 and 24: complementary explanation and an effective opening. | Keep two sentences. Express the second through congruences to state the exact closure hypotheses and the equality/totality alternatives of Section 2. |
| Proposed congruence sentence | “On its morphisms that is preserved” delays the predicate without adding a restriction in this context. | Section 1, point 17; independent local economy judgment. | Use “Every congruence preserved by the operations on morphisms and by uniform formula substitution either is equality or identifies every pair of parallel morphisms.” |
| v26 sentences 4–5 | The unspecified two isomorphisms describe only the first argument; “the proof” does not announce the second. | Wilf, Section 27: make the contribution plain at the outset. | State that there are two proofs and give their shared inference. “Derive equality … from an identification” fixes the logical direction. |
| v26 sentence 6 | The semantic corollary is a distinct result, but it adds a second collapse statement and makes “such” refer back across the proof outline. | Section 1, point 17; abstract scope and economy judgment. | Omit this sentence from the abstract; retain the corollary in Section 5. |
| Lean conclusion | Folding the coordinate correspondence into a list of maximality dependencies would misstate its role. | Preservation of mathematical dependencies; Section 1, point 17. | Retain a separate sentence listing contents of the formalization. Its “It” refers directly to the Lean formalization. |

## Definition-order and notation check

The final abstract keeps the nonempty hypothesis and universal quantifier over the stated congruences. Section 2 defines a proof congruence on hom-sets, adds uniform substitution to obtain a substitution congruence, and identifies total congruences with preorder quotients. Thus “every pair of parallel morphisms” does not identify objects or morphisms with different endpoints. The second sentence supplies the intended meaning of maximality before the conjecture is mentioned.

“Distinct parallel morphisms” supplies the required premise in the proof summary. Boolean Coherence is standard named terminology explained in Section 3; the product projections are defined in Section 2. Tagged occurrence sets and finite ordinals name the two substitution presentations compared in Appendix A. No symbols, unexplained local abbreviations, or new terminology are introduced in the abstract. The scope does not require reproducing these definitions there.

## Final wording

> We prove that the zero-identity Boolean category of Došen and Petrić, freely generated by a nonempty set of propositional variables, is maximal. Every congruence preserved by the operations on morphisms and by uniform formula substitution either is equality or identifies every pair of parallel morphisms. This disproves their conjecture that the category is not maximal. We give two proofs that use Boolean Coherence and uniform formula substitution to derive equality of the product projections from an identification of distinct parallel morphisms. We also give a Lean formalization of these proofs and their dependencies. It includes Boolean Coherence and the correspondence between substitution on tagged occurrence sets and substitution on finite ordinals.

The revised sequence is result, exact formulation, conjecture, shared proof mechanism, formalization, and formalization contents. No change to the paper's section structure is recommended.

## Disposition and limits

The wording is approved as a scoped editorial recommendation. The review checked its quantifiers, premises, conclusions, and dependency language against the identified manuscript passages; it does not certify the mathematics or novelty. No manuscript files were edited by this review. Compilation, rendered layout, the submission package, and external bibliographic verification are outside this report's checks.

## Additional comparison with the registered abstract

Read the exact v3 abstract in `provenance/palomar-v3-registration-20261103/entry.json` and the earlier rationale in `docs/reviews/PALOMAR_REGISTRATION_WRITING.md`. The registered abstract's theorem agrees with the manuscript's congruence dichotomy. Its additional claims correspond to the selected declarations for the two maximality proofs, nonzero variable identities, and the empty hom-set from the terminal object to the initial object. No mathematical discrepancy was found in this scoped comparison.

The registered abstract has one avoidable repetition: after spelling out the dichotomy, it says that the formalization “proves the congruence dichotomy.” The new information in that sentence is the existence of two proofs. An optional future editorial repair is simply “The formalization gives two proofs of maximality.” The registered abstract was not edited.

The earlier report describes the selected five-result formalization while preserving the then-current manuscript, explicitly identified there as v8. This documents why a separate description was prepared. It does not document a requirement that the two abstracts differ, or establish that a difference improves either abstract.

The v27 paper abstract is assessed on the paper's contribution and intended readership. Its congruence formulation earns its place by specifying the closure hypotheses and precise conclusion; its proof summary and Lean contents describe the paper's methods and scope. Agreement with registered wording is only a correctness crosscheck. Making the abstracts either identical or different is not an editorial objective, and this comparison supplies no reason for another rewrite of the v27 abstract.
