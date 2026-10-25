# Mathematical-writing review of v6

The revised manuscript states its result directly, attributes the structural ingredients precisely, and distinguishes the proved conditional Lean theorem from an uncompleted formalization of coherence. No material writing or contribution-positioning defect was found. The recommended deletion of one redundant concluding sentence in §6 has been applied and confirmed; the substantive qualification about faithfulness remains.

Reviewed manuscript: Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*, v6, dated 25 October 2026. The complete source was read, including both appendices, the disclosure, and bibliography. The full change from v5 was also inspected. The final source SHA-256 is `2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0`.

## Governing source

The review used the mathematical-writing skill and the supplied text of Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*: §1, especially points 5, 10–17, 24, and 26, and §§4–5 on definition placement, economical notation, sentence structure, and connected explanations. The supplied files were `review-source/klr-excerpt.txt` and `manuscript-second-review/klr.txt`.

The skill’s additional requirements concerning manuscript boundaries and editorial-process language were applied separately; they are not attributed to KLR. The notation and source-review supplements were read. The source material was available, so this was a source-grounded writing review.

## Current outline

| Part | Function and dependencies |
|---|---|
| Abstract | States maximality, identifies the conjecture, summarizes isolation and isomorphism collapse, and qualifies the Lean result. |
| §1 Introduction | States the question and contribution; attributes the contextual reduction and structural isomorphisms; locates closely related categorical results; gives the occurrence/Lean roadmap. |
| §2 The Boolean proof category | Defines the presentation, operations, zero identities, proof and substitution congruences, and maximality; states Theorem 2.1. |
| §3 Occurrences and substitution | Defines tagged occurrences and relations; states the cited coherence theorem; distinguishes the category from Joyal’s closed setting; develops signed normal forms and substitution. |
| §4 Isolating an occurrence | Defines the contextual equation and derives it for every formula from a nontrivial substitution congruence. |
| §5 Contextual collapse | Identifies the particular structural isomorphisms; proves terminality in the quotient and projection equality; completes maximality and the model corollary. |
| §6 Lean formalization | Describes the syntax and equation-generated quotient, the explicit hypotheses of the formal maximality theorem, and its mix-based proof; states the remaining faithfulness boundary. |
| Appendix A: profiles and fibres | Defines and diagrams occurrence profiles and local substitution blocks. |
| Appendix A: finite-ordinal presentation | Relates the tagged coordinates to the published ordinal construction and gives a worked example. |
| Appendix A: shared variables | Defines renaming and connects the diagrams with substitution in the main proof. |
| Appendix B | Gives typed diagrams for the first-injection equation, zero identity, and zero law. |
| Disclosure and references | Retains the conventional author-approved disclosure and identifies the exact sources and formalization revision. |

The dependency order is intact. The new proof uses the existing category, coherence, and substitution definitions. The formalization discussion follows the mathematical theorem, so its implementation vocabulary does not interrupt the proof.

## Comparison with the governing source

| Anchor | Finding | Source principle or rationale | Action |
|---|---|---|---|
| Abstract, “relative to explicit coherence and structural inputs” | The Lean claim is qualified where it first appears. It does not advertise a complete unconditional source-presentation theorem. | KLR §1 points 5 and 12; accuracy of the theorem being described. | Retain the qualification. |
| §1, second paragraph | Earlier contextual reduction and isomorphisms are cited as mathematical tools. No absence-of-prior-publication claim or ranking of contributions is inserted. | Precise attribution; KLR §1 point 12 cautions against self-praise. | Retain. |
| §3, Joyal paragraph | Gives a concrete hom-set obstruction to cartesian closure, after the occurrence functor and nonthinness have been established. | KLR §1 points 10–13: connected explanation and motivation. This is substantive comparison, not a preventive disclaimer. | Retain. |
| §5, structural-isomorphism lemma | Defines q_A and e_A with their types. The proof first identifies the particular singleton/two-point graphs and then uses substitution for arbitrary A. | KLR §1 points 5, 11, and 14; explicit typing requirement. | Retain. |
| §5, contextual-collapse lemma | The all-formula hypothesis is stated explicitly. The proof does not invoke closure of the congruence under substitution; substitution was used beforehand to establish the isomorphisms in the original category. | Preservation of hypotheses and logical dependencies. | Retain. |
| §5, terminality and invertible projection | Prose explains the purpose of the displayed equations. The diagonal is defined before the projection argument uses it. | KLR §1 points 10–13; definitions near use. | Retain. |
| §6, symmetric-map discussion | The implemented proof is related to the established mix map, with equation (dm) cited. This explains the difference between the written isomorphism proof and the existing formal proof. | Mathematical correspondence and attribution, not implementation narration. | Retain. |
| §6, final paragraph | The missing proof of faithfulness and absence of a complete source-presentation instance materially delimit the formalization claim. | Skill requirement to preserve genuine mathematical limitations. | Substantive statements retained. The redundant last recap was deleted; this correction was confirmed in the final source. |
| Appendices A–B | Definitions precede diagrams; the example and coordinate comparisons explain distinctions used in substitution. No task labels or retrospective verification checklist appear. | KLR complementary explanations; diagram convention. | Retain. |

No alternative outline is needed. No theorem, hypothesis, citation, or appendix should be removed merely because the proof now uses previously published isomorphisms.

## Definition-order and notation audit

- Formula syntax, the free category, composition direction, structural maps, and zero identities precede the definitions of congruences and maximality.
- Zero arrows are introduced only for inhabited hom-sets. Their composition laws are established before later transport arguments.
- Tagged disjoint union, occurrence sets, labels, relations, the functor G, signed literals, and normal forms are introduced before the isolation argument.
- Substitution block sets and all maps in the squares are defined before their diagrams. Occurrence positions remain distinct from their labels.
- The arrow j_A and contextual equation K_A precede their use in §5.
- The arrows q_A and e_A are typed in their lemma. The auxiliary b is typed in its proof; the two-element graph comparison makes its adjustment by product symmetry intelligible.
- The quotient proof defines E, S, s, r, and the diagonal before using them. The proof-congruence hypothesis and the substitution-congruence hypothesis remain distinct.
- The model corollary defines interpretation before invoking its universal quantifier.
- Section 6 explains `Derives` as the generated equational relation and explains `relative_maximality` by its conclusion and explicit assumptions. The mix map is typed and defined next to its first formula.
- The appendix defines formula patterns, profiles, finite ordinals, block encodings, and renaming maps before their mathematical use.

No new undefined manuscript-specific term or overloaded symbol requiring repair was found. Familiar terminology previewed in the introduction is appropriate for the intended readership.

## Manuscript boundary and positioning

The source contains no editorial-review narrative, agent instructions, internal audit labels, or self-deprecating account of the theorem’s value. It neither says that the work was already published nor asserts global originality from a negative search result. Its statement that maximality contradicts the specified conjecture remains distinct from attribution of the ingredients used in the proof.

The Lean section states the mathematical scope of the implemented theorem. It does not import declaration counts, test logs, service-registration claims, or a claim that general cut elimination has been completed. The reference fixes the formalization revision rather than relying on a moving project-status document.

The disclosure is conventional publication language. The prior saved writing review records it as author-approved. It is retained under that established session record, not treated as permission for process commentary elsewhere in the paper.

## Scope and final recommendation

This review covers the complete revised source and its reading order. It consulted the independent Lean-scope report and checked that the manuscript’s formalization wording agrees with that report; it did not independently rerun Lean or certify every code declaration. Mathematical correctness and exact source subsumption receive separate reviews.

No compilation or complete PDF-layout inspection was performed in this writing pass. The primary validator reports a successful final compilation with no warning, overfull, underfull, or undefined entries, and clean layout after rendering all twelve pages and inspecting contact sheets and selected full pages. Those PDF checks belong to the primary validation. This writing pass independently confirmed the revised well-definedness wording and the shortened displayed revision label with its full immutable SHA retained in the hyperlink.

No material prose reconstruction is required. Preserve the substantive conditional Lean scope and the precise attribution of the isomorphism argument. The recommended local cut has been applied; no writing correction remains outstanding.
