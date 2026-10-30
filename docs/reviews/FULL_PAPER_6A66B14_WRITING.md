# Writing review of manuscript v8 at 6a66b14

The manuscript's existing organization supports the argument, and no necessary prose repair or new version was established by this review. The complete 985-line TeX source was read continuously and all 13 rendered PDF pages were inspected. V8 preserves v7's mathematics and diagrams; its changes concern the date, formalization status and immutable proof-source citation.

This AI-assisted author-side review applies [Mathematical Writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59). It is dated 2026-10-30 UTC and concerns *Maximality of the Došen–Petrić Boolean Category*, v8, dated October 29, 2026, at `6a66b14b382aac214b52c055b8bf281b35302239`. The cited mathematical source is `630c4b6e47da16a1434476a211fd29ce6adc5569`.

The supplied copy of Knuth, Larrabee and Roberts, *Mathematical Writing*, was consulted directly: §1, printed pp. 1–4 (PDF pp. 3–6), and §§4–5, printed pp. 9–11 (PDF pp. 11–13). The applications below distinguish that advice from independent checks of typing, proof correspondence and document layout. The report's organization is an editorial method, not a format prescribed by the book.

## Existing outline and dependencies

The central question is whether an additional equation between distinct parallel arrows, imposed compatibly with proof operations and uniform substitution, forces the generated Boolean proof category to become a preorder. The manuscript isolates a differing occurrence, obtains the contextual equation for arbitrary formulas, and uses the particular `q_A/e_A` isomorphisms to collapse projections. The source also retains the symmetric-fold proof.

| Existing section | Mathematical function and principal dependencies |
| --- | --- |
| 1. Introduction | States the maximality problem, identifies the short argument, locates related work and gives the roadmap. |
| 2. The Boolean proof category | Fixes the source syntax, structural operations, witnessed zeros and proof/substitution congruences. States Theorem 2.1. |
| 3. Occurrences and substitution | Defines tagged occurrences and the relational functor; states Boolean Coherence. Explains nonthinness, the cartesian-closure obstruction, normalization and whole-arrow substitution. Supplies the tools for isolation. |
| 4. Isolating an occurrence | Lemma 4.1 gives original-endpoint selectors and coselectors. Proposition 4.2 treats positive and negative literals and derives the contextual equation for every formula. |
| 5. Contextual collapse | Lemma 5.1 specifies `q_A/e_A`; Lemma 5.2 derives quotient thinness. Completes Theorem 2.1 and proves the all-interpretations model corollary. |
| 6. Lean formalization | Relates the general and actual-source theorems, retains the alternative fold argument and identifies the completed formalized content. |
| A. Substitution in occurrence coordinates | A.1: profiles, dependent fibres, tagged insertion and the label square. A.2: finite-ordinal encodings, the coordinate formula and worked example. A.3: shared-variable renaming and the positive/negative specializations used by maximality. |
| B. Diagrammatic forms of the structural equations | Displays the three structural paths with their objects and arrows. |
| C. Two corrections to the cut-elimination proof | Identifies the p. 260 rank comparison and p. 262 distinction between right rank and total rank. |
| Use of AI tools; references | Retains the author's authorized disclosure and the sources, including the immutable Lean source reference. |

This order places the main mathematical construction before the detailed coordinate appendix while keeping its prerequisites available at the point of use. No alternative outline is warranted.

## Comparison with the writing source

| Manuscript location | Observation | Verified source principle or independent rationale | Action |
| --- | --- | --- | --- |
| Introduction, pp. 1–2 | The question and proof route precede the detailed coordinate apparatus. | KLR §1, points 12–13: motivate the reader and make the prose intelligible when formulas are skimmed. | Retain. |
| Theorem 2.1, p. 3; Corollary 5.3, p. 7 | The nonempty variable set and the relevant congruence/interpretation conditions are stated at the results. | KLR §1, point 5: theorem statements should be self-contained at their intended level. | Retain the hypotheses. |
| §§3–4 and Appendix A | Tagged positions, labels, substitution and the normalization maps are explained where the argument uses them. | KLR §§4–5 qualify rigid rules about placing definitions before all discussion; §1, points 10–11 support connected exposition and useful explanations. | Retain the present division between the proof and coordinate details. |
| Lemmas 5.1–5.2, pp. 6–7 | The displayed arrows are defined before their isomorphism and collapse properties are used. | KLR §1, points 14–15 on notation and indices; independently, exact arrow identity matters for this proof. | Retain the specific `q_A/e_A` formulas and types. |
| Appendix A.2, pp. 9–10 | The worked example supplies actual coordinates and the nontrivial repeated-occurrence output. | KLR §1, points 10–11: complementary explanation has a mathematical purpose. | Retain the example and one-based conversion. |
| Appendix C | The correction states the two different rank quantities rather than treating “rank one” as a statement about their sum. | Independent mathematical consistency check; this is a substantive distinction. | Retain. |
| Abstract and §6, pp. 1 and 7–8 | The completed formalization status now agrees with actual source endpoints. | Independent correspondence check, rather than an editorial rule from KLR. | Retain v8 wording; no additional status commentary is needed. |
| Entire source and all rendered pages | No new reader-facing defect requiring an edit was established. The diagrams and displays were legible in the inspected renders. | KLR §1, point 17 concerns readable sentences; page-layout inspection is a separate check. | Preserve the current manuscript. |

## Definitions, notation and typing

The nonempty variable set and the generated category are fixed in §2. Proof congruence and substitution congruence are distinguished before maximality uses them. Zero arrows between different objects retain an existing-arrow witness; the paper does not silently assume every hom-set is inhabited.

Section 3 introduces occurrences as tagged positions before using their label maps. The old occurrence tag and inner inserted position remain different coordinates throughout substitution and Appendix A. The finite-ordinal presentation explicitly converts these dependent coordinates into consecutive positions; the worked example preserves repeated outer occurrences. Shared variable names may coincide without identifying the corresponding positions.

Normalization maps and signed literals are available before Lemma 4.1 reattaches isolation to the original endpoints. Proposition 4.2 uses the double-negation comparison in the negative branch. The quotient argument in §5 uses equality of congruence classes, while coherence is applied in the original category. Corollary 5.3 quantifies over full interpretations, and its final step uses the target's native products to reach arbitrary target arrows.

The manuscript's composition notation and the code's operational convention were compared: manuscript `g ∘ f` corresponds to Lean `comp f g`. Derived negation reverses the source and target. The relevant double-negation and De Morgan comparisons have typed naturality equations in the formal source.

No missing definition, late indispensable local convention, conflicting index convention or new ambiguous reference was confirmed. Familiar category-theoretic notions previewed in the introduction do not require a glossary before the problem statement.

## Prioritized edits

No mandatory edit is proposed. There is therefore no replacement passage, manuscript rewrite or version increment in this review. The existing organization, authorized AI disclosure, Appendix C text, diagrams and references remain intact.

The author-facing completion description should continue to distinguish the completed local formalization from independent replay and publication. That distinction belongs in the review and delivery records; it is not a reason to insert an editorial checklist into the manuscript.

## Scope and delivery

The full manuscript source, complete claim map, v7-to-v8 diff and all 13 rendered pages were examined. The v8 PDF SHA-256 is `ea32f33f027a672125d9f2e162a75e6cdff9d980abc2c0ecbc4ccfb4632a83ea`; the TeX SHA-256 is `3e578fea8c27c292736090a6c959f474d0da58074b7d2a8f7ff9d481c49c44b1`. Both agree with the final delivery register and retained repository bytes.

No TeX or Lean build was run in this review environment. Rendering used the existing PDF. Bibliographic existence, primary-source wording and novelty were not all independently rechecked in this editorial pass. No claim of mathematical certification follows from the writing assessment; the separate source review states the proof/evidence scope.

Retained repository path: `docs/reviews/FULL_PAPER_6A66B14_WRITING.md`. Requested WSL destination: `/mnt/c/Users/fleng/Downloads/FULL_PAPER_6A66B14_WRITING.md`. This environment cannot access that directory, so **this new review has not been copied or byte-verified there**. The earlier 43 registered deliveries are a separate local-run record.
