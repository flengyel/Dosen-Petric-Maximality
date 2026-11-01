# Text prepared for public display

## Registry title

Maximality of the Došen–Petrić Boolean Category

## Registry abstract

Let P be a nonempty set of propositional variables. The freely generated zero-identity Boolean category B(P) of Došen and Petrić is maximal: every congruence on its arrows preserved by the arrow operations and uniform formula substitution is either equality or identifies every pair of parallel arrows. The formalization gives two proofs of maximality and proves the congruence dichotomy. It also proves that the identity and zero endomorphism of each variable are distinct, and that there is no arrow from the terminal object to the initial object.

## Challenge opening

The formulas, arrow terms and equations below present the zero-identity
Boolean category of Došen and Petrić. Two arrow terms represent the same
arrow if and only if `Derives` relates them.

For `f : Term P A B` and `g : Term P B C`,
`Term.comp f g : Term P A C` applies `f` and then `g`.

## Complete metadata in reading order

### version

v0.4

### project.name

Maximality of the Došen–Petrić Boolean Category

### project.description

Let P be a nonempty set of propositional variables. The freely generated zero-identity Boolean category B(P) of Došen and Petrić is maximal: every congruence on its arrows preserved by the arrow operations and uniform formula substitution is either equality or identifies every pair of parallel arrows. The formalization gives two proofs of maximality and proves the congruence dichotomy. It also proves that the identity and zero endomorphism of each variable are distinct, and that there is no arrow from the terminal object to the initial object.

### project.authors[0]

Florian Lengyel

### project.responsible_maintainers[0]

Florian Lengyel

### project.license

Apache-2.0

### classification.arxiv[0]

math.CT

### classification.arxiv[1]

math.LO

### classification.msc2020[0]

03G30

### classification.msc2020[1]

03F07

### classification.msc2020[2]

18A32

### sources[0].title

Maximality of the Došen–Petrić Boolean Category, version 13

### sources[0].authors[0]

Florian Lengyel

### sources[0].type

paper

### sources[0].relationship

formalizes

### sources[0].id

https://github.com/flengyel/Dosen-Petric-Maximality/blob/84d913d4ab30490ddf9c51788ed89ea5c7e9a601/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v13.tex

### sources[0].location

Theorem 2.1; Sections 2–6; Appendices A–C; October 31, 2026.

### sources[0].author_endorsement

participated

### sources[0].note

The manuscript states maximality as Theorem 2.1, gives the q_A/e_A proof in Sections 4–5 and the symmetric-fold proof in Section 6, and states the model corollary as Corollary 5.3. Section 3 and Appendices A–C give the occurrence, substitution, diagram and rank results identified in the scope and correspondence fields below. The Lean development formalizes these results; the five registry declarations state the maximality and separation results listed below.

### sources[1].title

Proof-Theoretical Coherence

### sources[1].authors[0]

Kosta Došen

### sources[1].authors[1]

Zoran Petrić

### sources[1].type

book

### sources[1].relationship

formalizes

### sources[1].id

https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf

### sources[1].location

King's College Publications, 2004; revised author version September 2007; the zero-identity Boolean presentation in Sections 14.2–14.3 and the cut-elimination and coherence arguments used by that presentation.

### sources[1].author_endorsement

not-contacted

### sources[1].note

The development proves the cut-elimination and coherence results used for the category presented in Sections 14.2–14.3. The maximality theorem is stated in Lengyel's manuscript. Appendix C of manuscript v13 corrects the rank comparisons on pp.260 and 262; the corresponding Lean equations and inequalities are listed below.

### sources[2].title

Isomorphic formulae in classical propositional logic

### sources[2].authors[0]

Kosta Došen

### sources[2].authors[1]

Zoran Petrić

### sources[2].type

paper

### sources[2].relationship

background

### sources[2].id

https://doi.org/10.1002/malq.201020020

### sources[2].location

Mathematical Logic Quarterly 58 (2012), 5–17; Lemma 7; author version arXiv:0912.1271v3.

### sources[2].author_endorsement

not-contacted

### sources[2].note

Lemma 7 constructs an isomorphism from a bijection of occurrences. Manuscript v13, Section 5, relates this construction to the displayed q_A and e_A arrows. ShortProof.q_definition, ShortProof.e_definition and their inverse equations prove that these arrows are isomorphisms in the category presented by the defining equations.

### status.scope

The five selected declarations state two proofs of maximality, the congruence dichotomy, the distinction between the identity and zero endomorphism of each variable, and the absence of an arrow from the terminal object to the initial object. The first three declarations assume that P is nonempty, as in manuscript v13, Theorem 2.1. Version 1 is registered as PALOMAR-2026-10-30-000014 at source 2e771844077fd8cebfbe365230f13d4dd13a75b1. This prose correction is prepared for an ordinary update under the same identifier; version 1 and its source remain available.

The development also proves cut elimination and Boolean coherence. The declarations DosenPetric.Reduced.Gentzen.cut_elimination and atomized_cut_elimination are in DosenPetric/GentzenCutElimination.lean. DosenPetric.Presentation.coherence is in DosenPetric/PresentationCoherence.lean and corresponds to manuscript v13, Theorem 3.1. These results supply the cut-elimination and coherence inputs from Proof-Theoretical Coherence.

The model corollary is manuscript v13, Corollary 5.3. DosenPetric.PresentationSemantics.model_corollary and model_corollary_interpretations, in DosenPetric/SemanticModelCorollary.lean, prove the conclusion for models of the full presentation, using agreement under all valuations and interpretations.

Manuscript v13, Section 3 and Appendix A, describe occurrence substitution by tagged blocks and finite-ordinal coordinates. DosenPetric.Formula.expand and contract are inverse bijections. Formula.substitution_count and substitution_index in DosenPetric/FormulaSubstitutionOrdinals.lean, and PatternProfiles.actual_ordinal_square in DosenPetric/PatternSubstitutionOrdinals.lean, identify the tagged construction with the finite-ordinal coordinates. ProfileComposition.Data.coordinate_oneBased in DosenPetric/ProfileComposition.lean gives the one-based coordinate formula.

Manuscript v13, Appendix B, displays the first-injection triangle, the five-arrow zero-identity path and the zero-law square for equations (1), (2) and (3). DosenPetric.Presentation.ManuscriptDiagrams.first_triangle, zero_diagram, zero_primitive and zero_square, in DosenPetric/ManuscriptStructuralDiagrams.lean, prove their identities.

Manuscript v13, Appendix C, corrects two rank descriptions in Proof-Theoretical Coherence. For p.260, DosenPetric.Reduced.Gentzen.BlockedLeftDisj.gamma_equation and gamma_first_descent/gamma_second_descent prove the equation and both strict recursive rank comparisons; see DosenPetric/GentzenBlockedLeftGammaDisj.lean and GentzenBlockedLeftGammaDisjRank.lean. For p.262, BlockedDisjFirst.source_equation, fresh_principal_rank, fresh_total_rank and fresh_total_rank_ge_two prove the equation, the fresh right rank of one and the total rank of at least two; see DosenPetric/GentzenBlockedDisjFirstEquation.lean and GentzenAppendixCFreshRight.lean.

The complete mathematical source is 630c4b6e47da16a1434476a211fd29ce6adc5569. The exhaustive correspondence for manuscript v13 is docs/MANUSCRIPT_COMPLETE_CLAIM_MAP.md at commit 84d913d4ab30490ddf9c51788ed89ea5c7e9a601. The additional results above belong to the full development; the Comparator selection consists of the five declarations listed in alignment.statements.

### status.sorry_count

0

### status.sorry_in_definitions

0

### status.axioms[0]

propext

### status.axioms[1]

Quot.sound

### status.axioms[2]

Classical.choice

### automation.methods[0].method

agent

### automation.methods[0].framework

OpenAI Codex / ChatGPT

### automation.methods[0].tool_setup

Local WSL Codex developed Lean proofs and ran builds and audits. ChatGPT research/review sessions prepared mathematical instructions, inspected source and evidence, and reviewed the manuscript and its correspondence with the formal statements. Exact historical model identifiers and aggregate costs are not reconstructed here.

### automation.notes

Florian Lengyel is the human author and responsible maintainer. The author supplied the mathematical objective, corrected scope and presentation, and requested the complete-paper formalization. AI systems are credited here rather than listed as authors. The manuscript contains the author's authorized disclosure of ChatGPT assistance.

### fidelity.divergences

The three maximality declarations retain the manuscript's nonempty-variable hypothesis. PrimitiveCongruence is an equivalence relation on parallel typed arrow terms that contains every defining equation and is preserved by composition, conjunction and disjunction. Its Closed property requires preservation under uniform formula substitution on the terms and both endpoints. Derives is the equivalence relation generated by the defining equations and closed under those three arrow operations.

DosenPetric/PalomarCorrespondence.lean proves descent from terms to the quotient by Derives, restriction of full proof congruences to terms, pointwise relation correspondence, preservation of substitution closure and totality, correspondence of distinctness, and preservation by derived negation. The extension from a congruence closed under substitution to a full proof congruence uses the proved fragment dichotomy. The short proof uses occurrence isolation, ContextualCollapse.all_contexts and ShortProof.total with the q_A/e_A arrows. All quantification over parallel arrows preserves empty hom-sets, and repeated occurrences retain distinct tags. The metadata makes no priority claim or claim to an exhaustive novelty assessment.

### review.status

agent-reviewed

### review.reviewers[0]

OpenAI Codex local source and manuscript reviews

### review.reviewers[1]

ChatGPT source, evidence and mathematical-writing reviews through manuscript v13

### review.notes

The author-side full-development reviews are docs/reviews/FULL_PAPER_6A66B14_REVIEW.md and FULL_PAPER_6A66B14_WRITING.md. The statement and definition correspondence reviews are docs/reviews/PALOMAR_REGISTRATION_REVIEW.md and PALOMAR_REGISTRATION_WRITING.md. The manuscript v13 statement, literature and hostile reviews are docs/reviews/V13_STATEMENT_REVIEW_2026-10-31.md, V13_LITERATURE_REVIEW_2026-10-31.md and V13_HOSTILE_REVIEW_2026-10-31.md at commit 84d913d4ab30490ddf9c51788ed89ea5c7e9a601. These are AI-assisted author-side reviews. The registered version-1 automated Palomar review identified no blocking problem; docs/PALOMAR_REGISTRATION_REPORT.md records its separate mechanical, review and registration evidence. This account does not claim a service review or registration for the prose update. Independent-kernel outcomes for version 1 are recorded in docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md.

### alignment.namespace

DosenPetric.Palomar

### alignment.statements[0].source

Manuscript v13, Theorem 2.1; symmetric-fold proof in Section 6.

### alignment.statements[0].lean

DosenPetric.Palomar.maximality

### alignment.statements[0].module

Solution

### alignment.statements[0].status

proved

### alignment.statements[0].note

The symmetric-fold proof uses Presentation.fragment_maximality for the quotient by Derives. DosenPetric/PalomarCorrespondence.lean proves the relation correspondence between terms and quotient arrows.

### alignment.statements[1].source

Manuscript v13, Theorem 2.1; q_A/e_A proof in Sections 4–5.

### alignment.statements[1].lean

DosenPetric.Palomar.short_maximality

### alignment.statements[1].module

Solution

### alignment.statements[1].status

proved

### alignment.statements[1].note

The q_A/e_A proof uses Isolation.normalized_literal_context, ContextualCollapse.all_contexts and ShortProof.total. Its proof is independent of the invocation of fragment_maximality in the symmetric-fold proof.

### alignment.statements[2].source

Manuscript v13, Theorem 2.1, equality/totality dichotomy.

### alignment.statements[2].lean

DosenPetric.Palomar.congruence_dichotomy

### alignment.statements[2].module

Solution

### alignment.statements[2].status

proved

### alignment.statements[2].note

Equality of quotient arrows is the relation Derives on their representatives. The correspondence with full proof congruences and the preservation of totality are proved in DosenPetric/PalomarCorrespondence.lean.

### alignment.statements[3].source

Manuscript v13, Section 3, nonzero variable identity.

### alignment.statements[3].lean

DosenPetric.Palomar.identity_ne_zero

### alignment.statements[3].module

Solution

### alignment.statements[3].status

proved

### alignment.statements[3].note

Presentation.identity_ne_primitive_zero proves that the variable identity differs from the primitive zero endomorphism in the quotient by Derives.

### alignment.statements[4].source

Manuscript v13, Sections 2–3, empty terminal-to-initial hom-set.

### alignment.statements[4].lean

DosenPetric.Palomar.no_top_to_bot

### alignment.statements[4].module

Solution

### alignment.statements[4].status

proved

### alignment.statements[4].note

Presentation.empty_hom, proved by the truth interpretation, rules out any arrow term from the terminal object to the initial object.

### alignment.broader_correspondence.manuscript

https://github.com/flengyel/Dosen-Petric-Maximality/blob/84d913d4ab30490ddf9c51788ed89ea5c7e9a601/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v13.tex

### alignment.broader_correspondence.claim_map

https://github.com/flengyel/Dosen-Petric-Maximality/blob/84d913d4ab30490ddf9c51788ed89ea5c7e9a601/docs/MANUSCRIPT_COMPLETE_CLAIM_MAP.md

### alignment.broader_correspondence.scope

The scope field identifies the manuscript anchors, Lean declarations and source modules for cut elimination, Boolean coherence, the model corollary, occurrence substitution and its finite-ordinal coordinates, all three Appendix B diagrams, and the Appendix C rank comparisons. These results are part of the development and are not additional Comparator selections.

## Complete Challenge documentation in source order

### Documentation block 1

```lean
/-!
The formulas, arrow terms and equations below present the zero-identity
Boolean category of Došen and Petrić. Two arrow terms represent the same
arrow if and only if `Derives` relates them.

For `f : Term P A B` and `g : Term P B C`,
`Term.comp f g : Term P A C` applies `f` and then `g`.
-/
```

### Documentation block 2

```lean
/-- Tagged positions distinguish repeated occurrences of a variable. -/
```

### Documentation block 3

```lean
/-- Conjunction and disjunction are the two covariant binary arrow operations. -/
```

### Documentation block 4

```lean
/-- The arrow terms follow the primitive grammar C(B) in the September 2007
revision of Proof-Theoretical Coherence, pp.310,312,316.
The term `comp f g` denotes the book's g ∘ f, and `swap .disj A B` denotes
its c_(B,A). Negation on arrows, pairing, copairing, and dR are derived
operations. -/
```

### Documentation block 5

```lean
/-- Pairing is defined by the diagonal and conjunction, as on p.187. -/
```

### Documentation block 6

```lean
/-- Copairing is defined by disjunction and the codiagonal, as on p.198. -/
```

### Documentation block 7

```lean
/-- The arrow to the terminal object is defined as on p.191. -/
```

### Documentation block 8

```lean
/-- The arrow from the initial object is defined as on p.207. -/
```

### Documentation block 9

```lean
/-- The right distributor is defined by (dR c), p.145, with the disjunctive symmetry indices translated. -/
```

### Documentation block 10

```lean
/-- The medial arrow occurs in equation (b c w), p.186. -/
```

### Documentation block 11

```lean
/-- The composite in (0ηε), p.317, defines the zero endomorphism. -/
```

### Documentation block 12

```lean
/-- The letterless formulas of the inherited positive language, p.121. -/
```

### Documentation block 13

```lean
/-- The defining equations of E(B), pp.316–317, include those inherited from
E(DL_top,bot), E(L_top,bot), E(DS), E(MS), and E(I^neg_top,bot). -/
```

### Documentation block 14

```lean
/-- (cat 1), p.332 -/
```

### Documentation block 15

```lean
/-- (cat 1), p.332 -/
```

### Documentation block 16

```lean
/-- (cat 2), p.332 -/
```

### Documentation block 17

```lean
/-- (xi 1), p.332 -/
```

### Documentation block 18

```lean
/-- (xi 2), p.332 -/
```

### Documentation block 19

```lean
/-- (bR nat), p.332 -/
```

### Documentation block 20

```lean
/-- (bL nat), p.332 -/
```

### Documentation block 21

```lean
/-- (b b), p.333 -/
```

### Documentation block 22

```lean
/-- (b b), p.333 -/
```

### Documentation block 23

```lean
/-- (b 5), p.89; list p.333 -/
```

### Documentation block 24

```lean
/-- (c nat), p.333; disjunctive indices reversed -/
```

### Documentation block 25

```lean
/-- (c c), p.107; list p.334 -/
```

### Documentation block 26

```lean
/-- (b c), p.107; list p.334 -/
```

### Documentation block 27

```lean
/-- (delta/sigma nat), pp.332–333 -/
```

### Documentation block 28

```lean
/-- (delta/sigma nat), pp.332–333 -/
```

### Documentation block 29

```lean
/-- (delta delta)/(sigma sigma), p.101 -/
```

### Documentation block 30

```lean
/-- (delta delta)/(sigma sigma), p.101 -/
```

### Documentation block 31

```lean
/-- (delta/sigma nat), pp.332–333 -/
```

### Documentation block 32

```lean
/-- (delta/sigma nat), pp.332–333 -/
```

### Documentation block 33

```lean
/-- (delta delta)/(sigma sigma), p.101 -/
```

### Documentation block 34

```lean
/-- (delta delta)/(sigma sigma), p.101 -/
```

### Documentation block 35

```lean
/-- (b delta sigma), p.101 -/
```

### Documentation block 36

```lean
/-- (w nat), p.333 -/
```

### Documentation block 37

```lean
/-- (w nat), p.333 -/
```

### Documentation block 38

```lean
/-- (k1 nat), p.333 -/
```

### Documentation block 39

```lean
/-- (k1 nat), p.333; disjunctive indices translated -/
```

### Documentation block 40

```lean
/-- (k2 nat), p.333 -/
```

### Documentation block 41

```lean
/-- (k2 nat), p.333; disjunctive indices translated -/
```

### Documentation block 42

```lean
/-- (b w), p.186 -/
```

### Documentation block 43

```lean
/-- (b w), dual p.186; list p.336 -/
```

### Documentation block 44

```lean
/-- (c w), p.186 -/
```

### Documentation block 45

```lean
/-- (c w), dual p.186; list p.336 -/
```

### Documentation block 46

```lean
/-- (b c w), p.186 -/
```

### Documentation block 47

```lean
/-- (b c w), dual p.186; list p.336 -/
```

### Documentation block 48

```lean
/-- (b k), p.186 -/
```

### Documentation block 49

```lean
/-- (b k), dual p.186; list p.336 -/
```

### Documentation block 50

```lean
/-- (c k), p.186 -/
```

### Documentation block 51

```lean
/-- (c k), dual p.186; list p.336 -/
```

### Documentation block 52

```lean
/-- (w k), p.186 -/
```

### Documentation block 53

```lean
/-- (w k), dual p.186; list p.336 -/
```

### Documentation block 54

```lean
/-- (w k), p.186 -/
```

### Documentation block 55

```lean
/-- (w k), dual p.186; list p.336 -/
```

### Documentation block 56

```lean
/-- (k delta), p.191 -/
```

### Documentation block 57

```lean
/-- (k delta), dual p.191; list p.338 -/
```

### Documentation block 58

```lean
/-- (c bottom)/(c top), p.121, inherited by p.207 -/
```

### Documentation block 59

```lean
/-- (dL nat), p.333 -/
```

### Documentation block 60

```lean
/-- (dR nat), p.333, dR defined by p.145 -/
```

### Documentation block 61

```lean
/-- (dL and), p.132 -/
```

### Documentation block 62

```lean
/-- (dL or), p.132 -/
```

### Documentation block 63

```lean
/-- (dR and), p.132 -/
```

### Documentation block 64

```lean
/-- (dR or), p.132 -/
```

### Documentation block 65

```lean
/-- (d b and), p.132 -/
```

### Documentation block 66

```lean
/-- (d b or), p.132 -/
```

### Documentation block 67

```lean
/-- (m nat), p.333 -/
```

### Documentation block 68

```lean
/-- (b m), section 8.2; list p.336 -/
```

### Documentation block 69

```lean
/-- (c m), section 8.4; list p.336 -/
```

### Documentation block 70

```lean
/-- (w m), p.219 -/
```

### Documentation block 71

```lean
/-- (d k and), p.234 -/
```

### Documentation block 72

```lean
/-- (d k or), p.234 -/
```

### Documentation block 73

```lean
/-- (d m), p.234 -/
```

### Documentation block 74

```lean
/-- (0I), p.288, inherited p.317 -/
```

### Documentation block 75

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 76

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 77

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 78

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 79

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 80

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 81

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 82

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 83

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 84

```lean
/-- n-r/rho isomorphism equations, pp.310,312 -/
```

### Documentation block 85

```lean
/-- The relation `Derives` is the equivalence relation on parallel arrow terms
generated by the defining equations and closed under composition and the
conjunction and disjunction operations. Uniform substitution preserves this
relation. -/
```

### Documentation block 86

```lean
/-- An equivalence relation on parallel arrow terms that contains every
defining equation and is preserved by composition, conjunction and
disjunction. -/
```

### Documentation block 87

```lean
/-- A congruence is closed under uniform substitution if it relates the
substituted terms whenever it relates the original terms. Substitution acts
on both endpoint formulas as well. -/
```

### Documentation block 88

```lean
/-- A congruence is total if it relates every pair of parallel arrow terms. -/
```
