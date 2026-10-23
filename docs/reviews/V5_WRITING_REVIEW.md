# Writing review of v5

Date: 2026-10-23. Scope: the complete LaTeX manuscript, compared with v4, with particular attention to the requested literature and MSC additions. This is an editorial review; the mathematical source audit and rendered-PDF inspection are recorded separately.

Reviewed source: `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex`.

Final reviewed SHA-256: `5d9ab4080a52a57d0e3e69bc732ada39e6911bc63cb235bb61fea17448365d2e`.

Comparison source: `arxiv-review/manuscript.tex` (v4), SHA-256 `aebd6a8be39dcbdcc1a7e5061b4e65a585de2345784011fb03d28cc3326fc93e`.

## Governing source and consultation

The governing source is Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*, the course-report copy available at [MIT CSAIL/JMLR](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf). Sections 1, 4, and 5 were consulted directly for this review. This identifies the consulted 119-page typeset copy; it does not assert byte identity with a Stanford scan or the later MAA edition. Historical access records are unchanged.

The applicable advice is to introduce and motivate the problem, keep claims precise, make statements sufficiently self-contained, introduce notation before or near use, maintain consistent notation, and use readable sentences and informative transitions. The course report also counsels accurate bibliographic details, economical display numbering, and restraint with parentheses and typographic devices (§1, especially items 5, 10–17, 24, 26; §§4–5, printed pp. 9–13). The observations below are applications of that advice, not quotations or claims that the source prescribes a particular manuscript structure.

## Actual outline and argument order

1. **Introduction.** States the maximality question and conclusion, describes the two proof stages, places the argument among related results, distinguishes the intended Boolean category, and explains the occurrence-coordinate appendix and source pagination.
2. **The Boolean proof category.** Fixes formulas and the category, states the categorical operations and equations used, defines witnessed zero arrows and substitution congruences, and states maximality.
3. **Occurrences and substitution.** Defines tagged occurrence sets and the relation interpretation, states the cited Boolean Coherence theorem, and describes normal forms, literal preservation, and substitution coordinates.
4. **Isolating an occurrence.** Introduces the contextual equation, proves occurrence isolation, and extends the equation from a selected literal to every formula by substitution.
5. **Contextual collapse.** Constructs a symmetric arrow, derives equality of product projections from the contextual equation, proves maximality, and gives the model consequence.
6. **Appendix: Substitution in occurrence coordinates.** Develops profiles and fibres, relates them to finite-ordinal coordinates, and handles shared variables and the substitution used in the maximality argument.
7. **Disclosure and references.** Retains the AI-use disclosure and provides bibliographic records.

This order matches the proof dependencies. No revised outline is warranted by the requested literature and MSC revision.

## Comparison and findings

| Item | Finding | Disposition |
|---|---|---|
| Problem and contribution | The opening states the source's question, the new conclusion, and the substitution closure required. The roadmap identifies occurrence isolation and contextual collapse as separate stages. | Retain. |
| Literature placement | The two new paragraphs follow the proof roadmap and precede the coordinate explanation. They therefore contextualize a result the reader has already been told, without interrupting a proof. | Appropriate. |
| Antecedents | The paragraph separates lattice/dicartesian maximality, occurrence selection, and relation presentations. It does not call all these results the same theorem. | Retain; the source audit supplies verification of the citations' mathematical scope. |
| Other Boolean-category frameworks | The Strassburger paragraph makes clear that the title's category has a specified source and structural assumptions. | Retain; no additional survey section is necessary. |
| Repetition | An optional deletion removed the sentence beginning “Here the selectors and coselectors…”, whose substance was already stated in the preceding proof roadmap. | Implemented and checked; no further repetition edit needed. |
| Definitions and statements | The main theorem follows definitions of the category and substitution congruence. Later constructions are introduced before their proof use. | No missing local definition found. |
| Proof readability | The selection, substitution, and collapse stages have explicit connecting prose. Displayed equations support the prose rather than replacing it. | Retain. |
| Notation and diagrams | Occurrence positions are distinguished from labels. The appendix explains the objects and maps in each diagram and relates the diagrams to substitution. | Retain. |
| MSC and keywords | The MSC2020 line and keyword line follow the abstract and precede the Introduction. The codes are presented as primary and secondary classifications. | Placement and format are suitable. Code selection was checked separately against the official classification. |
| Bibliography | Added items give full titles, author names, publication details, and public author-version or journal links. Versions and dates are bibliographic information. | Retain, subject to the source audit's factual checks. |
| Process commentary | No review instructions, audit claims, failed attempts, or revision-process comments were inserted into the manuscript or LaTeX comments. The existing AI-use disclosure is a disclosure, not review commentary. | Retain the disclosure. |

## Definition and notation audit

| Notion | Introduction and later use |
|---|---|
| `P`, `Form(P)`, and `B(P)` | Fixed at the start of Section 2, before the main theorem. The nonempty-variable assumption remains explicit. |
| Products, coproducts, units, composition, distributor, negation, and zero identity | Introduced with types or defining equations before use in witnessed zeros and collapse. |
| Zero arrows | Defined only for inhabited hom-sets, using an existing arrow and the zero law. The exposition does not silently add arrows between arbitrary endpoints. |
| Proof and substitution congruences | Defined before the maximality statement, including action on full arrow terms and endpoints. |
| Tagged occurrences and their labels | Distinguished in Section 3 and retained in substitution coordinates and the appendix, including repeated equal labels. |
| Relation interpretation and Boolean Coherence | Introduced and attributed before faithfulness is used for isolation and symmetry. |
| Contextual equation and symmetric arrow | Introduced before their lemmas and before the final collapse argument. |
| Profiles, block coordinates, and renaming | Introduced locally before the associated appendix diagrams; each map has a stated domain and codomain. |
| Standard contextual terms | “Maximality,” “dicartesian,” “coherence,” “substitution congruence,” “occurrence,” and “zero identity” are used consistently with the manuscript's subject and cited framework. No replacement by a new label is needed. |

The Introduction names other frameworks for bibliographic orientation. It does not use their technical structures in a proof before defining them; the citations are sufficient at that location.

## Prioritized recommendations

**Required editorial revisions:** none identified in the reviewed draft.

**Completed optional economy revision:** the editor deleted the last sentence of the first new literature paragraph:

> Here the selectors and coselectors have formula endpoints, and the contextual-collapse argument uses the zero identities and distributor.

The preceding roadmap already states these features. Deletion reduces repetition without changing a claim. This was an editorial preference, not a source-mandated correction or a mathematical defect. No manuscript edit was made by this reviewer; the editor's deletion was checked in the final source. The final wording “split equivalence relations” and the explicitly dated author version for *Isomorphic formulae in classical propositional logic* were also reread after the source audit's corrections.

The sentence “Other axiomatizations of Boolean categories use different structures.” was reread after a final typesetting adjustment. It preserves the intended comparison and reads naturally with the following sentence identifying Strassburger's framework. The recorded source hash includes this final adjustment.

**Do not broaden the revision:** retain the existing proof and appendix, avoid adding a formalization-progress discussion to the mathematical argument, and avoid expanding the focused related-work paragraphs into a survey unsupported by the source audit.

## Preservation and remaining checks

The direct v4–v5 source diff contains the date change, MSC and keywords, two introductory literature paragraphs, four bibliography items, and a final blank line. It contains no change to theorem statements, hypotheses, proofs, mathematical definitions, or appendix diagrams.

The source therefore passes this writing review for the requested revision. This report does not claim that compilation proves mathematical correctness, that the incomplete Lean formalization is complete, or that a literature search certifies novelty. Compilation, citation resolution, line breaking, page layout, and rendered diagram placement require the separately recorded PDF checks.

Final production check: removal of the extra blank line at end of file made no prose or mathematical change. The source hash above includes that whitespace correction.
