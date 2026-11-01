# V13 literature review

31 October 2026. Input: manuscript v12 at
`cbcd59ca1b9382bdcd0de8c648e4a351495ccf81`. Corrections appear in v13.
The introduction contains the literature discussion; no separate survey section
has been added merely to accommodate more references.

## Search and result

This pass searched for the exact Boolean maximality problem, zero-identity
Boolean/distributive categories, the §14.2 conjecture, maximality of cartesian
and cartesian closed categories, occurrence isolation and split relations,
proof-net coherence, and later work on Boolean categories and identity of
proofs. Searches used both available web indexes, the authors' publication
lists, arXiv records and linked author or publisher copies. Later-work searches
included material after 2015. These searches are not an exhaustive bibliography
or a proof of priority.

No earlier proof of this exact zero-identity Boolean maximality result was found
in the inspected material. The manuscript says which conjecture it disproves;
it does not add an unsupported claim to be first, unique, or a generalization
of every result discussed below.

Two bibliography entries have been added: Došen–Petrić on cartesian closed
maximality, and their proof-net coherence paper. Their book's zero-identity
distributive results are now included through the existing book citation.
An omitted hypothesis in the occurrence-selection citation is corrected.

## Results used or compared

| Primary source and locator | Statement or construction checked | Relation to this paper and action |
| --- | --- | --- |
| Došen–Petrić, [Proof-Theoretical Coherence](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), September 2007 revision, §14.2 p.322 | The conjecture for the freely generated zero-identity Boolean category. | Exact target of the paper. Retain the edition and printed page convention. |
| Same, §9.3 p.194; §9.7 pp.215–216 | Universal-equation notion of maximality and contextual reduction used for relative maximality. | The model corollary quantifies over every interpretation; the selected contextual equation has the required endpoints. No fixed interpretation kernel is substituted for that quantification. |
| Same, §12.5 p.292 | Maximality of zero-identity distributive lattice categories without truth constants; relative maximality with both constants. | A close antecedent omitted from the prior introduction. Add the exact distinction. Do not identify the positive signature with the Boolean signature. |
| Same, §12.5 p.294 | Isomorphism types including the endpoints of q_p and e_p. | Used in the short proof. Coherence and the possible product swap identify the particular displayed arrows; the existence of an endpoint isomorphism alone would not do so. |
| Došen–Petrić, [The maximality of cartesian categories](https://arxiv.org/abs/math/9911059), §5 | Coherence, substitution and composition reduce an additional equation to equality of projections. | Retain as a proof-method antecedent. The source has finite products and does not prove the Boolean result merely by inclusion of operations. |
| Došen–Petrić, [The maximality of the typed lambda calculus and of cartesian closed categories](https://arxiv.org/abs/math/9911073), §11 | Typed Böhm separation yields equal projections and collapse under an additional nonderivable equation. | Add citation and method. The theorem does not apply to B because p⇒p does not exist. The source credits earlier results of Statman and Simpson; the manuscript does not assign exclusive priority to these authors. |
| Došen–Petrić, [Bicartesian coherence revisited](https://arxiv.org/abs/0711.4961), §§8–10 | Lattice maximality and relative maximality for dicartesian categories; limitations of stronger general claims. | Retain the precise qualifiers and “without assuming distribution”. This later account is preferred to relying on the earlier paper's unrevised proof. |
| Došen–Petrić, [Isomorphic formulae in classical propositional logic](https://arxiv.org/abs/0912.1271), Lemmas 6–7 | Lemma 6 selects an edge between prescribed occurrences of one variable for negation-free A,B with A→B tautological. Lemma 7 constructs isomorphisms using prescribed label-respecting occurrence bijections under its hypotheses. | Correct the omitted negation-free hypothesis. The q/e application involves only positive p and constants; it falls within the needed construction. |
| Došen–Petrić, [Syntax for split preorders](https://arxiv.org/abs/0902.0742), §16 | Isolating a pair in one relation but not another proves maximality for the stated relational presentations. | Retain as an antecedent of the isolation method; do not claim that its objects, operations and congruence are those of B. |
| Došen–Petrić, [Coherence of proof-net categories](https://arxiv.org/abs/math/0503301), introduction; PN¬ and MPN¬ Coherence | Faithful functors to Brauerian split equivalences for the proof-net categories for multiplicative linear logic without constants, with and without mix. | Add a brief comparison specifying the graph category. Brauerian split equivalences are not the arbitrary binary relations of G:B→Rel_fin. |
| Lamarche–Straßburger, [Constructing free Boolean categories](https://www.lix.polytechnique.fr/~lutz/papers/FreeBool.pdf), proceedings Theorem 3.5.4 | Freeness for graphical, Δ–∇-strong K-flat and K-sharp autonomous categories. | Retain these hypotheses and the proceedings locator. The expanded preprint uses different organization/wording; do not silently transfer its theorem labels. Categorical products and coproducts are not imposed as in B. |
| Straßburger, [On the axiomatisation of Boolean categories with and without medial](https://www.tac.mta.ca/tac/volumes/18/18/18-18abs.html), introduction and defining structures | Equations on monoid/comonoid structures in star-autonomous categories. | Retain as a different axiom system. No maximality transfer is asserted. |
| Führmann–Pym, [Order-enriched categorical models of the classical sequent calculus](https://carstenfuehrmann.org/papers/order-enriched-models-for-classical-sequent-calculus.pdf), (11) and Theorems 6.4–6.5 | The negation triangle equates the indicated composite with the unit isomorphism; net-theory inequalities are exactly those holding under every interpretation of the theory in the stated classical categories. | Replace “ordered soundness and completeness” by this quantified assertion. With unit isomorphisms the manuscript's zero-defining composite would equal 1_A under those equations; in B it equals 0_A. This is an explicit difference of axioms, not a claim of inconsistency in either source. |
| DP book, §14.3 p.324 | Joyal collapse in the stated CCC/initial-object/double-negation form. | Replace “concerns ... a dualizing object” by the exact condition, then retain the independent proof that B is not CCC. |
| Lengyel, [The Unbearable Notation of Logic v8](https://github.com/flengyel/notes/blob/main/logic/The-Unbearable-Notation-of-Logic_v8.pdf), §9 | Tagged occurrence/block notation. | Not a novelty antecedent for maximality. The mathematical substitution construction is checked directly against DP p.46 and the appendix equations. |

## Corrected overstatement: Lemma 6

V12 §1, lines 79–81, says that the lemma links two prescribed occurrences of
the same variable provided the implication is a tautology. The source states
the lemma for formulas in the language containing constants, conjunction and
disjunction, without negation. That condition matters.

A small counterexample to the unrestricted reading is A=p and B=¬p∨p.
The implication A→B is tautological. Select the occurrence of p in A and the
negative occurrence in B. Every relation edge of an arrow between these
negation-normal formulas preserves the signed literal, so no such arrow has
the prescribed edge. Minimality of this example is not asserted.

V13 states the negation-free condition explicitly. The manuscript's own
Lemma 4.1 already chooses an edge whose ends have the same signed literal,
so this finding changes neither that lemma nor the registered proof.
The previous v12 review's claim to have supplied the cited lemma's hypothesis
was incomplete; its historical report is preserved, and this report corrects it.

## Additional works inspected and disposition

| Work | Actual inspection | Disposition |
| --- | --- | --- |
| Došen–Petrić, [Bicartesian Coherence](https://arxiv.org/abs/math/0006052) | Downloaded primary paper; introduction and comparison with the later survey. | Existing citation to the revised account is more useful for the stated maximality comparison. No redundant entry added. |
| Hyland, [Abstract Interpretation of Proofs: Classical Propositional Calculus](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2004/aap04.pdf) (2004) | Introduction and Definitions 1–2 concerning compact closed models with chosen monoid/comonoid structures. | Relevant to categorical proof identity, but these inspected passages do not supply the B congruence theorem. Existing comparisons already exhibit the relevant difference of operations; no extra citation added solely for breadth. |
| Pistone, [A New Conjecture about Identity of Proofs](https://arxiv.org/abs/2110.02630) (2021 preprint; 2024 chapter) | Introduction and conclusion on naturality and proof identity. | A distinct conjecture and program. No exact Boolean maximality result established by the inspected passages. No claim to have checked every theorem in this work. |
| Došen–Petrić, [Representing Conjunctive Deductions by Disjunctive Deductions](https://arxiv.org/abs/1511.05462), v3 (2016) | Abstract and introduction: embedding a free product category into a free coproduct category up to equivalence. | Different categorical representation question; no maximality transfer follows. |
| McKinley, [Canonical Proof nets for Classical Logic](https://arxiv.org/abs/1203.4084) | Abstract only: expansion-net sequentialization and cut elimination. | Potential proof-identity context. Not counted as a fully reviewed source or evidence excluding priority. |
| Hughes–Straßburger–Wu, [Combinatorial Proofs and Decomposition Theorems for First-order Logic](https://arxiv.org/abs/2104.13124) | Abstract only: first-order combinatorial proofs, soundness and full completeness. | Different language and result. Not counted as a fully reviewed source or used to infer absence of a related theorem. |
| Krenicky, *A 2-Categorical Approach to Proof-Comparison* (Manchester thesis, 2013) | Official repository abstract only. | Weak 2-categorical proof comparison; full thesis not inspected. No theorem-level exclusion asserted. |
| Došen–Petrić, modal coherence/maximality, [arXiv:0809.2494](https://arxiv.org/abs/0809.2494) | Search/abstract lead only. | Different signature. Not treated as a checked antecedent for the Boolean theorem. |

The search also encountered Boolean restriction categories and coherent
categories in other senses. The shared adjective “Boolean” does not identify
their objects, morphisms, operations or equation theory with the category here.
No generalization claim is inferred from terminology.

## Source edition and bibliography checks

The new CCC reference is *Publications de l'Institut Mathématique* (N.S.)
68(82) (2000), 1–19; the inspected arXiv copy is v2, 25 September 2012.
The new proof-net reference is the same journal, 78(92) (2005), 1–33,
DOI [10.2298/PIM0578001D](https://doi.org/10.2298/PIM0578001D).
Author lists, titles, publication information and author-copy links were
cross-checked against primary records. The book's p.292 result and p.294
isomorphism list are separate locators and are cited separately.

The source manifest records PDF hashes and the passages actually inspected.
Downloaded third-party PDFs are not included in the repository or upload
archive. The user's exact Palomar BibTeX entry is unchanged. Thirteen references
are used in v13; no uncited bibliography item was added as padding.

The literature check does not certify originality, inspect every subsequent
paper, or establish publication suitability. It does establish the cited
qualifications recorded above and the concrete difference between the main
comparison categories. No source found in this pass establishes that the
manuscript's formal theorem is false.

Reports are retained in the repository. This environment cannot deliver or
verify new copies in the author's Windows Downloads directory.
