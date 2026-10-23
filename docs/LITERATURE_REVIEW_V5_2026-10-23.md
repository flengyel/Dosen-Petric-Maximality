# Literature review for *Maximality of the Došen–Petrić Boolean Category*

Review date: 23 October 2026 (UTC). Baseline: manuscript v4 at repository commit `6192328eccde5e4aa912017409289255bc8c5cb1`. Revision prepared: v5.

## Finding

The focused public-source review did not identify an earlier resolution of the exact maximality conjecture for the Došen–Petrić zero-identity Boolean category. Confidence: Medium on this negative finding; High on the distinctions between the inspected results.

The closest additional antecedent is Došen–Petrić's *Syntax for Split Preorders*, §16: its maximality argument already isolates a differing relational edge. V5 acknowledges this method, the earlier lattice/dicartesian maximality results, and the one-cross-link construction in *Isomorphic Formulae in Classical Propositional Logic*. It also distinguishes Straßburger's alternative Boolean-category axioms.

This review supports retaining the claim that the theorem disproves the conjecture stated in the September 2007 revision. It does not establish that no earlier proof exists in unsearched or inaccessible literature.

## Exact comparison target

For a nonempty variable set P, let B(P) be the free zero-identity Boolean category of Došen and Petrić. The manuscript proves that any congruence compatible with the proof operations and uniform formula substitution which identifies distinct parallel arrows identifies all parallel arrows. This is a claim about an added equation in an existing nonthin category. It is different from showing that a different collection of categorical axioms collapses immediately, or that two formulas are isomorphic.

The source is [*Proof-Theoretical Coherence*, September 2007 revision](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf). Printed p.321 states Boolean Coherence; p.322 states the nonmaximality conjecture and identifies B as the generated zero-identity Boolean category. The manuscript's substitution closure agrees with the arrow-and-type substitution rule in §2.7, p.51, and the schematic/model formulation in §9.3, p.194. The cited coherence theorem is an established input to the written argument. Its unfinished reconstruction in Lean is a separate status.

## Closest primary literature

### 1. Bicartesian coherence and maximality

Kosta Došen and Zoran Petrić, “Bicartesian coherence revisited,” in Zoran Ognjanović (ed.), *Logic in Computer Science*, Zbornik radova **12(20)** (2009), 5–34. Inspected author version: [arXiv:0711.4961v3](https://arxiv.org/html/0711.4961v3), 8 December 2008.

The abstract expressly excludes distribution. Sections 8–10 formulate substitution-closed equational maximality, prove maximality for lattice categories, and establish relative maximality for dicartesian categories. Section 10's contextual equation is a direct antecedent of the manuscript's reduction. The paper does not supply the subsequent collapse in the full zero-identity Boolean signature. V5 cites these sections in the introduction.

The earlier paper [“The Maximality of Cartesian Categories”](https://arxiv.org/abs/math/9911059), *Mathematical Logic Quarterly* **47** (2001), 137–144, provides historical context. Its abstract and bibliographic record were inspected; its complete proof was not re-audited. The closer bicartesian paper suffices for v5's concise introduction.

### 2. Occurrence selection in the same Boolean category

Kosta Došen and Zoran Petrić, “Isomorphic formulae in classical propositional logic,” *Mathematical Logic Quarterly* **58** (2012), 5–17. DOI: [10.1002/malq.201020020](https://doi.org/10.1002/malq.201020020). Inspected author version: [arXiv:0912.1271v3](https://arxiv.org/pdf/0912.1271), 4 October 2010.

Section 4 concerns the same category B. Lemma 6, author-version pp.12–13, constructs an arrow with one prescribed cross-link when the endpoints lie in the positive formula language, the implication is tautological, and the selected occurrences have the same variable. Proposition 3 characterizes isomorphism of negation-normal formulas.

This is a close antecedent for occurrence selection, but its existence statement is not the manuscript's selector/coselector factorization of an arbitrary differing parallel pair. The paper's linking equivalence is not the same as the faithful relation Gf; the text explicitly warns that linking equivalences need not compose functorially. V5 cites Lemma 6 without identifying these interpretations.

### 3. Maximality of presentations of relational categories

Kosta Došen and Zoran Petrić, “Syntax for split preorders,” *Annals of Pure and Applied Logic* **164** (2013), 443–481. Inspected author version: [arXiv:0902.0742v7](https://arxiv.org/pdf/0902.0742), 18 October 2012.

Section 16, author-version pp.55–58, proves maximality for PF, EF and RB, isomorphic respectively to the categories of split preorders, split equivalence relations and binary relations. The RB proof selects an edge in one relation but not the other, composes with selectors, obtains equality of an identity and a zero, and collapses parallel arrows.

This is a substantive methodological antecedent. It is not already the theorem for B: the available operations and endpoint objects differ. Faithfulness of B → Rel does not imply fullness or lift arbitrary relational selectors. In particular, the manuscript must construct the required selectors at its actual formula endpoints and then prove contextual collapse. V5 acknowledges the prior differing-edge method.

### 4. Alternative axioms for Boolean categories

Lutz Straßburger, “On the axiomatisation of Boolean categories with and without medial,” *Theory and Applications of Categories* **18** (2007), 536–601. [Journal record](https://www.tac.mta.ca/tac/volumes/18/18/18-18abs.html); inspected author text [arXiv:cs/0512086v3](https://arxiv.org/pdf/cs/0512086), 5 October 2007.

The introduction and relevant definitions were inspected, including the discussion of order-enriched LK-categories in §6. The hierarchy uses *-autonomous categories with monoid and comonoid structures and explicitly distinguishes this framework from Došen–Petrić's. The familiar collapse results discussed there assume additional structure, such as cartesian closure with involutive negation or natural structural maps in a *-autonomous category. They do not state maximality of B under substitution congruences.

V5 cites this paper to identify the structural distinction. Its journal version was revised in December 2007; v5's broad introductory comparison does not depend on edition-specific pagination.

The journal metadata of the three Došen–Petrić papers were checked against the authors' official publication records. The isomorphism paper's DOI also appears in retrieved bibliographic metadata; the publisher DOI endpoint was not successfully inspected.

## Additional literature screened

| Source and access | Inspected scope | Relevance to the target |
| --- | --- | --- |
| François Lamarche and Lutz Straßburger, “Constructing Free Boolean Categories,” LICS 2005, 209–218, DOI 10.1109/LICS.2005.13. [Author announcement](https://lists.seas.upenn.edu/pipermail/types-list/2005/000580.html), [author PDF address](https://www.lix.polytechnique.fr/~lutz/papers/FreeBool.pdf). | Original announcement and indexed author abstract; complete PDF access failed. | Free graphical Boolean categories in a different signature. No exact B-maximality result was identified. This is an abstract-level screen, not a full-text exclusion. |
| Carsten Führmann and David Pym, “Order-enriched categorical models of the classical sequent calculus,” *Journal of Pure and Applied Algebra* **204** (2006), 21–78, DOI 10.1016/j.jpaa.2005.03.016. [Institutional record and abstract](https://researchportal.bath.ac.uk/en/publications/order-enriched-categorical-models-of-the-classical-sequent-calcul/). | Original abstract and metadata; detailed comparison in Straßburger §6. Full original PDF unavailable. | Cut reduction is interpreted by an order on morphisms, with noncollapsing models. This is a different claim from equational maximality of B. |
| Richard McKinley, “Canonical proof nets for classical logic,” *Annals of Pure and Applied Logic* **164** (2013), 702–732; arXiv:1203.4084. [Author manuscript](https://home.inf.unibe.ch/ltg/publications/2012/mck12a.pdf). | Introduction, definitions, principal theorem statements and conclusion in the 36-page author manuscript. | Sequentialization and weakly normalizing cut elimination for expansion nets and LK*. No theorem about substitution congruences on B was identified. |
| Kosta Došen and Zoran Petrić, “Representing conjunctive deductions by disjunctive deductions,” *Review of Symbolic Logic* **10** (2017), 145–157; [arXiv:1511.05462v3](https://arxiv.org/abs/1511.05462). | Abstract/introduction and targeted full-text search. | Embeddings involving free finite-product and finite-coproduct categories; no identified resolution of the Boolean conjecture. |
| Zoran Petrić and Mladen Zekić, “Coherence for logicians,” [arXiv:2402.01285v2](https://arxiv.org/pdf/2402.01285), 25 July 2026. | Introduction, Theorem 5.9, Proposition 6.5 and §7's categorical explanation. | Kelly–Mac Lane coherence for symmetric monoidal closed categories, with 1-dimensional cobordisms as graphical target. The initial submission was in 2024; the inspected revision is from 2026. |
| Amirhossein Akbar Tabatabai, “An Introduction to Categorical Proof Theory,” [arXiv:2408.09488v2](https://arxiv.org/pdf/2408.09488), 24 March 2025. | Contents, relevant classical-logic discussion, bibliography and targeted text searches; not a complete audit of all 146 pages. | Used to discover later references and distinguish control, *-autonomous and order-enriched approaches. No exact resolution was identified through this lead. |

These sources were not added indiscriminately to v5. Only the four directly useful comparisons above were added to its bibliography. No claim is made that every result in each screened paper was checked.

## Search and citation-following record

Two web search engines were used. Queries included:

- `"zero-identity Boolean" maximality`
- `"Boolean category" "maximality" Dosen Petric`
- `"Proof-Theoretical Coherence" "maximality" Boolean`
- `"Dosen" "Petric" nonmaximality`
- `"Boolean" "maximality" "Petrić"`
- `"Proof-Theoretical Coherence" "conjecture" maximal`
- `"Boolean categories" "nonmaximality"`
- `"Boolean category" "non-maximal"`
- Title-specific searches for the papers listed above, combined with `maximality`, `collapse`, and `autonomous`.
- Public-web searches restricted to `zbmath.org` and `mathscinet.ams.org` for the book and exact target; these did not provide a usable comprehensive citation traversal.

A recent-results query for Boolean-category maximality was also run; unrelated uses of “Boolean” or “maximal” were discarded. Search-engine crawl dates were not used as publication dates.

[Došen's official publication list](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/publications.htm) was screened through its later entries, and [Petrić's current CV](https://www.mi.sanu.ac.rs/~zpetric/cv.pdf) through its 2025 publications and listed preprints. Selected later papers and bibliography leads citing the book or the bicartesian survey were followed. These lists are discovery aids, not proof that no unlisted resolution exists.

There was no comprehensive MathSciNet/zbMATH citation-index search, complete forward-citation census, or author contact. Complete PDFs for Lamarche–Straßburger and Führmann–Pym were unavailable in this review. Some versioned arXiv URLs failed; successful unversioned PDF retrievals were checked for their actual version stamps.

## Consequences for v5

1. Retain the theorem and the precisely dated September 2007 conjecture attribution.
2. Add the four references and concise comparisons identified above.
3. Preserve the theorem statements, proof, occurrence coordinates and Appendix A.
4. Retain the *Unbearable Notation of Logic* reference. The notes repository is public; GitHub also resolved the exact cited PDF at commit `a89f60bfd36f0141dee879681faa43a23e6cf321`, blob `7415c7c3c5bd841bec867cb8e69f145109401e60`.
5. Keep search limitations, review commentary and formalization status outside the manuscript.

## MSC2020

The codes were checked in the [official joint Mathematical Reviews–zbMATH MSC2020](https://msc2020.org/MSC_2020.pdf), printed pp.10–11 and 50:

| Role | Code | Official label | Reason |
| --- | --- | --- | --- |
| Primary | 03G30 | Categorical logic, topoi | The principal theorem concerns a category of classical propositional proofs. |
| Secondary | 03F07 | Structure of proofs | The result classifies additional identifications of proofs. |
| Secondary | 18A32 | Factorization systems, substructures, quotient structures, congruences, amalgams | The conclusion concerns substitution congruences and quotient categories. |

The manuscript does not claim a new cut-elimination theorem, so 03F05 was not added merely because the separate Lean project reconstructs cut elimination.

## Review boundary

The negative literature conclusion is bounded by the stated searches and access. No prior resolution was found, and no inspected theorem was shown to subsume the manuscript's result. The new source comparisons were checked separately from the manuscript's mathematical argument. Compilation, rendering, source preservation and the author-side hostile and writing reviews are recorded in the accompanying v5 verification records.
