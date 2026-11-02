# Review of v22: correctness, citations and mathematical writing

2 November 2026. Reviewed *Maximality of the Došen–Petrić Boolean Category*, v22, at commit `5b515365f5d5164ba65c91ab3571fd2f475a0b66`. The source has 1,767 lines and the PDF has 23 pages. Four parallel author-side reviews covered the written arguments, primary citations, exposition, and registered Lean correspondence; the findings were reconciled against the source. This is not human peer review.

No fatal or major mathematical defect was found in the checked arguments. The seven numbered statements, both maximality proofs, and the model corollary survive the review. The abstract makes sense. The introduction needs a focused revision: its catalogue of related results obscures their different roles. Appendix C must identify its dependency on Došen and Petrić’s Boolean Coherence proof and show the decreasing rank in the second corrected case.

This report supplies complete proposed replacements and exact local edits. It does not release a revised manuscript or change the registered proof. Apply accepted revisions in v23 or the next unused version; preserve v22.

## (A) Kill-shots / hard blockers

None confirmed. In particular, the paper does not assume that all hom-sets are nonempty, apply coherence to the collapsed quotient, omit the negative-literal case, or replace universal agreement in a model by agreement under one interpretation.

The two erroneous rank claims are in the cited book. The registered Lean source already proves the corrected inequalities and uses them in the induction. No missing Lean proof was identified.

## (B) Major weaknesses

No major correctness or citation defect confirmed. Appendix D.5 describes a coherence proof using substantial constituent results; it does not reproduce every cut-elimination, atomization, and common-factorization derivation. The main proof legitimately cites Boolean Coherence. That scope must not be confused with a self-contained reproof of its full dependency chain.

## (C) Minor issues and exact repairs

### Actual outline

| Section | Function and dependency |
|---|---|
| Abstract | Main result and contrary conjecture; proof outline; model corollary; formalization. |
| 1 Introduction | Problem, conjecture and contribution; proof outline; antecedents; alternative categorical semantics; occurrence notation; roadmap. |
| 2 The Boolean proof category | Presentation, composition, zero law, congruences and quotient; statement of Theorem 2.1. |
| 3 Occurrences and substitution | Tagged occurrence sets and relations; Boolean Coherence; signs and literals; normalization; substitution functors and their composition. |
| 4 Isolating an occurrence | Context equation, isolation lemma, passage to retracts and extension by uniform substitution to every formula. |
| 5 Equality of the product projections | Two isomorphisms, collapse lemma, completion of maximality proof and model corollary. |
| 6 Lean formalization | Formalization setup; a second mathematical proof using mix; union and hom-set semilattices; implementation and registration scope. |
| A Substitution in occurrence coordinates | Occurrence maps and fibres; finite-ordinal presentation; shared variables and application to maximality. |
| B Diagrams for three defining equations | First-injection triangle, zero-identity diagram and zero-law square. |
| C Two corrections to the cut-elimination proof | Two precise rank corrections to the cited source. |
| D The registered Lean theorems | Arrow terms and equations; reading a declaration; five statements; term/arrow congruence correspondence; construction of coherence proof. |
| E Inverses of q_A and e_A | Explicit inverse of q_A; explicit inverse of e_A; split comparisons used in coherence. |
| Use of AI tools and bibliography | Author-requested disclosure and references. |

The theorem depends on coherence and normalization, isolation, substitution, and the two isomorphisms. The model corollary then uses congruence under all interpretations. The alternative proof replaces the isomorphism argument by the symmetric mix argument. Appendix A has a distinct mathematical purpose and should remain.

### Findings

| Anchor in v22 | Finding and evidence | Repair |
|---|---|---|
| Abstract, p.1, lines35–38 | Two consecutive “We also” sentences. Local repetition, not an unclear theorem. | Remove the earlier “also”; preserve the approved Lean sentence. |
| Introduction, p.1, lines65–73 | The proof outline passes from isolation to the two isomorphisms without mentioning the substitution step. The full proof supplies it. | Add the sentence about uniform substitution in the replacement below. |
| Introduction, p.1, lines80,83 | The symbol B is used before its declaration in §2, lines140–145. | Remove the premature symbols in the replacement. |
| Introduction, pp.1–2, lines75–116 | The succession of category classes is a literature catalogue. The standalone proof-net paragraph states no use or comparison. This is a relevance/organization defect, not a false citation. | Organize around projection collapse, occurrence isolation and differences in hypotheses. Remove the standalone proof-net paragraph; move the detailed comparisons to their points of use. |
| §6, pp.9–11 | “Lean formalization” hides a complete second mathematical proof. | Rename to “A second proof and the Lean formalization”; keep the existing label. |
| §6, p.11, lines882–883 | “Witnessed zero” is unnecessary implementation terminology; independence was already established. | Replace that sentence by “On each nonempty hom-set, the empty union is its zero arrow.” |
| Appendix C, p.15, lines1171–1190 | The source/theorem dependency is not identified; the p.262 note stops at total rank at least two and leaves the crucial strict inequality unstated. Evidence: book’s cluster definition and both registered descent arguments. | Use the complete replacement below. This is clarification of an existing proof, not a new rank measure or changed reduction. |
| Appendix D.2, p.16, lines1282–1283 | “Raw terms” changes the established terminology without need. | Replace “raw terms” by “arrow terms”. Preserve Lean identifiers. |
| Appendix D.5, p.19, lines1495–1504 | “The zero law gives f union zero = f” compresses a derivation that also uses the other presentation equations. | Write “the zero law and the product, coproduct and dissociativity equations give …”. Retain the fact that these derivations do not use faithfulness. |
| Notation bibliography entry | The version is named, but its GitHub URL uses main. | Pin the existing v8 PDF URL to `42eaccdccf6413fe4d643a347fab33edafb1c056`. This is citation stability, not a mathematical error. |

All findings are minor and repairable. Failure-mode labels are `ambiguous` (omitted connection or unclear role), `missing_definition` (early B only), and potential `irreproducible` (mutable URL only). Evidence consists of the displayed text, the defined rank calculation and inspected primary sources. None warrants a claim that the maximality theorem is false.

Knuth–Larrabee–Roberts, *Mathematical Writing*, §1 points 9–14 and 24–26 support avoiding repeated words, connecting the argument, introducing notation, and removing unnecessary jargon. Sections 4–5 qualify definition placement; abstracts may preview familiar concepts. Wilf’s §27 discussion and van Leunen’s §36 abstract exercise were also consulted. The choice to group or relocate these citations is an editorial judgment, not a rule quoted from the book.

No printed use of “actual” or “structural” remains in v22. The latter occurs in unprinted labels. “Uniform”, “parallel”, “nonempty”, “positive”, “tagged” and the comparison maps’ universal-property qualifications do mathematical work and should remain. Appendix A and the author-requested Lean guide should remain.

### Replacement abstract

Only the earlier “also” is removed.

```latex
We prove that the zero-identity Boolean category of Do\v{s}en and
Petri\'c, freely generated by a nonempty set of propositional
variables, is maximal. Adjoining any equation between parallel arrows that does not follow
from the defining equations, and closing under the arrow operations
and uniform formula substitution, collapses this category to a preorder.
This disproves their conjecture that the category is not maximal.
The proof uses Boolean Coherence to select a pair of variable
occurrences on which the two arrows differ. Composition with arrows
selecting these occurrences, uniform substitution and two
isomorphisms yield equality of the product projections. We
prove that any zero-identity Boolean category satisfying such an
additional equation under every interpretation of the variables is
a preorder. We also give a Lean formalization of these proofs and
their dependencies. It includes Boolean Coherence and the
correspondence between substitution on tagged occurrence sets and
substitution on finite ordinals.
```

### Replacement introduction

Retain the existing section label. The detailed comparisons move as specified below; no new priority claim is introduced.

```latex
We prove that the freely generated zero-identity Boolean category of
Do\v{s}en and Petri\'c over a nonempty set of propositional variables
is maximal. Adding any equation between parallel arrows that does
not follow from its defining equations, and closing under the arrow
operations and uniform formula substitution, collapses the category
to a preorder. This disproves Do\v{s}en and Petri\'c's conjecture that the category
is not maximal \cite[\S14.2, p.~322]{DP}. Before adjoining the equation, the
two projections $p\wedge p\to p$ are distinct for every
propositional variable $p$.

The proof reduces an added equation to equality of the product
projections, as in the maximality theorem for cartesian categories
\cite[\S5]{DPCartesian}. Boolean Coherence supplies a pair of
variable occurrences belonging to one arrow's relation and not the
other. Precomposition and postcomposition isolate this pair and
give the equation of \cite[\S9.7, pp.~215--216]{DP}.
Uniform substitution then gives this equation for every formula.
The two isomorphisms listed in \cite[\S12.5, p.~294]{DP}
give equality of the product projections. Sections~\ref{sec:isolation}
and~\ref{sec:collapse} present this proof; Section~\ref{sec:formalization}
gives a second proof using mix. The proof of
\cite[Lemma~7]{DPIsomorphic} also supplies the two isomorphisms.

Other notions of Boolean category need not make conjunction and
disjunction categorical products and coproducts. Free categories constructed from classical proof nets
are studied in \cite[Theorem~3.5.4]{LSFree}, equations on monoid
and comonoid structures in $*$-autonomous categories in
\cite{Strassburger}, and inequalities interpreting cut reduction
in \cite{FP}. Section~\ref{sec:category} compares the negation
equation of \cite{FP} with the zero-identity equation used here.

We use the occurrence coordinates of \cite[\S9]{Notation}:
occurrences form tagged disjoint unions, and substitution replaces
each occurrence by a block. Section~\ref{sec:occurrences} defines
these coordinates; Appendix~\ref{app:substitution} proves their
correspondence with the finite-ordinal substitution formula of
Do\v{s}en and Petri\'c. Section~\ref{sec:formalization} and
Appendix~\ref{app:lean-statements} describe the Lean formalization,
including a guide to its declarations and proof steps.
Appendix~\ref{app:explicit-inverses} constructs the two inverses
used in the first maximality proof, and
Appendix~\ref{app:cut-errata} corrects two typographical errors
in the cut-elimination argument used in Do\v{s}en and Petri\'c's
proof of Boolean Coherence \cite{DP}.
References to \cite{DP} use the printed pagination of its
September 2007 revised version. Lean declaration names in footnotes
omit the namespace prefix \texttt{DosenPetric.}
```

### Relocated comparisons

Insert before Lemma 4.1, after the paragraph identifying the context equation:

```latex
For negation-free formulas $A,B$ such that $A\to B$ is a
tautology, \cite[Lemma~6]{DPIsomorphic} constructs an arrow whose
occurrence relation consists of the edge between any prescribed
occurrences of the same variable in $A$ and $B$. The following
lemma isolates an edge of either of two given arrows; normalization
allows the formulas to contain negation.

Selecting a pair on which relations differ also occurs in the
maximality proofs for presentations of split preorders, split
equivalence relations and binary relations \cite[\S16]{DPSplit}.

```

Move the following comparison after the zero-law discussion in §2:

```latex
F\"uhrmann and Pym interpret cut reduction by inequalities between
arrows. An inequality belongs to a net theory if and only if it
holds in every interpretation of that theory in their classical
categories \cite[Theorems~6.4--6.5]{FP}.
Their negation triangle makes the composite in
\eqref{eq:zero-identity}, with the corresponding monoidal unit
isomorphisms, equal to $1_A$ \cite[(11)]{FP}.
Here that composite is $0_A$.
```


After the proof in §3 that the exponential $p\Rightarrow p$ does not exist, insert:

```latex
The maximality theorem for cartesian closed categories
\cite[\S11]{DPCCC} uses a typed B\"ohm theorem.
The absence of $p\Rightarrow p$ prevents its application here.
```

After the proof of Corollary 5.3, retain the following comparison of hypotheses:

```latex
For zero-identity distributive lattice categories,
\cite[\S12.5, p.~292]{DP} proves maximality without the truth
constants and relative maximality when both constants are present.
For lattice and dicartesian categories without an assumption of
distribution, the maximality and relative-maximality results are
proved in \cite[\S\S8--10]{DPBicartesian}.
```

The introduction now keeps the conjecture, proof inputs, projection-collapse method and distinction between Boolean-category axiom systems. The more detailed comparisons accompany the relevant constructions and result. The unused proof-net paragraph is removed, while its bibliography entry may remain in the source database.

### Replacement Appendix C

```latex
\section{Corrections to the cut-elimination argument used in Boolean Coherence}
\label{app:cut-errata}

Do\v{s}en and Petri\'c's proof of Boolean Coherence
\cite[\S14.2]{DP} uses the cut-elimination theorem for distributive
lattice categories proved in \cite[\S11.2]{DP}.
Our maximality proof uses Boolean Coherence as
Theorem~\ref{thm:coherence}.
We correct two typographical errors in the rank comparisons of
that cut-elimination argument. The displayed cut reductions are unchanged.

Write $L,R$ for the left and right ranks of a cut and $r=L+R$
for its total rank. Each one-sided rank counts the nodes of the
corresponding cut-formula cluster, so $L,R\geq1$.
The induction orders $(d,r)$ lexicographically, where $d$ is the
degree of the cut formula \cite[pp.~249,253]{DP}.
In the following cases, the cut formula is unchanged.

\paragraph{Page 260, case $(w\,\gamma\,3)$.}
The inequality $r<r'$ following the displayed reduction should
read $r'<r$. The two recursive cuts retain the left premise $h$.
Their right cut-formula clusters lie properly inside the original
right cluster. If their ranks are $R_f,R_g$, then
$R_f<R$ and $R_g<R$. Thus both recursive cuts have smaller total
rank: $L+R_f<r$ and $L+R_g<r$.

\paragraph{Page 262, case $(w\,\vee\,1)$.}
The phrase ``whose rank is~1'' should read ``whose right rank
is~1'', as in the analogous case on p.~261.
After eliminating the first recursive cut, the selected disjunction
in the new right premise is introduced by $\vee L$, so its
cluster has one node. The left premise is still $h$.
The new cut therefore has total rank $L+1$, not~1.
The original right cluster passes through the contraction and has
$R>1$. Hence $2\leq L+1<L+R=r$, which justifies the second
application of the induction hypothesis.

```

The appendix now names the source argument and its role in maximality before giving page references. The inequalities explain why the corrected text supports the induction. The source’s cut-reduction equations remain unchanged.

## (D) Cross-section consistency and verification

### Mathematical claims

| Statement and source lines | Hypotheses and proof check | Result |
| --- | --- | --- |
| Theorem 2.1, 236–242; proof 723–728 | Nonempty variable set, substitution congruence, and a distinct parallel pair. Isolation yields $K_\ell$; substitution/double negation yields $K_A$ for every formula; Lemma 5.2 gives thinness. The quantifiers over arbitrary parallel arrows survive the argument. | No defect found. |
| Theorem 3.1 (Boolean Coherence), 319–323 | $G$ is the specified relational interpretation. This is an attributed external theorem. D.5 outlines an independent equational route through positive coherence and common atomic factorization. The two uses must remain distinguished in a review. | Main proof uses the stated theorem correctly; full cut-elimination proof not independently rechecked. |
| Lemma 4.1 (isolation), 518–579 | Distinct parallel arrows. Normalize both endpoints by isomorphisms, choose a differing relation edge and its signed literal, then build singleton-relation input/output maps. Empty-relation filler maps exist because their source contains $\bot$ or their target contains $\top$. Coherence identifies the two composites with the singleton and zero arrows. | Typed and valid; no illicit arbitrary zero arrow. |
| Proposition 4.2, 596–629 | A substitution congruence with a distinct pair. Positive literal: substitute $A$ for $p$. Negative literal: substitute $\neg A$ for $p$, obtaining $K_{\neg\neg A}$; pre/postcompose with the double-negation isomorphism and its product/coproduct maps. Zero absorption gives the zero on the transported right side. | Valid for formulas with zero occurrences as well. |
| Lemma 5.1, 636–669 | Every formula over the fixed nonempty $P$. For one variable, the cited isomorphism types and faithfulness identify the specified $q_p,e_p$; in the two-occurrence case symmetry corrects the permutation. Substitution preserves inverse equations. Appendix E also explicitly constructs inverse arrows. | No defect found. External isomorphism citations are a separate source-verification duty. |
| Lemma 5.2, 676–721 | Proof congruence satisfying every $K_A$. Quotient retains products/coproducts because the equations and operations descend. $q_A$ factors through $\top$, making $A\vee\top$ terminal in the quotient. Then $\pi_1\circ e_A=\pi_1^{A,A}$ is invertible. The diagonal is its inverse, so the two projections coincide; pairing equates any parallel arrows. | No defect found. Coherence is applied only in the original category. |
| Corollary 5.3, 738–760 | A distinct parallel pair agrees under **every** interpretation into the model. Agreement under all interpretations is a proof congruence and is substitution closed because $I_vF_\sigma$ is an interpretation. Maximality makes all projection interpretations equal. Assign a fixed $p\in P$ to arbitrary $X$; pairing proves thinness in the model. | No defect found. The universal quantifier over interpretations is essential and retained. |


The significant unnumbered arguments were also read: zero absorption, signed-label preservation, absence of an exponential p⇒p, negation and converse relations, substitution composition, retract transfer, the symmetric-mix proof, union laws, Appendix A’s coordinate maps and example, Appendix B’s typed diagrams, term/arrow congruence correspondence, Boolean soundness excluding an arrow from top to bottom, positive-coherence transfer, common atomic factorization and both explicit inverses. No invalid inference was found in those checks.

### Appendix C and the registered proof

The dependency is cut elimination, then positive/Boolean coherence, then occurrence isolation and maximality. The two corrections justify recursive calls in the first stage. The printed errors therefore matter to the stated induction, even though neither changes a reduction or theorem.

At registered commit `5dbee39bea09539bd130f729e82636419f71f920`:

- `GentzenBlockedLeftGammaDisjRank.lean`: `gamma_first_descent` and `gamma_second_descent` prove both strict child comparisons; `blockedL_gammaDisj_rank_step` passes them to the induction hypothesis.
- `GentzenAppendixCFreshRight.lean`: `fresh_principal_rank` proves right rank 1; `fresh_total_rank` proves total rank L+1; `fresh_total_rank_ge_two` proves its lower bound.
- `GentzenBlockedDisjFirstRank.lean`: `fresh_clean_and_rank` proves the new cut is clean and has smaller total rank, using the original contracted rank greater than one. `blockedL_disjunctionFirst_rank_step` applies the induction hypothesis to both cuts, each compared with the original cut.

These are source checks of the statements and induction calls. They are not a new build or a full audit of every transitive dependency.

### Citation audit

No substantive false citation or incorrect bibliographic year, author, title, volume or page range was found. The nonmaximality conjecture is explicitly present in the cited revised book. The negation-free hypothesis of the cited Lemma 6 is retained. The use of Lemma 7 first at a variable, followed by substitution, respects its scope. The primary-source loci checked are recorded below.

| Key and manuscript lines | Primary location inspected | Result |
| --- | --- | --- |
| DP: 61 | §14.2, p.322 | Conjecture attribution confirmed. |
| DP: 70, 516 | §9.7, pp.215–216 | Isolation equation and restricted collapse confirmed. |
| DP: 71, 634, 650 | §12.5, p.294 | Both isomorphism types confirmed. |
| DP: 90 | §12.5, p.292 | Maximality/relative-maximality distinction confirmed. |
| DP: 142, 203, 206, 280 | §§14.2–14.3, pp.316–322 | Category, zero identity and defining law confirmed. |
| DP: 180, 794 | §11.1, p.234 | First-injection and mix equations confirmed. |
| DP: 228 | §2.7, p.51 | Uniform substitution on terms and types confirmed. |
| DP: 299 | §2.9, p.60 | Relation interpretation confirmed. |
| DP: 325 | §14.2, p.321 | Boolean Coherence confirmed. |
| DP: 332 | §14.3, p.324 | Initial-object argument and double-negation collapse confirmed. |
| DP: 346, 351 | §14.1, pp.313–315; §14.2, pp.318–321 | Normalization and equivalence confirmed. |
| DP: 731 | §9.3, p.194 | Model formulation of maximality confirmed. |
| DP: 852, 874 | p.220; pp.290–291 | Union definition and zero law confirmed. |
| DP: 921, 1013, 1052 | §2.5, pp.45–46 | Ordinal formula confirmed. |
| DP: 130, 131, 1171, 1175 and Appendix C | pp.249, 258–262; edition title page | Edition and rank claims checked as detailed below. |
| DPIsomorphic: 72, 92, 664 | Lemmas 6–7, author pp.12–13 | Lemma 6 requires no negation; Lemma 7's proof realizes each variable-preserving occurrence bijection. Manuscript uses both correctly. |
| DPCartesian: 77 | §5, author pp.6–7 | Coherence, substitution and composition yield equal projections, then collapse. |
| DPCCC: 79 | §11, author pp.18–19 | Typed Böhm theorem yields equal projections in every target model; citation supported. |
| DPBicartesian: 87 | §§8–10 | Lattice maximality and dicartesian relative maximality supported. |
| DPSplit: 95 | §16, author pp.55–58 | Isolation of a differing relation pair is used in the maximality proofs for RB, EF and PF. |
| DPPN: 101 | Introduction; PN¬ and MPN¬ Coherence statements | Unit-free multiplicative fragment, with/without mix, and Brauerian split-equivalence target supported. |
| LSFree: 106 | Proceedings version, Theorem 3.5.4, author p.10 | Freeness is for graphical, Δ–∇-strong K-flat/K-sharp-autonomous categories. The manuscript's broad summary is accurate; it does not assert freeness for every possible Boolean-category axiom system. |
| Strassburger: 108 | Abstract, §5 and subsequent axioms | Monoid/comonoid axioms on a star-autonomous category supported. |
| FP: 112, 116 | Theorems 6.4–6.5, author pp.49,51; diagram (11), author p.8 | Quantification over interpretations and identity-valued negation triangle supported. Compare unit isomorphisms as the manuscript does; its conjunction is not the paper's categorical product. |
| Notation: 118, 379, 924 | Version-8 TeX §9, lines 1032–1345 | Tagged blocks, fibre map and ordinal coordinate transport supported; date 19 September 2026 confirmed. |
| Formalization: 770; Palomar: 910,1275 | Repository links and existing registration evidence | Parent agent handles declaration/link correspondence. This citation subaudit did not replay kernels or inspect every linked proof body. |


The Lean-manual citation names the appropriate chapters on types, propositions and tactics. The Formalization and Palomar references agree with the registered source and five selected statements. All 56 hyperlink occurrences were checked: they reach 49 named declarations at 29 source modules at the stated commit, with correct line targets. The manuscript distinguishes those five selections from the wider formalization.

The cited Notation v8 §9 was read at notes commit `42eaccdccf6413fe4d643a347fab33edafb1c056`; its tagged-coordinate account agrees with the paper. The source text was checked, not that note’s rendered PDF.

### Definition order and typing

Apart from the premature B in the introduction, the principal notation is introduced before mathematical use: category and formulas; products, coproducts and composition; contravariant negation; zero arrows on nonempty hom-sets; congruences; occurrences and labels; relational interpretation; literals and normal forms; substitution blocks and functors; the context equation; interpretations; pattern coordinates; term equality; and the positive-fragment convention. Types in the displayed diagrams and Appendix E’s composites were checked. Quotient arrows are distinguished from terms, and negation closure is deduced at the point where the dichotomy supplies it.

## (E) Conditions for the next manuscript version

1. Apply the explicit Appendix C dependency and strict-rank explanation. Without it, retain a finding of incomplete exposition; this audit supplies no mathematical ground for rejecting the theorem.
2. Remove the early undefined notation and include substitution in the introductory proof outline. No theorem changes are required.
3. Preserve the nonempty-variable hypothesis, uniform-substitution closure, universal quantifier over model interpretations, signed-literal distinction and restriction of zero arrows to nonempty hom-sets. Weakening these would require a new correctness review.
4. Preserve both maximality proofs, Appendix A, the author-approved disclosure, all 49 declaration destinations and the supplied Palomar v2 BibTeX. Reorganization must not delete the substantive distinctions between the compared theories.
5. Local Codex should apply the changes in the next unused version, compile and inspect it, update the package and active pointers, and provide the complete diff and before/after text. Reuse the registered proof verification; none of these prose changes calls for rebuilding the Lean proofs. Treat a later Palomar v3 submission as a separate task with its required exact-candidate checks.

This report is a review handoff, not a release candidate or a new submission. No repository commit, Windows Downloads delivery or registration was performed from this environment. The report and exact replacement text are provided directly to the author for the local Codex workflow.

## (F) Not checked / uncertainty log

The complete 1,767-line v22 source was read. The original 23-page PDF was extracted for page anchors; pages 1, 2 and 21 were inspected visually in this review. No new compilation was run, because the manuscript itself was not edited. The proposed replacement text has not been compiled as a new version.

The entire Lean development and its transitive imports were not independently reverified, and no kernels were rerun. The affected rank comparisons and their induction calls were checked directly. The citation audit revisited all external mathematical citation loci, but did not reprove every theorem in the cited literature or perform an exhaustive new priority search. Some live publisher pages were unavailable; downloaded primary texts and institutional publication records supplied the necessary evidence.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none identified. Most important unchecked item: full independent verification of the transitive proof dependencies underlying cut elimination. That limitation does not make the paper’s citation of Boolean Coherence a gap. Editorial conclusion: localized revision; no major reconstruction indicated. Final recommendation under the hostile-review rubric: **unknown** as a global certification, with no confirmed ground for mathematical rejection in the material checked.

Primary sources used include the September 2007 [Proof-Theoretical Coherence](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), the [institutional publication list](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/publications.htm), the cited author PDFs and publisher records, and [Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf). The substantive review is based on the source passages, not search snippets.
