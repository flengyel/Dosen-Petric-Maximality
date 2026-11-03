# (A) Kill-shots / hard blockers

**V23 requires local corrections, including an explicit substitution-closure hypothesis in Appendix D.4. No fatal error or major proof gap was established.**

This joint hostile-referee and mathematical-writing review concerns *Maximality of the Došen–Petrić Boolean Category*, v23, dated 2 November 2026: 1,781 LaTeX source lines and 23 PDF pages. It is an author-side AI-assisted audit under HostileRefereeGPT — Cat/Rec and the mathematical-writing plugin. The complete source, both bibliography files, and rendered pages were examined. No manuscript or Lean source was changed.

The [repository v23 source](https://github.com/flengyel/Dosen-Petric-Maximality/blob/main/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.tex) was fetched again and matches the reviewed local file. Its Git blob is e7da5595065e36955d40bfa5109fbe1c01ba70bd; its SHA-256 is b34afdb82b1f36731ef9c1d8cb6a369b07fc40a71e3189cf3c093677f3b303c2. Source line numbers below refer to those bytes. PDF page numbers are printed page numbers.

The correction newly identified in this pass is a conditional-scope ambiguity in D.4. The earlier six local clarification requests remain justified. Two earlier suggestions remain optional. The prose also retains generic “arrow” where the author's preferred word is “morphism”; the specific expression “arrow term,” exact Lean names, and diagram commands require separate treatment.

# (B) Major weaknesses

**None established.** The existing organization preserves the dependencies of both proofs.

**Current outline and mathematical function**

| Part | Function |
| --- | --- |
| Abstract | States maximality, the disproved conjecture, proof method, model consequence, and formalization. |
| §1 Introduction | Positions the result, identifies antecedents and different categorical frameworks, and gives the roadmap. |
| §2 The Boolean proof category | Defines the relevant operations, equations, congruences, and Theorem 2.1. |
| §3 Occurrences and substitution | Defines occurrence coordinates, labels and signs, states coherence, and develops normalization and substitution. |
| §4 Isolating an occurrence | Proves isolation, transport along retracts, and passage from the literal equation to every \(K_A\). |
| §5 Equality of the product projections | Proves the two isomorphism facts, collapse, maximality, and the model corollary. |
| §6 A second proof and the Lean formalization | Gives the mix proof, union laws, and their correspondence with the formalization. |
| A.1 Occurrence maps and their fibres | Defines substitution coordinates and the label map through commuting squares. |
| A.2 The finite-ordinal presentation | Derives the ordinal formula and computes the eight-position example. |
| A.3 Shared variables and the maximality argument | Proves renaming compatibility and connects the coordinates to substitution in \(K_A\). |
| B Diagrams for three defining equations | Displays the first-injection, zero-identity, and zero-law equations with their types. |
| C Cut-elimination corrections | Identifies two published rank misstatements and proves the corrected inequalities. |
| D.1 Arrow terms and equations | Defines typed terms, derivability, quotient morphisms, and primitive congruences. |
| D.2 Reading a Lean declaration | Explains the declaration syntax and the short proof's mathematical steps. |
| D.3 The five declarations | States and explains the registered entry points. |
| D.4 Congruences on terms and on arrows | Relates congruences on terms and quotient morphisms and identifies further formalized results. |
| D.5 The proof of coherence | Explains positive coherence, split comparisons, common factorization, and transfer to \(\mathsf B(P)\). |
| E.1–E.2 Inverses of \(q_A,e_A\) | Constructs the inverse morphisms and verifies their equations. |
| E.3 Split comparisons | Constructs the section and retraction used in D.5. |
| Disclosure and references | Gives the expressly authorized disclosure and source bibliography. |

No reorganization is recommended.

**Claims checked**

| Result or construction | Check and outcome |
| --- | --- |
| Zero morphisms, §2, lines 179–185 | The zero law makes \(f0_A\) independent of the witness \(f\). Both composition-absorption identities follow at the stated types. No zero is supplied to an empty hom-set. |
| Theorem 3.1 and occurrence calculations | The stated coherence theorem supplies faithfulness in the original category. Signed-label preservation and the block formula for substitution agree with the inspected source declarations. |
| Failure of cartesian closure, §3 | Faithfulness makes \(\mathsf B(\top,E)\) at most singleton, whereas \(1_p\ne0_p\). An exponential for \(p,p\) would contradict this through the exponential adjunction and \(\top\wedge p\cong p\). |
| Lemma 4.1 | The source and target selectors have singleton occurrence relations. Relational composition isolates the selected differing pair. The normalization morphisms have the required directions. |
| Proposition 4.2 | Substitution gives \(K_A\) directly for a positive literal. For a negative literal, substituting \(\neg A\) and transporting through \(\neg\neg A\cong A\) gives the required equation. |
| Lemma 5.1 | At a variable, the proposed maps have the relations of the cited isomorphisms, allowing product symmetry for the two-occurrence case. Substitution preserves their inverse equations. Appendix E also constructs inverses directly. |
| Lemma 5.2 and Theorem 2.1 | \(K_A\) makes \(q_A\) factor through \(\top\); invertibility makes \(A\vee\top\) terminal in the quotient. Invertibility of \(e_A\) then makes the first projection invertible. Its diagonal right inverse identifies the two projections; pairing collapses arbitrary parallel morphisms. |
| Corollary 5.3 | Agreement under all interpretations is substitution closed. Equal interpreted projections imply equality of arbitrary morphisms in the target category. No fullness or surjectivity assumption on interpretation functors is needed. |
| Second proof, §6 | The mix computations give terminality of \(A\vee\top\), then \(h_A\equiv\pi_1\). Symmetry gives equal projections. The displayed compositions are well typed. |
| Appendix A | Conjugating the tagged-coordinate function by the enumerating bijections gives the stated ordinal formula. Empty blocks and repeated labels are handled correctly; the example computes correctly. |
| Appendix C | The two printed errors and their corrections are supported by the book passages and inspected rank declarations. In the second case, right rank is \(1\), while total rank is \(L+1\), with \(2\le L+1<L+R\). |
| D.5 and E.3 | The union laws used to establish coherence have equational derivations before faithfulness. The comparisons provide one-sided inverses, sufficient for the normal-form reductions. No distributivity isomorphism is assumed. |
| Appendix E | The inverse constructions have the required occurrence graphs. The zero used in the inverse of \(e_A\) has an explicit witness. Empty occurrence sets cause no failure. |

These findings support the arguments examined. They do not certify every transitive Lean dependency.

# (C) Minor issues

The writing review uses Knuth, Larrabee, and Roberts, *Mathematical Writing*, §1 and §§4–5, consulted in the available copy. The relevant principles are connected explanation and definition near use (§1, points 10–11), reader expectations (12), unambiguous sentences (17), and avoiding unnecessary jargon (26). Sections 4–5 qualify definition placement; they do not require formal definitions for every introductory preview. The author's terminology preferences and the optional deletion below are independent editorial requirements, not rules attributed to KLR.

**Comparison table**

| ID and manuscript anchor | Difficulty and evidence | Severity and recommended action |
| --- | --- | --- |
| C1: D.4, p.18, lines 1454–1463 | “For nonempty \(P\), the dichotomy therefore makes \(\overline R\) either equality or the total relation.” The preceding paragraph introduces closure conditionally; this sentence repeats only nonemptiness. Failure mode: ambiguous. Evidence: counterexample to the unconditional reading, below. | Minor hypothesis-scope clarification. State explicitly that R.Closed holds. |
| C2: D.5, p.19, lines 1581–1586 | “Gentzenization, cut elimination and atomization express the given arrow ...” leaves atomization unexplained. Evidence: absence_in_text and the registered atomization construction. | Minor explanation. Describe the reduction of compound weakening and retain the original morphism as the subject of the normal-form equality. |
| C3: D.5, p.20, lines 1606–1614 | “atomic factorization constructs ...” uses an unexplained adjective. The complete typed factorization data follow, so no missing mathematical data are established. Failure mode: ambiguous; evidence: absence_in_text. | Minor terminology correction. State the existence of those data directly and repair “It also gives.” |
| C4: §1, p.1, lines 68–71 | “the equation of” an external reference does not identify the equation labelled in §4. Evidence: absence_in_text. | Minor navigation clarification. Refer to the literal instance of \(K_A\), retaining the source citation. |
| C5: §1, p.1, lines 72–76 | “The two isomorphisms listed” does not locally identify the chosen morphisms. Evidence: absence_in_text. | Minor navigation clarification. Refer to Lemma 5.1 and retain both primary-source citations. |
| C6: §6, p.11, footnote 7, lines 887–889 | The maps “identify these expressions with arrows of \(\mathsf B(P)\),” although the body has already stated its expressions there. The other hom-sets are unnamed. Failure mode: ambiguous; evidence: the registered map types. | Minor correspondence correction. Identify the hom-set between the normalized endpoints in the normal-form presentation. |
| C7: D.5, p.20, lines 1625–1626 | “recovery maps of Section 3” does not match the construction named there. Failure mode: ambiguous; evidence: absence_in_text. | Minor internal-reference correction. Refer to the occurrence-preserving equivalence stated in §3. |
| C8: throughout, beginning abstract lines 28–34 | Generic “arrow” persists where the author requested “morphism.” | Editorial terminology correction, not a mathematical error. Replace contextually; preserve the explicitly retained technical expression “arrow term.” |
| O1: D.2, p.17, lines 1373–1374 | The parameter recap repeats the roles identified in the preceding sentences. | Optional economy: delete the recap. |
| O2: D.4, p.18, lines 1454–1456 | “the substitution square” can be made more precise, since §3 also contains a substitution square. | Optional navigation: specify Appendix D.1. |

All entries are locally repairable. C4 and C5 concern navigation, not false citations or invalid inferences.

**Why the closure qualification in C1 matters**

Let \(P=\{p,q\}\), and define a substitution \(\sigma:P\to\operatorname{Form}(P)\) by \(\sigma(p)=\top\) and \(\sigma(q)=q\). For terms \(t,u\in\mathcal T_P(A,B)\), put
\[
t\,R_{A,B}\,u
\quad\Longleftrightarrow\quad
[t[\sigma]]=[u[\sigma]]
\quad\text{in }\mathsf B(P)(A[\sigma],B[\sigma]).
\]
Because substitution preserves the defining equations, composition, conjunction and disjunction, \(R\) is a primitive congruence. It contains the derivability relation \(\mathcal E\).

Coherence gives \(1_\top=0_\top\), so \(\operatorname{id}_p\,R\,z_p\), although \(\operatorname{id}_p\) and \(z_p\) are not \(\mathcal E\)-related. However, \(\operatorname{id}_q\) and \(z_q\) remain unrelated, because their substituted morphisms are \(1_q\ne0_q\). Thus \(R\ne\mathcal E\) and \(R\) is not total.

The substitution \(\tau(p)=q,\ \tau(q)=q\) carries the first related pair to the second, unrelated pair. Consequently R.Closed fails. This demonstrates that closure is necessary for the dichotomy; it does not refute the correctly qualified theorem. The intended conditional reading of D.4 is recoverable from the preceding paragraph, which is why the finding is minor.

**Definition order and notation**

| Data | First explanation or definition | Assessment |
| --- | --- | --- |
| \(\operatorname{Form}(P),\mathsf B(P)\), basic operations | §2, lines 105–156 | Typed before use in the proof. Composition order and negation's opposite-category domain are explicit. |
| \(0_A\), zeros in inhabited hom-sets | §2, lines 157–185 | Defined with the necessary existence qualification. |
| Proof and substitution congruences | §2, lines 196–204 | Defined before the main theorem. |
| Maximality | Abstract/introduction preview; precise explanation at lines 220–224 | Adequately introduced. |
| Occurrences, labels, signs, \(\mathbf{Rel}_{\mathrm{fin}}\), \(G\) | §3, lines 229–293 | Introduced before the isolation proof. |
| Literals, normal forms, normalization isomorphisms | §3, lines 319–326 | Defined before the construction using them. |
| \(F_\sigma,\chi_{A,\sigma},R_{f,\sigma}\) | §3, lines 360–438 | Types and actions are stated; endpoint identifications for iterated substitution are explicit. |
| \(j_A,K_A,q_A,e_A\) | §4, lines 486–496; §5, lines 627–637 | Defined before deduction; only introductory pointers need clarification. |
| Interpretations \(I_v\) | §5, lines 721–727 | Defined before the model corollary. |
| Mix, \(h_A\), and union | §6, lines 782–878 | Defined before their calculations. |
| Formula patterns, occurrence maps, skeleton | A.1–A.2 | Defined adjacent to the constructions that use them. |
| \(\mathcal T_P,\mathcal E,R\), Closed and Total | D.1, lines 1215–1283 | Typed before the registered statements; the local scope issue is C1. |
| \(\mathcal R(P)\), positivity | D.5, lines 1499–1506 | Defined before the coherence argument. |
| Atomization, “atomic factorization,” recovery reference | D.5 | The explanatory/reference issues C2, C3 and C7 remain. |

No further undefined central symbol was established. No empty reader-facing use of “actual,” “structural,” “raw,” “obvious,” “clearly,” “essentially,” or “genuine” was found. Internal reference keys and exact Lean identifiers are not prose defects.

# (D) Cross-section consistency failures

The confirmed local inconsistencies are C1's conditional scope, C6's unnamed hom-sets, and C7's mismatched internal reference. No contradiction between the main theorems and their proofs was established.

The abstract retains the “every interpretation” condition of Corollary 5.3. Coherence is used in the original category, not presumed in a quotient after adding an equation. The distinction between terms and their quotient morphisms is explained. The category on an empty variable set is explicitly allowed where needed. The one-sided comparison identities in D.5 agree with E.3.

The faithfulness-transfer replacement in C7 is mathematically valid. An occurrence-preserving equivalence transports equality of occurrence relations to the reduced presentation; reduced faithfulness gives equality there, and faithfulness of the equivalence gives equality in \(\mathsf B(P)\). No circularity is established by this argument. The registered implementation uses representatives and normalization before constructing later quotient-level reduction maps.

**Exact replacement passages, in priority order**

**C1 — Appendix D.4, lines 1460–1461.** Replace the sentence beginning “For nonempty \(P\)” by:

~~~latex
If $P$ is nonempty and \texttt{R.Closed} holds, the dichotomy
therefore makes $\overline R$ either equality or the total relation.
~~~

Retain the following sentences about preservation by all operations and substitution congruences.

**C2 — Appendix D.5, lines 1581–1583.** Replace the opening through “inhabited hom-set” by:

~~~latex
Represent the given morphism by a Gentzen derivation and eliminate
its cuts. Replace weakening on compound formulas by weakening on
literals and constants. The normal-form theorem then expresses
the original morphism as a finite union of these paths; an empty
union uses the zero in its inhabited hom-set.
~~~

Retain the subsequent relational argument and declaration links. “Original morphism” is deliberate. In the registered Gentzen representation, the singleton sequent's denotation has type \(U\wedge\top\to V\vee\bot\); the decoded morphism has type \(U\to V\). The original v23 sentence is not ill typed. The earlier review's proposed replacement introduced that ambiguity by using “denotation” without specifying unit transport.

**C3 — Appendix D.5, lines 1606–1609 and 1613.** Use:

~~~latex
For arbitrary terms $f,g:A\to B$ of $\mathcal R(P)$, there are
formulas $A',B'$, morphisms $u:A\to A'$, $v:B'\to B$ and positive
terms $f_0,g_0:A'\to B'$ such that, on quotient morphisms,
~~~

Keep the factorization display. Replace “It also gives injections” by “There are also injections.” Keep the direct-image equalities and both linked Lean names.

**C6 — Section 6, footnote 7.** Replace its concluding explanation while preserving the existing declaration links:

~~~latex
These Lean laws concern the presentation on negation normal forms
described in Section~\ref{sec:occurrences}. The mutually inverse maps
\href{https://github.com/flengyel/Dosen-Petric-Maximality/blob/5dbee39bea09539bd130f729e82636419f71f920/DosenPetric/ReducedQuotientReduction.lean\#L21}{\texttt{Reduced.\allowbreak{}reduceHom}}
and
\href{https://github.com/flengyel/Dosen-Petric-Maximality/blob/5dbee39bea09539bd130f729e82636419f71f920/DosenPetric/ReducedRecovery.lean\#L26}{\texttt{Reduced.\allowbreak{}recoverHom}}
identify its hom-set from $A^\circ$ to $C^\circ$ with
$\B(P)(A,C)$, transferring these laws to $\B(P)$.
~~~

This does not introduce the notation \(\mathcal R(P)\) before its definition in D.5.

**C7 — Appendix D.5, lines 1625–1626.**

~~~latex
The equivalence described in Section~\ref{sec:occurrences}
preserves the occurrence interpretation and therefore transfers
faithfulness from $\mathcal R(P)$ to $\B(P)$.
~~~

Retain the existing footnote.

**C4–C5 — Introduction, lines 68–76.**

~~~latex
Precomposition and postcomposition isolate this pair and give a
literal instance of equation~\eqref{eq:context} in
Section~\ref{sec:isolation} \cite[\S9.7, pp.~215--216]{DP}.
Uniform substitution and the double-negation isomorphism then give
this equation for every formula.
The isomorphisms of Lemma~\ref{lem:structural-isos}, whose types are
listed in \cite[\S12.5, p.~294]{DP}, give equality of the product
projections. Sections~\ref{sec:isolation} and~\ref{sec:collapse}
present this proof; Section~\ref{sec:formalization} gives a second
proof using mix. The proof of \cite[Lemma~7]{DPIsomorphic} also
supplies the two isomorphisms.
~~~

“Literal instance” preserves the order: isolation gives \(K_\ell\), then substitution gives every \(K_A\).

**C8 — Contextual terminology correction.** Use “parallel morphisms,” “zero morphisms,” “positive morphisms,” “operations on morphisms,” and “quotient morphisms” for the corresponding categorical objects. For example, replace “five-arrow composite” by “composite of five morphisms,” and title D.4 “Congruences on terms and on morphisms.”

Retain the technical expression “arrow term,” as specifically requested for v23, together with exact Lean declaration names, quotations, bibliography titles, and TikZ commands. Do not replace terms by their equivalence classes or vice versa. The source has 117 arrow/Arrow/arrows word tokens excluding diagram commands; 15 occur in “arrow term(s).” Those counts are an inventory, not a count of 117 defects.

**Optional O1–O2.** Delete the parameter recap at lines 1373–1374. At lines 1454–1456, use:

~~~latex
If \texttt{R.Closed} holds, the substitution square in
Appendix~D.1, with $Q=P$, shows that they are preserved by
$F_\sigma$ for every $\sigma:P\to\FormulaSet(P)$.
~~~

The exact square reference can instead use a new label when implementing a numbered revision.

# (E) Acceptance conditions, non-negotiable

No condition for rejecting the main mathematical result was established.

1. **D.4 must keep substitution closure explicit in the dichotomy inference.** The verifiable endpoint is the corrected conditional sentence in C1. An unconditional dichotomy is false by the exhibited example.
2. **The coherence guide must identify the constructions and hom-sets it invokes.** Implement C2, C3, C6 and C7 without changing the factorization data or normal-form equality. A literal Gentzen-denotation equality at endpoints \(U\to V\) must not replace the decoded equality.
3. **Preserve the mathematical qualifications.** In particular, retain universal quantification over interpretations, witnessed zeros, the split identities, and the algebraic derivation of union laws before faithfulness. Their removal would change the argument.

The introductory cross-references, terminology consistency, and optional economy edits do not provide mathematical rejection grounds. Any released manuscript revision must use v24 or later and preserve v23, in accordance with the repository's versioning instructions.

# (F) Not checked / uncertainty log

The entire manuscript source and both bibliography files were read. Three separate checking passes covered the main mathematics, appendices/formal correspondence, and prose. KLR §1 and §§4–5 were consulted directly. The current repository v23 source was compared with the local source. All 83 internal references resolve to the 34 labels.

All 23 existing PDF pages were visually inspected in page sheets, and PDF text was used to confirm finding locations. No clipping or overlapping content was observed in that inspection. The existing build log has one underfull-box diagnostic and no reported overfull box; no new manuscript build was run.

Relevant registered declarations and the cited book passages were inspected as specified in the checks above. This pass did not rerun Lean, kernel replay, Comparator, registration, or service verification. It did not reconstruct every cut-elimination branch or every transitive formal dependency, renew every bibliographic comparison, or perform an exhaustive novelty search.

The report contains proposed replacement passages. It does not release v24, alter the registered source, commit, push, or submit a manuscript. A workspace copy is retained at revision-v23/docs/reviews/V23_JOINT_HOSTILE_WRITING_REVIEW_2026-11-03.md. The WSL Downloads destination is not available in this environment; no copy there is claimed.

**Strongest confirmed blocker:** none. The most consequential local correction is the explicit R.Closed hypothesis in D.4.

**Strongest suspected but unconfirmed blocker:** none supported by the evidence.

**Most important unchecked item:** complete independent reconstruction of the cut-elimination dependency.

**Dependence on unavailable material:** none for the stated findings; unperformed checks remain outside the conclusion.

**Final formal referee recommendation: unknown.** The audit supports the specified local corrections and supplies no demonstrated mathematical basis for rejection.

