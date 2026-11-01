# From the formalization to the manuscript

1 November 2026. Input: manuscript v15 and repository commit
f869fe74e9cc713ad366b51fad16d5de357fe74a. The registered version-2 proof
source is 5dbee39bea09539bd130f729e82636419f71f920.

The formalization contains mathematical content that the paper does not print.
The most useful additions are the formula for the complete occurrence relation
after substitution, the explicit inverses of q_A and e_A, and the union
operation on parallel arrows. These are additions to the exposition, rather
than missing Lean proofs or established errors in the main theorem. The
existing isomorphism lemma has a cited proof; printing its formal witnesses
would give a different, more explicit proof.

This report checks the direction Lean → paper. The existing complete claim map
principally checks paper → Lean. A complete map in the latter direction does
not assert that the paper presents every mathematical result in the library.
V15 and its upload package are unchanged by this audit. The proposed wording
below is review material; it has not been released as manuscript v16.

## Scope and method

The source inventory covers all 850 production modules, including the root
facade: 77,946 physical lines and 7,548 explicit declaration openings. This is
a lexical source count, not the kernel's count including generated declarations.
The 1,870 tracked Lean files also include checks, scripts and retained control
fixtures. They are not 1,870 production mathematical modules.

The five selected entry points import 755 production modules transitively.
Ninety-five other production modules include model semantics, the substitution
action laws, occurrence coordinates, examples and other support. They were
included in the inventory; the audit was not confined to Solution's imports.
All 131 modules outside the Gentzen family had their explicit declaration-name
inventories examined. Detailed source reading followed the principal
mathematical interfaces and the candidates reported below. The 719 Gentzen
modules were assigned to their proof roles through the inventory/import graph;
the normalization, coherence, split-comparison, common-factorization and
counterexample interfaces were read in detail. This is not a claim to have
independently rechecked all 77,946 source lines or every kernel proof term.

Every finding was compared with the complete v15 TeX, including Appendix D,
and the existing statement/correspondence records. The retained PDF supplies
page anchors. No Lean build, kernel replay, Comparator, Palomar verification
or registration was repeated. Source and release preservation are checked
against the input and frozen commits in the accompanying provenance.

## Findings and recommended placement

| Item | Content in Lean | Status in v15 | Recommended treatment |
| --- | --- | --- | --- |
| R1 | Complete occurrence relation after substitution | Endpoint blocks are described; the relation formula is absent | Add after F_sigma in Section 3, with the typed square |
| R2 | Explicit inverses of q_A and e_A | Their existence is proved through cited isomorphisms; the concrete terms are absent | Give the witnesses in Lemma 5.1 or a mathematical appendix |
| R3 | Union of parallel arrows and its algebraic laws | Mix appears, but the induced union operation does not | Add a short structural remark if this helps explain the formal coherence proof |
| R4 | Identity, composition and extensionality laws for substitution | Each F_sigma is a functor; the laws between substitutions are not stated | Add beside R1, avoiding a separate section |
| R5 | The equation K_A passes to retracts | Only its double-negation instance is printed | State the general lemma immediately before the negative case, if useful |
| R6 | Occurrence signs are preserved for arbitrary formulas; negation takes converse relations | Literal preservation is stated for negation normal forms only | Add one short statement in Section 3 |
| R7 | Split distributive comparisons, DNF/CNF retracts and the positive-coherence argument | Section 6 states that coherence is proved, without this proof outline | Add a concise mathematical account to Appendix D if the Lean proof itself is to be explained |

The first two items most directly improve the mathematical argument's
self-contained exposition. R4 fits naturally with R1. R3 and R7 explain
substantial structure used by the formal coherence proof. R5 and R6 can be
short remarks; the present proof does not require their full generality.

## R1. The relation after substitution

Manuscript anchor: Section 3, PDF p.5, the paragraph beginning “Substitution
on arrow terms induces a functor,” source lines 378–396; Appendix A describes
the labels of the substituted objects. Neither passage states the complete
relation of a substituted arrow.

Lean anchors: Presentation.occurrence_substitute_coordinates and
occurrence_substitute_expanded in
[PresentationSubstitutionRelation.lean](../DosenPetric/PresentationSubstitutionRelation.lean);
Relations.Fiber.lift and lift_composition in
[SubstitutionFiberRelations.lean](../DosenPetric/SubstitutionFiberRelations.lean).
The term theorem checks every primitive constructor, not only the endpoints.

For sigma:P→Form(Q), retain D_(A,sigma), E_sigma and the occurrence bijection
b_A:Occ(A[sigma])→D_(A,sigma) of Section 3. For an arrow f:A→B, define a
relation R_(f,sigma):D_(A,sigma)→D_(B,sigma) by

\[
 ((x,t),(y,u))\in R_{f,\sigma}
 \quad\Longleftrightarrow\quad
 (x,y)\in Gf\ \text{ and }
 (\lambda_A(x),t)=(\lambda_B(y),u)\text{ in }E_\sigma.
\]

This equality is typed in the common disjoint union E_sigma. It compares the
inner positions only after identifying their variable labels. The theorem is

\[
 (x',y')\in G(f[\sigma])
 \quad\Longleftrightarrow\quad
 (b_A(x'),b_B(y'))\in R_{f,\sigma}.
\]

Regard b_A,b_B as graphs of bijections. Then the typed square is

```latex
\begin{tikzcd}[column sep=large,row sep=large]
 \Occ(A[\sigma])\arrow[r,"G(f[\sigma])"]\arrow[d,"b_A"']
   &\Occ(B[\sigma])\arrow[d,"b_B"]\\
 D_{A,\sigma}\arrow[r,"R_{f,\sigma}"']&D_{B,\sigma}.
\end{tikzcd}
```

The square is in the category of finite sets and relations. It says that each
old edge is replaced by the identity relation inside the inserted block.
Different old occurrences retain their different first coordinates even when
they have the same label. An empty inserted block contributes no edges.

Proof: induction on the arrow term. Identities and structural maps give the
corresponding graphs on blocks; zero, eta and epsilon give empty relations.
The two binary operations preserve the two tags. In composition an old
intermediate occurrence supplies an intermediate block with the same inner
position; preservation of variable labels makes it well typed. Equational
soundness then passes the statement to quotient arrows. This is stronger
than the assertion that the source and target occurrence sets have blocks.

## R2. The concrete inverses in the short proof

Manuscript anchor: Lemma 5.1, PDF pp.6–7, and Section 6, p.9, “with explicit
inverses for q_A and e_A.” The paper does not display those inverses. The
existing argument through the cited isomorphisms remains valid.

Lean anchors: ShortProof.qInverseTerm/q_qInverse/qInverse_q in
[PresentationShortQ.lean](../DosenPetric/PresentationShortQ.lean), and
sourceConjTerm/sectionTerm/eInverseTerm/e_eInverse/eInverse_e in
[PresentationShortE.lean](../DosenPetric/PresentationShortE.lean).
All these names have prefix DosenPetric.Presentation.

Here is their mathematical content, with composition in the paper's order.
Set S_A=(A∧bottom)∨top. Define

\[
 \bar q_A=
 [d_{A,\bot,\top}\circ(1_A\wedge\iota_2^{\bot,\top})\circ
      \langle1_A,!_A\rangle,\ \iota_2^{A\wedge\bot,\top}]:
      A\vee\top\longrightarrow S_A.
\]

To describe the other inverse without a name hiding an unspecified map,
let alpha_(X,Y,Z):(X∧Y)∧Z→X∧(Y∧Z) be product associativity and let
beta_(U,V):U∨V→V∨U be coproduct symmetry. Define the following composite:

\[
\begin{aligned}
 c_{X,Y;U,V}: (X\wedge Y)\wedge(U\vee V)
 &\xrightarrow{1_{X\wedge Y}\wedge\beta_{U,V}}
       (X\wedge Y)\wedge(V\vee U)\\
 &\xrightarrow{\alpha_{X,Y,V\vee U}}
       X\wedge(Y\wedge(V\vee U))\\
 &\xrightarrow{1_X\wedge d_{Y,V,U}}
       X\wedge((Y\wedge V)\vee U)\\
 &\xrightarrow{1_X\wedge\beta_{Y\wedge V,U}}
       X\wedge(U\vee(Y\wedge V))\\
 &\xrightarrow{d_{X,U,Y\wedge V}}
       (X\wedge U)\vee(Y\wedge V).
\end{aligned}
\]

Put

\[
 s_{X,U,V}=c_{X,X;U,V}\circ
       (\Delta_X\wedge1_{U\vee V}):
       X\wedge(U\vee V)\longrightarrow
       (X\wedge U)\vee(X\wedge V).
\]

With T_A=A∧top, define

\[
 \bar e_A=[1_{A\wedge A},0_{T_A,A\wedge A}]\circ s_{A,A,\top}:
        A\wedge(A\vee\top)\longrightarrow A\wedge A.
\]

The zero in this formula exists: Delta_A composed with the first projection
is an arrow T_A→A∧A. Thus no uninhabited hom-set is supplied with a zero.
The occurrence relations of bar q_A and bar e_A are the inverse bijections
of Gq_A and Ge_A. Faithfulness gives all four inverse equations:

\[
 \bar q_A\circ q_A=1_{S_A},\quad q_A\circ\bar q_A=1_{A\vee\top},\qquad
 \bar e_A\circ e_A=1_{A\wedge A},\quad e_A\circ\bar e_A=1_{A\wedge(A\vee\top)}.
\]

These formulas work directly for every formula A; they do not
require choosing a variable and then substituting for it. This explicit proof
uses Boolean Coherence but does not need the separate cited classification
of isomorphic objects. That distinction is about the proof used, not a flaw
in the paper's existing cited proof.

## R3. Union on parallel arrows

Manuscript anchor: Section 6, PDF p.8, defines mix and h_A but never defines
the induced binary operation on a hom-set.

Lean anchors:
[ReducedUnion.lean](../DosenPetric/ReducedUnion.lean),
[ReducedUnionOccurrences.lean](../DosenPetric/ReducedUnionOccurrences.lean) and
[ReducedFiniteUnion.lean](../DosenPetric/ReducedFiniteUnion.lean).
These results are named in the reduced presentation. Their passage to B(P)
uses reduceHom/recoverHom and their inverse and composition equations in
[ReducedRecovery.lean](../DosenPetric/ReducedRecovery.lean).
The code does not contain a separately named Presentation.union theorem;
the following transfer is a mathematical deduction from those proved maps.

For parallel f,g:A→B define, directly in B(P),

\[
 f\mathbin\cup g=[1_B,1_B]\circ m_{B,B}\circ
                   (f\wedge g)\circ\Delta_A.
\]

The same term in the reduced category is Reduced.union. Reduction preserves
its constituent operations, and recovery is inverse to reduction on every
hom-set. Consequently its proved laws pass to this operation. For parallel
f,g,h:A→B,

\[
 (f\cup g)\cup h=f\cup(g\cup h),\qquad
 f\cup g=g\cup f,\qquad f\cup f=f,
 \qquad G(f\cup g)=Gf\cup Gg.
\]

For k:X→A and l:B→Y, composition satisfies
\[
 (f\cup g)\circ k=(f\circ k)\cup(g\circ k),\qquad
 l\circ(f\cup g)=(l\circ f)\cup(l\circ g).
\]
In an inhabited hom-set,
f union 0_(A,B)=f. Define f≤g by f union g=g. This is equivalent to
Gf⊆Gg, by faithfulness and the union equation.
Thus every inhabited hom-set is a join semilattice with
least element its witnessed zero; a finite union, including the empty one,
is independent of the chosen witness, order and repeated summands. This is
not a claim that all hom-sets are inhabited or that B(P) has zero morphisms
between every pair of objects.

This operation and its laws have antecedents in Došen–Petrić's book, printed
pp.220 and 290–291; the omission is not evidence of a new result. The
[September 2007 source](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf)
was checked at those passages. If included, cite the antecedent and explain
its use in the finite-union proof of coherence.

## R4. The laws relating different substitutions

Manuscript anchor: Section 3, PDF p.5, and Appendix D.1, p.13. Both define
F_sigma but neither states the substitution identity/composition laws.

Lean anchors: Formula.subst_identity/subst_composition/subst_ext in
[FormulaSubstitutionLaws.lean](../DosenPetric/FormulaSubstitutionLaws.lean),
and Presentation.substitute_identity/substitute_composition/substitute_ext in
[PresentationSubstitutionActionQuotient.lean](../DosenPetric/PresentationSubstitutionActionQuotient.lean).

Let sigma:P→Form(Q), tau:Q→Form(R), and define
(tau star sigma)(p)=sigma(p)[tau]. For formulas A,B over P and an arrow
f:A→B of B(P),

\[
 A[p\mapsto p]=A,\qquad (A[\sigma])[\tau]=A[\tau\star\sigma],
\]
\[
 f[p\mapsto p]=f,\qquad (f[\sigma])[\tau]=f[\tau\star\sigma].
\]

In the arrow equations the endpoints are identified by the displayed formula
equalities. Pointwise equal substitutions give the same substituted formula
and arrow, with the same endpoint identifications. Formula induction proves
the first equations; term induction and quotient descent prove the arrow
equations. The formalization explicitly records the endpoint transports.
This is different from functoriality in f and composition of arrows.

## R5. K passes to retracts

Manuscript anchor: Proposition 4.2, PDF p.6, uses the double-negation
isomorphism for its negative case. The following more general lemma is
proved as ContextualCollapse.context_retract in
[Substitution.lean](../DosenPetric/Substitution.lean).

For a proof congruence, suppose i:A→B and r:B→A satisfy r composed with i = 1_A. If K_B holds
modulo a congruence preserved by composition, then K_A holds modulo it.
Precompose K_B with i∧1_bottom and postcompose it with r∨1_top. The left
side becomes j_A composed with the first projection, by the product and
coproduct equations and ri=1_A. Zero absorption gives the zero on the right.
Only one inverse equation is needed. The paper's negative-literal argument
is the case \(B=\neg\neg A\), \(i=n_A^{-1}\) and \(r=n_A\).

## R6. The complete sign invariant and converse under negation

Manuscript anchor: Section 3, PDF p.4, says that edges between negation normal
forms join occurrences of the same literal. The code proves a statement for
arbitrary formulas before applying normalization.

Lean anchors: Presentation.occurrence_signedLabel/occurrence_label/
occurrence_polarity in
[PresentationSignedLabels.lean](../DosenPetric/PresentationSignedLabels.lean),
and occurrence_negate in
[PresentationNegationOccurrence.lean](../DosenPetric/PresentationNegationOccurrence.lean).

Define \(\operatorname{sgn}_A:\operatorname{Occ}(A)\to\{+1,-1\}\)
by \(\operatorname{sgn}_A(x)=(-1)^k\), where k is the number of negations
above the occurrence x. For every f:A→B and every (x,y) in Gf,
\(\lambda_A(x)=\lambda_B(y)\) and
\(\operatorname{sgn}_A(x)=\operatorname{sgn}_B(y)\).
This follows by induction on the term,
including the double-negation and De Morgan constructors; it does not need
faithfulness. In addition,

\[
 (y,x)\in G(\neg f)\quad\Longleftrightarrow\quad(x,y)\in Gf.
\]

Here \(\operatorname{Occ}(\neg A)=\operatorname{Occ}(A)\), as already defined in the paper. This states the
variance of negation at the level of the interpretation, in addition to the
functorial variance already stated in Section 2.

## R7. What the formal proof of coherence constructs

Manuscript anchor: Section 6, PDF p.9, “Cut elimination and Boolean Coherence
are proved for the presentation defining B(P).” This states the result without
explaining the following architecture of its proof.

The source establishes split comparison maps for the two distributive
patterns in GentzenDistributiveEpi/Mono. A formula in negation normal form is
a retract of a disjunctive normal-form expansion and of a conjunctive
normal-form expansion: there are i:A→D and r:D→A with ri=1_A, and analogous
maps for a conjunctive expansion. These are one-sided equations, not
distributivity isomorphisms.

For a positive arrow from a pure conjunction to a pure disjunction, the
cut-free proof is expressed as a finite union of paths through individual
literals. The occurrence relation determines that union. Products,
coproducts and the retract equations extend this equality criterion to
arbitrary positive endpoints.

For arbitrary reduced terms f,g:A→B, common atomic factorization constructs
formulas A',B', arrows u:A→A' and v:B'→B, and terms f_0,g_0:A'→B'
containing no eta or epsilon constructor. Writing [t] for the quotient arrow
represented by a term t, it gives
\[
 [f]=v\circ[f_0]\circ u,\qquad [g]=v\circ[g_0]\circ u.
\]
It also gives injections a:Occ(A)→Occ(A') and b:Occ(B)→Occ(B') with
\[
 G[f_0]=(a\times b)(G[f]),\qquad G[g_0]=(a\times b)(G[g]).
\]
Here the right sides are direct images of relations along the product of
the injections. Thus G[f]=G[g] implies G[f_0]=G[g_0], positive coherence gives
[f_0]=[g_0], and the displayed factorizations give [f]=[g]. Reduction and inverse
normalization transfer faithfulness to B(P).

With prefix DosenPetric.Reduced, exact entry points are:
Gentzen.DistributiveEpi.section_comparison,
Gentzen.DistributiveMono.comparison_retraction, Gentzen.dnf_expansion/
cnf_expansion, Gentzen.G.mix_normal_form, Gentzen.HasPureNormalForm.faithful,
Gentzen.represented_coherence/positive_coherence, commonAtomicFactor,
faithful_of_positive_coherence, and faithful/boolean_coherence.
The original-presentation endpoint is DosenPetric.Presentation.coherence.
The inventory and source anchors resolve the individual files.

The hundreds of selected-position, replacement, rank and contraction lemmas
support these results. They are not hundreds of omitted independent theorems
that the maximality paper must state. Retained counterexamples concern failed
implementation candidates: atomization need not preserve AllBlocked, and one
terminal replacement fails a required strict-rank condition. The declarations
and their reports explicitly distinguish these from counterexamples to
existential reducibility or published cut elimination. No third source erratum
was established in this audit; Appendix C's two corrections remain unchanged.

## Further consequences and deliberate scope

The following are deductions or proof simplifications, not separately selected
registered theorem statements. They should not be advertised as newly
formalized theorems without adding their own declarations if that is desired.

- **Only constant substitutions are used in all_contexts.** Its positive
  branch substitutes A for every variable; its negative branch substitutes
  \(\neg A\) for every variable and uses the double-negation retraction. Together
  with isolation, this proves the same collapse for an equivalence family
  preserved by composition, pairing, copairing and just these constant
  substitutions. The existing relative_maximality interface assumes closure
  under every substitution. This weakening is visible in the proof, rather
  than separately exposed by its type.
- **Empty variable sets.** Presentation.maximality, fragment_maximality and
  short_maximality do not assume Nonempty P. If P is empty, every occurrence
  set is empty and faithfulness makes B(P) thin already. The paper and three
  selected declarations restrict to nonempty P to address the nonthin case.
  The model corollary uses a chosen variable in its target-projection argument.
- **Finite hom-sets.** Faithfulness injects B(P)(A,B) into the subsets of
  Occ(A)×Occ(B), giving the bound 2^(|Occ(A)| |Occ(B)|). Equal variable/sign
  constraints can sharpen it. This is a deduction from formalized finite
  coordinates and coherence; there is no separately named cardinality theorem
  in the inspected interfaces.

Already present and not counted as omissions: original-endpoint isolation;
both literal signs and the double-negation square; witness-dependent zeros;
the model corollary's all-interpretations quantifier and native target
products; the raw/quotient correspondence and negation closure after the
fragment dichotomy; finite-ordinal substitution including empty blocks,
repeated labels, the worked example, renaming and skeleton reconstruction;
the two source errata; both maximality routes. A prototype relational model
in GeneratedModel.lean is not substituted for the equation-generated category.

## Review, preservation and delivery

The [hostile review](reviews/REVERSE_AUDIT_HOSTILE_2026-11-01.md) and
[writing review](reviews/REVERSE_AUDIT_WRITING_2026-11-01.md) are author-side
AI-assisted reviews. They check the mathematical distinctions above; they are
not independent peer review. The writing source and the cited union antecedent
were consulted. No novelty claim is made for the additional structures.

The provenance directory
`provenance/reverse-manuscript-audit-20261101/` retains the module inventory,
source-level declaration index, import closures, finding anchors, detailed-read
scope and preservation checks. Frozen proof inputs, every manuscript/package,
the existing stash and private staging are preserved. V15's successful
compilation/render inspection is reused; no new manuscript build is claimed.

The reports and provenance are delivered from committed bytes to
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Reverse-Audit-20261101/`.
The delivery receipt records exact source/destination paths and byte/SHA-256
checks. Differing earlier copies are preserved. Completed authorized main is
pushed and its remote ref verified before reporting completion. No external
submission or new registration occurs.
