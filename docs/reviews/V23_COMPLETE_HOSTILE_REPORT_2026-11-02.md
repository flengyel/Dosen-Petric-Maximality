# (A) Kill-shots / hard blockers

**Maximality of the Došen–Petrić Boolean Category, v23.** Manuscript date:
2 November 2026; 23 pages. Complete manuscript audit, prepared at the author's
request. Reviewed repository snapshot:
`f16f66814faf4902e1f3059766a34eb96bab038d`.

**No mathematical error, fatal blocker or major proof gap was established.**
The objections supported by this audit concern exposition and identification
of references. There are eight local findings below, including two optional
deletions/navigation changes. A hostile review is not evidence of an error
unless it exhibits one.

- [Reviewed LaTeX](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.tex),
  SHA-256 `b34afdb82b1f36731ef9c1d8cb6a369b07fc40a71e3189cf3c093677f3b303c2`.
- [Reviewed PDF](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.pdf),
  SHA-256 `732ce3d7886fc837b8297273ca1d33a50346ebc5b0e74a55d2b047cf52dce0c1`.
- Registered Lean source: `5dbee39bea09539bd130f729e82636419f71f920`.
- Pinned toolchain: `leanprover/lean4:v4.35.0`.
- [Source-check evidence](../../provenance/v23-complete-hostile-review-20261102/audit-checks.json).

This is an author-side AI-assisted audit under HostileRefereeGPT — Cat/Rec and
the mathematical-writing skill, not independent peer review. It examines
correctness, typing, self-containedness, correspondence with Lean, exposition,
positioning and reproducibility. It consolidates the
[earlier v23 review](V23_READ_ONLY_REVIEW_2026-11-02.md) and
[focused prose audit](V23_PROSE_REFERENCE_AUDIT_2026-11-02.md), and adds the
claim-by-claim analysis, source comparisons and checks recorded here.
The manuscript is unchanged. This report does not create v24.

# (B) Major weaknesses

None established. This section explains the deductions examined and the
attempts to find failures. The successful checks are not additional objections.

## 1. Actual organization and mathematical contribution

| Part, in reading order | Function |
| --- | --- |
| Abstract; §1 Introduction | State maximality, collapse after every nonderivable equation, the disproved conjecture, proof method, model consequence and formalization. |
| §2 The Boolean proof category | Fix the presentation, arrow operations, zero identity and congruences; state Theorem 2.1. |
| §3 Occurrences and substitution | Define tags, labels and signs; state coherence; construct normalization and substitution. |
| §4 Isolating an occurrence | Isolate a differing pair and derive every K_A. |
| §5 Equality of the product projections | Identify q_A/e_A, prove collapse, finish maximality and prove the model corollary. |
| §6 A second proof and the Lean formalization | Give the mix argument and union laws and identify their formal counterparts. |
| A.1 Occurrence maps and their fibres | Define the blocks and their maps. |
| A.2 The finite-ordinal presentation | Prove the coordinate formula and compute the example. |
| A.3 Shared variables and the maximality argument | Prove renaming compatibility and connect it to substitution in Proposition 4.2. |
| B Diagrams for three defining equations | Display and type the first-injection, zero-identity and zero-law diagrams. |
| C Corrections to the cut-elimination argument used in Boolean Coherence | Identify the two published errors and prove the strict rank comparisons. |
| D.1 Arrow terms and equations | Define derivability, quotient arrows and term congruences. |
| D.2 Reading a Lean declaration | Translate the theorem header and the short proof's steps. |
| D.3 The five declarations | State the registered entry points mathematically. |
| D.4 Congruences on terms and on arrows | Explain the correspondence and additional Lean results. |
| D.5 The proof of coherence | Explain positive coherence, retractions, factorization and normalization. |
| E.1 The inverse of q_A; E.2 The inverse of e_A | Construct the inverse arrows and prove the inverse equations. |
| E.3 The split comparisons used in coherence | Construct the section and retraction and derive their equations. |
| Use of AI tools; references | Give the authorized disclosure and sources. |

The contribution is maximality of the specified zero-identity Boolean
presentation: every nontrivial substitution congruence gives a preorder
quotient. The argument is not a claim about every notion called a Boolean
category. The body supplies two proofs and a model consequence. The ordering
of definitions and deductions works; no alternative outline is recommended.

## 2. Ambient data, equality and variance

The source category is the quotient of typed arrow terms by the published
generating equations and congruence rules. Arrows are quotient classes, not
untyped expressions. A proof congruence is an equivalence relation on each
hom-set, preserved by the specified operations. A substitution congruence
also respects uniform substitution of formulas for variables, on the entire
term and both endpoints. The quotient has the original objects.

| Construction | Typed data and laws checked | Result |
| --- | --- | --- |
| Composition | f:A→B, g:B→C; g composed with f applies f first. Lean `comp f g` uses execution order. | Consistent in the prose, diagrams and inspected declarations. |
| Products and coproducts | Pairing requires a common source; copairing requires a common target. Projections/injections have the displayed types. | The collapse calculations use the correct universal properties. |
| Occurrence functor G | Covariant B(P)→Rel_fin; A maps to Occ(A), f to a relation; identities become diagonals and composition is relational composition. | Correctly used in the original category. |
| Negation | Contravariant: B(P)^op→B(P), with f:A→C sent to neg f:neg C→neg A. Its occurrence relation is the converse. | No variance reversal was missed in the inspected formulas. |
| Double negation | n_A:neg neg A→A is a natural isomorphism between the double-negation and identity functors. | Its inverse is used in the precomposition direction in Proposition 4.2. |
| De Morgan comparisons | Natural comparisons for the corresponding contravariant two-variable functors. | The paper relies on the cited presentation; it does not assert that eta/epsilon are ordinary natural transformations. |
| Substitution F_sigma | Covariant B(P)→B(Q); A maps to A[sigma] and f to f[sigma]:A[sigma]→C[sigma]. | Identity, composition, operation preservation and endpoint transport are accounted for. |
| Normalization | Isomorphisms A→A-circle; the equivalence with the normal-form presentation preserves occurrence relations. | The argument transports inequality before applying coherence. |
| Interpretation I_v | A structure-preserving functor B(P)→C induced by an object assignment v:P→Ob(C). | Composing with substitution gives another interpretation, as required by Corollary 5.3. |

As a variance and empty-hom check, consider the two-element Boolean poset
0<1 with meet, join and complement. Complement takes the arrow 0→1 to the
arrow neg 1→neg 0, again 0→1; a covariant complement would require an arrow
1→0. The manuscript uses the contravariant type. This model also has an
empty hom-set from 1 to 0. Nothing in the manuscript's zero construction
inserts an arrow into that hom-set.

## 3. Every numbered result

### Theorem 2.1: maximality

**Anchor:** p.3, §2, lines 212–225; completion on p.9, lines 714–719.
**Claim:** for nonempty P, every substitution congruence identifying distinct
parallel arrows has a preorder quotient.

The inference is Lemma 4.1 → Proposition 4.2 → Lemma 5.2. The first uses
inequality in the original category and faithfulness; the second uses
substitution closure; the third uses only the resulting equations K_A and
proof-congruence compatibility. No totality is assumed in order to obtain
totality. The conclusion is precisely the universally quantified collapse
statement explained after the theorem. **No failure established.**

### Theorem 3.1: Boolean Coherence

**Anchor:** p.4, §3, lines 295–303.
**Claim:** the occurrence functor is faithful, equivalently equal occurrence
relations characterize equality of parallel arrows.

This is explicitly a cited theorem. The source attribution matches
[Došen–Petrić, Proof-Theoretical Coherence, September 2007 revision,
§14.2, printed p.321](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
D.5 describes the formal proof's construction; it does not supply maximality
as an input to coherence. The inspected source instantiates the faithful
interface through `Gentzen.positive_coherence`, `Reduced.faithful`,
`Reduced.boolean_coherence` and `Presentation.coherence`.
**No false attribution or circular inference established.**

### Lemma 4.1: isolation

**Anchor:** pp.6–7, §4, lines 509–570.
**Claim:** distinct f,g:A→C yield a literal ell and arrows
i:ell∧bot→A, r:C→ell∨top such that one selected composite is the
projection/injection path and the other is zero, after a permitted interchange.

Conjugating by normalization isomorphisms preserves inequality. A pair in
one occurrence relation and not the other has a common literal at its
endpoints. The selector follows the chosen source occurrence: at conjunctions
it pairs with a map through bot, and at disjunctions it chooses an injection.
The coselector uses projections and copairing with maps through top. Their
relations have exactly one pair each, so relational composition separates
the two arrows. Coherence then gives the claimed original-category equations.
Repeated labels do not identify positions, and the literal may be negative.
**No counterexample or typing failure established.**

### Proposition 4.2: all equations K_A

**Anchor:** p.7, §4, lines 587–620.
**Claim:** a substitution congruence identifying distinct parallel arrows
satisfies K_A for every formula A.

For ell=p, substitute A for p and fix the other variables. For ell=neg p,
substitute neg A, giving the equation for neg neg A. Precomposition by
n_A^{-1}∧1_bot has source A∧bot, and postcomposition by n_A∨1_top has
target A∨top. The displayed square transports the nonzero side; absorption
transports the zero side. Substitution acts on the term and its types.
**No hidden positive-literal assumption established.**

### Lemma 5.1: the particular q_A and e_A are isomorphisms

**Anchor:** p.8, §5, lines 624–665.
**Claim:** the two displayed arrows, not merely some arrows between the
same objects, are isomorphisms.

For A=p, the cited object-isomorphism types give a bijection of occurrence
sets. The q_p endpoints each have one occurrence. The e_p endpoints each
have two; precomposition with symmetry, if necessary, matches their order.
Coherence identifies the chosen arrows with isomorphisms. Substitution
preserves their inverse equations for arbitrary A. Appendix E independently
exhibits the inverse terms and verifies those equations. Nonempty P supplies
the variable used in this proof. **No substitution of an arbitrary arrow
for an isomorphism established.**

### Lemma 5.2: collapse from every K_A

**Anchor:** p.8, §5, lines 667–712.
**Claim:** a proof congruence containing all K_A has a preorder quotient.

Put E=A∨top, S=(A∧bot)∨top and s:top→E. In the original category, the
zero arrow from A∧bot to E equals the path through top, by coherence.
Modulo the congruence, q_A=s∘!_S. Its inverse equation gives
1_E=s∘!_E, while !_E∘s=1_top. Thus E is terminal in the quotient.
The projection A∧E→A is invertible; composing it with e_A makes
pi_1:A∧A→A invertible. Its right inverse is the diagonal, so the two
projections coincide. Pairing then gives equality of arbitrary parallel
arrows. Product and coproduct equations pass to quotient classes.
**No application of coherence in the quotient established.**

### Corollary 5.3: arbitrary target arrows

**Anchor:** p.9, §5, lines 721–751.
**Claim:** if an additional source equation holds under every interpretation
in a zero-identity Boolean category C, then C is a preorder.

Agreement under all interpretations gives a proof congruence. Since
I_v∘F_sigma is the interpretation induced by p↦I_v(sigma(p)), that
agreement is substitution closed. Theorem 2.1 makes it total. Choose a
variable p and interpret it as an arbitrary target object X; the two
projections X∧X→X are equal. Pairing any target arrows a,b:Y→X then gives
a=b. Surjectivity of the interpretation on arrows is unnecessary.
The source theorem `PresentationSemantics.model_corollary` has the same
quantification over all native target arrows. **No fixed-interpretation
kernel or hidden surjectivity assumption established.**

## 4. Central unnumbered assertions and both proof routes

| Anchor | Assertion and deduction examined | Result |
| --- | --- | --- |
| §2, p.3, lines 179–185 | A witnessed zero is independent of its witness by the zero law; pre/postcomposition supplies the witnesses for the absorbed zeros. | Empty hom-sets remain possible. |
| §3, p.4, lines 277–293 | Every related occurrence pair preserves its variable and sign. The generator cases, composition and binary operations preserve that property. | No loss of negative literals found. |
| §3, p.4, lines 305–317 | Hom(top,E) has at most one member because Occ(top) is empty, whereas id_p differs from zero_p. A self-exponential would contradict the resulting hom-set bijection. | The argument concerns cardinality at most one; it does not assume a global point exists. |
| §3, pp.4–5, lines 319–354 | Normalization preserves occurrence interpretation; negation takes converse, transported back by the normalization bijections. | Correct direction of the converse and endpoint transport. |
| §3, pp.5–6, lines 356–458 | Each original occurrence has its own inserted block. A substituted edge matches equal inner positions in blocks belonging to the same variable. | Repeated positions and empty blocks are retained correctly. |
| §3, p.6, lines 459–482 | Substitution identity, composition and extensionality include the formula equalities identifying endpoints. | No untyped equality between terms with different endpoints found. |
| §4, p.7, lines 572–585 | If r∘i=1_A, pre/postcomposition transports K_B to K_A. | A retraction suffices; an inverse is not silently assumed. |
| §6, pp.9–10, lines 776–843 | The mix expression is independent of B; h_A is symmetric. K_A first gives equality of the injected projections, then terminality of A∨top, then h_A=pi_1 using the B=top expression and the first-injection equation. | The displayed second proof reaches equal projections and collapse. |
| §6, pp.10–11, lines 845–889 | The occurrence relation of union is relational union. Faithfulness gives associativity, commutativity, idempotence, composition compatibility and the join order. | The empty union and least element are restricted to inhabited hom-sets. |
| D.1/D.4, pp.15–18 | Derives is contained in a primitive congruence; quotient relations are independent of representatives; substitution closure descends through the term/quotient square. | The term/arrow distinction is maintained. |
| D.3, pp.17–18 | Failure of the reverse inclusion R⊆Derives invokes maximality, yielding the dichotomy. id_p has a diagonal relation, zero_p an empty one. Boolean evaluation rules out a term top→bot. | All five statement translations match their selected types. |
| D.4, p.18, lines 1458–1463 | A uniformly closed fragment becomes equality or totality; both preserve negation. | Negation closure is concluded after the dichotomy, not assumed in the fragment proof. |

The union-zero correspondence deserves precision: `Reduced.union_id_zero`
proves the identity/zero case. The same module also proves
`Reduced.union_zeroOf`, deriving f union zeroOf(w)=f from composition
compatibility and witness independence. The general law stated in the paper
therefore has a named source proof; it is not an unproved extrapolation from
the identity case.

## 5. All appendix constructions

**Appendix A, pp.11–13.** The maps o_M and o_i have declared finite domains
and codomains. Every (r,t) lies in a uniquely tagged block; gamma sends it
to (o_M(r),o_i(t)) with i=o_M(r), so both squares commute and uniqueness
follows from the injections. Consecutive numbering is bijective even with
empty blocks. For a source coordinate x, the unique nonempty containing
block supplies t=x−s_(r−1), giving the stated delta formula. The skeleton
retains the connectives and constants; the occurrence map restores labels.
The eight example outputs are 4,3,4,1,2,4,3,4, and position 2 maps to 3.
Noninjective renaming changes labels, not occurrence coordinates. The final
positive/negative specializations have A and neg neg A at the stated
endpoints. **No undefined map, lost tag or empty-block exception found.**

**Appendix B, p.14.** Every path in the three diagrams was typed. The first
triangle is A∧B→(A∧B)∨C. The five-arrow path starts and ends at A, with
intermediate objects A∧top, A∧(neg A∨A), (A∧neg A)∨A and bot∨A.
The zero square has the parallel composites f∘0_A and 0_C∘g; it does not
require f=g. **No reversal of composition or endpoint mismatch found.**

**Appendix C, p.15.** One-sided ranks count clusters and are at least one.
For the p.260 reduction, the unchanged left rank and strictly smaller right
ranks give both strict decreases. For the p.262 reduction, the fresh right
rank is one, so the total is L+1; the contracted original right cluster has
R>1, giving 2≤L+1<L+R. The cut degree is unchanged. These conclusions
agree with the published reductions and the original-rank source steps
identified in the earlier review. **No incorrect total-rank-one claim remains.**

**Appendix D, pp.15–20.** The five declarations are translated as quantified
statements about typed terms. `Total` does not produce terms in empty
hom-sets. D.2 gives the meaning of hypotheses and proof commands and the
short proof's mathematical correspondences. The factor relation on quotient
arrows is representative independent; conversely, pulling back a substitution
congruence gives a primitive term congruence. The source modules establishing
the full coherence and model result exist beyond the five entry points.
**No mismatch between a selected statement and the prose was found.**

**Appendix D.5, pp.19–20.** Positive means no eta_p/epsilon_p constructor.
The union laws needed before coherence are derived from presentation
equations, not from faithfulness. Split comparison maps construct normal-form
retractions. At pure endpoints, Gentzen representation, cut elimination and
thinning atomization reduce to unions of literal paths. Positive coherence
then extends through the retractions. Common factorization gives the same
outer arrows and positive middle terms for both inputs; equal original
relations give equal middle relations, hence equal arrows. Normalization
transfers faithfulness. **The architecture is noncircular on the inspected
source path.** C1/C2 and D3/D4 below concern explaining that architecture.
The audit does not independently reconstruct every cut-elimination branch.

**Appendix E.1, p.20.** The path u_A:A→(A∧bot)∨top is well typed; the
copair with the second injection has source A∨top. Its occurrence graph
is the inverse of Gq_A. Both inverse equations follow by coherence in B.

**Appendix E.2, p.21.** The five stages of c_(X,Y;U,V) have the displayed
endpoints. Precomposing with the diagonal supplies the section s. The
zero used in the second copair component has a witness
Delta_A∘pi_1:A∧top→A∧A. Killing that summand leaves exactly the inverse
graph of Ge_A, including the empty-occurrence case. **No unwitnessed zero
or implicit distributivity isomorphism found.**

**Appendix E.3, pp.21–22.** The expressions v, b and t have the stated
types. Product projections prove c-wedge∘s=id; coproduct injections prove
t∘c-vee=id. The source's section/retraction proofs use the presentation
equations, including the mix/diagonal/codiagonal identity, before coherence.
The proof does not need the other composites to be identities.

## 6. Explicit checks of possible incorrect strengthenings

These examples test hypotheses and possible readings; they do not contradict
statements in v23. No minimality claim is made for either example.

**One interpretation is insufficient.** Let P={p,q}. In the category of finite
sets and relations, use disjoint union for both product and coproduct, empty
set for both units, and relational converse for negation. Interpret p by the
empty set and q by a singleton. Then id_p and zero_p have the same interpreted
relation. After substitution p↦q they have different interpreted relations:
the singleton diagonal and the empty relation. Thus this fixed kernel is not
substitution closed. The model proof avoids exactly this failure by using
agreement under every interpretation.

**A split comparison is not necessarily an isomorphism.** For singleton
X,U,V, the occurrence relation of c-wedge maps four positions to three:
c={(0,0),(1,1),(2,0),(3,2)}. The section relation is
s={(0,0),(0,2),(1,1),(2,3)}. Relational composition gives c∘s=id_3, whereas
s∘c contains (0,2) and (2,0) and is not id_4. The finite calculation is
recorded in the evidence. The manuscript uses only the split equation.

## 7. Primary-source comparisons, positioning and novelty

The following verifies the claims made in the paper, not an exhaustive
priority search. The report does not certify a first-in-the-literature claim.
The paper makes no unsupported assertion that its theorem follows from
maximality for a different class of categories.

| Source | Passage examined and result |
| --- | --- |
| [Proof-Theoretical Coherence, revised September 2007](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf) | Printed pp.316–322 fix the presentation, coherence and conjecture; p.294 gives the isomorphism types. The cut-rank passages are pp.249,253,260,262. The manuscript identifies the correct category and conjecture. |
| [The Maximality of Cartesian Categories, §5](https://arxiv.org/html/math/9911059v1) | The comparison to reduction of an equation to equal product projections is supported. |
| [Isomorphic Formulae in Classical Propositional Logic, Lemmas 6–7](https://arxiv.org/html/0912.1271v3) | The negation-free and tautology hypotheses in the manuscript's Lemma 6 comparison are present. Lemma 7's occurrence-bijection construction supports the isomorphism comparison. |
| [Typed lambda calculus and cartesian closed categories, §11](https://arxiv.org/html/math/9911073v2) | The theorem concerns cartesian closed categories and uses typed Böhm separation. V23 explicitly explains why it does not apply here. |
| [Bicartesian Coherence Revisited, §§8–10](https://arxiv.org/html/0711.4961v3) | The lattice/dicartesian comparison distinguishes maximality and relative maximality and does not add a distribution hypothesis to that source. |
| [Syntax for split preorders, §16](https://arxiv.org/pdf/0902.0742v7) | The cited occurrence-pair separation method is present in the maximality arguments. |
| [Constructing free Boolean categories, Theorem 3.5.4](https://www.lix.polytechnique.fr/Labo/Lutz.Strassburger/papers/FreeBool.pdf) | The cited proof-net/free-category comparison concerns a different categorical structure. |
| [On the axiomatisation of Boolean categories, Definition 5.5](https://www.lix.polytechnique.fr/Labo/Lutz.Strassburger/papers/medial.pdf) | The comparison with monoid/comonoid structures on a star-autonomous category is supported. |
| [Order-enriched categorical models, (11), Theorems 6.4–6.5](https://carstenfuehrmann.org/papers/order-enriched-models-for-classical-sequent-calculus.pdf) | Ordered soundness/completeness and the negation triangle support §2's comparison. The latter composite is identity after unit comparison; it is not the zero-identity law used here. |
| [The Unbearable Notation of Logic, pinned v8, §9](https://github.com/flengyel/notes/blob/42eaccdccf6413fe4d643a347fab33edafb1c056/logic/The-Unbearable-Notation-of-Logic_v8.pdf) | Tagged blocks, gamma and ordinal coordinates agree with Appendix A. |

The three author-hosted papers initially failed in the web interface; complete
PDFs were subsequently retrieved from the authors' public sites. The two other
PDFs were retrieved from arXiv and the pinned GitHub revision. Their URLs and
SHA-256 values are recorded in the evidence. No inaccessible excerpt is treated
as a completed full-text comparison. Only the relevant passages, not every
page of every cited work, were read.

## 8. Reproducibility and Lean correspondence

Fresh source checks established:

- All 56 Lean-link occurrences resolve to 49 distinct line destinations at
  the registered commit; every destination starts the named declaration.
- All linked files match the working tree byte for byte. There are no
  production Lean changes between the registered source and reviewed snapshot.
- The five selected theorem signatures in Challenge and production match
  after whitespace normalization. D.3's statements retain the same hypotheses.
- The scan covers 849 modules under DosenPetric plus the root aggregator.
  It finds no production `sorry`, `admit`, `native_decide` or custom axiom
  declaration. The only raw “axiom” match in the directory is a comment
  explicitly saying that a premise is not supplied as an axiom.
- All 83 LaTeX reference occurrences resolve to the 34 labels.

Challenge's five `sorry` bodies are the problem statements for the verifier;
Solution imports the production proofs. They are not implementations of those
proofs. No production proof hole is inferred from their presence in Challenge.
The five selections are entry points, not the whole formalization. The model
corollary and the additional appendix declarations were inspected as further
source results.

This is a source/correspondence review. Earlier successful compilation, kernel,
Comparator, preflight and service checks are reused, not claimed as newly run.

# (C) Minor issues

| ID and anchor | Wording and exhibited difficulty | Basis and consequence | Recommended repair |
| --- | --- | --- | --- |
| C1: D.5, p.19, lines 1581–1586 | “Gentzenization, cut elimination and atomization express ...”: the role of atomization is not explained. | `ambiguous`; `absence_in_text` plus source inspection. This impedes the stated translation guide, not the main theorem. | Explain the representation, elimination and replacement of compound weakening by weakening on literals/constants. |
| C2: D.5, p.20, lines 1606–1614 | “atomic factorization constructs ...”: “atomic” has no explained referent in the displayed data. | `missing_definition`; `absence_in_text`. The factorization's typed properties are stated; the label is the problem. | State the existence of the data directly and repair the following pronoun. |
| C3: D.2, p.17, lines 1373–1374 | “These parameters supply the structures and equations used in the four steps above.” | Optional economy; the preceding sentences already identify each parameter and its role. No mathematical failure is alleged. | Delete this recap. |

All three are **minor** and locally repairable. C3 is optional. None establishes
a false theorem, missing Lean proof or invalid inference.

For C1, the suggested replacement is:

> Represent the arrow by a Gentzen derivation, eliminate its cuts, and replace
> weakening on compound formulas by weakening on literals and constants.
> At these endpoints, the denotation of the resulting derivation is a finite
> union of the paths j_y composed with p_x.

Retain the following empty-union sentence. The source's unrestricted
`cut_elimination` followed by `atomize` supports this order of explanation.
The actual normal-form theorem also establishes the endpoint conditions.

For C2, replace “atomic factorization constructs” by “there are”, and replace
“It also gives injections” by “There are also injections”. Keep the displayed
equalities, the direct-image conditions and the exact Lean declaration name.
The source name has a meaning involving eta/epsilon data; the paper need
not introduce a second label to state the factorization it needs.

These applications follow KLR's discussion of connected explanation, reader
expectations and unnecessary jargon in
[Mathematical Writing, §1, points 10–12 and 26](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
C3 is an independent economy judgment. KLR does not forbid useful complementary
explanations, and this review does not recommend deleting the Lean tutorial.

# (D) Cross-section consistency failures

| ID and anchor | Claim as written and failure mode | Evidence and impact | Exact local repair |
| --- | --- | --- | --- |
| D1: §1, p.1, lines 68–71 | “give the equation of [1, §9.7, pp.215–216]”; `ambiguous`. | `absence_in_text`: no local equation identifier is supplied in the outline; §4 identifies it. This is a loose pointer, not a false citation. | Refer to equation K_A in §4, retaining the source attribution. |
| D2: §1, p.1, lines 72–76 | “The two isomorphisms listed in [1, §12.5, p.294]”; `ambiguous`. | `absence_in_text`: the reader is sent outside the paper before the particular arrows are identified in Lemma 5.1. | Begin “The isomorphisms of Lemma 5.1 ...”, retaining the source citation. |
| D3: §6, footnote 7, p.11, lines 887–889 | reduceHom/recoverHom “identify these expressions with arrows of B(P)”; `ambiguous`. | `absence_in_text` plus source signatures: the main text already states the formulas in B(P), while the footnote does not identify the normal-form hom-sets. | State that the linked Lean laws concern the normal-form presentation and that the mutually inverse hom-set maps transfer them to B(P). |
| D4: D.5, p.20, lines 1625–1626 | “normalization and recovery maps of Section 3”; `ambiguous`. | `absence_in_text`: §3 states the equivalence and occurrence compatibility but does not name recovery maps. Named reduceHom/recoverHom occur in §6's footnote. | “The equivalence of Section 3 preserves the occurrence interpretation and therefore transfers faithfulness from R(P) to B(P).” |
| D5: D.4, p.18, lines 1454–1456 | “the substitution square with Q=P”; `ambiguous`, optional navigation polish. | `absence_in_text`: D.1 contains the intended term/quotient square; §3 contains another substitution-related square. The inference is recoverable. | “the substitution square in Appendix D.1, with Q=P ...”. |

All five are **minor**; D5 is optional. The repairs identify existing objects
and deductions. They do not introduce new mathematical premises. Together with
C1–C3 these are the eight supported findings.

## Definition order, qualifications and prose that should be preserved

- B(P), composition and the arrow operations are introduced in §2; occurrence
  sets, labels, signs, literals and substitution are introduced in §3 before
  their proof use. Introductory previews do not need duplicate definitions.
- Positive terms and arrows are explicitly defined at the start of D.5.
  The canonical comparison arrows are given by their product/copairing
  formulas; “canonical” is not concealing a choice of an unspecified arrow.
- Nonempty variable sets, empty occurrence sets, empty blocks, literal signs,
  witnessed zeros and one-sided inverse equations are mathematical
  qualifications. They are not weasel phrases.
- No empty “genuine”, “actual”, “obvious”, “clearly”, “essentially”,
  “straightforward”, “remarkable” or “interesting” qualifier remains in the
  reviewed prose. “Structural” survives only in internal reference keys;
  “raw” survives in an exact Lean identifier. Those keys need not be renamed.
- The authorized disclosure and the explanations of Lean syntax serve stated
  purposes. They are not accidental process narration. The accepted abstract
  introduces the formalization and does not imply that Lean substitutes for
  the paper's proofs.

# (E) Acceptance conditions, non-negotiable

No unmet mathematical condition was established. The following conditions
are already satisfied in the reviewed argument and must survive any prose
repair. They are stated here to make the audit's mathematical requirements
verifiable, not to impose a new approval or publication procedure.

| Required condition | Endpoint examined | Consequence if absent |
| --- | --- | --- |
| Additional equations are closed under uniform substitution on terms and types. | §2 definition; §3 functor; Proposition 4.2; D.1/D.4 closure. | The stated universal collapse deduction would not follow. |
| Coherence is applied in the original category. | Lemma 4.1, Lemma 5.1, the original equations in Lemma 5.2/§6, Appendix E. | A proof using faithfulness in the quotient would need reconstruction. |
| Zero arrows and empty unions require an existing-arrow witness. | §2, §6, D.5 and E.2. | A blanket zero-morphism assertion would change the category. |
| The particular q_A/e_A have proved inverse equations. | Lemma 5.1, E.1–E.2 and the named production proofs. | The short proof could not be retained without replacing that step. |
| Model agreement is over all interpretations. | Corollary 5.3 and SemanticModelCorollary.lean. | Fixed-kernel agreement alone does not support the model conclusion. |
| DNF/CNF comparisons are used as retractions. | D.5 and E.3. | An unsupported distributivity-isomorphism claim would have to be removed. |
| The appendix rank corrections give strict descent from the original cut. | C and the linked rank declarations. | The stated justification of those induction calls would fail. |

No claim needs to be dropped on the evidence found. C1–C3 and D1–D5 are local
expository repairs; none is a mathematical rejection condition. The report
does not authorize implementation or an arXiv/Palomar action.

# (F) Not checked / uncertainty log

**Material read.** The complete 1,781-line v23 source was read, including
footnotes, appendices and bibliography. The earlier full review's mathematical
work, the focused rereading and the additional source checks belong to this
continuous review session. All 23 PDF pages were inspected in the earlier
v23 phase, with individual inspection of pp.15,20,23; current extracted PDF
text supplies the page anchors. The source and PDF hashes are unchanged.
No new layout build was performed.

**Selected source depth.** Full relevant declarations/proof passages were
read in PalomarMaximality, PresentationMaximality, PresentationShortMaximality,
PresentationShortProjection, PresentationShortQ/E, PresentationCoherence,
ReducedCoherence, SemanticModelCorollary, CommonAtomicFactorization,
ReducedQuotientReduction, ReducedRecovery, ReducedUnion,
GentzenDistributiveEpi/Mono, GentzenPositiveCoherence,
GentzenPurePositiveCoherence, GentzenPureNormalForms, GentzenCutElimination,
PresentationSubstitutionRelation, PresentationNegationOccurrence and
FormulaSubstitutionLaws, together with the relevant isolation and rank passages.
The all-module token/link inventory is broader than this proof-body reading.

**Limits.** This is not a line-by-line independent reconstruction of all 850
Lean modules or every cut-elimination reduction. The raw-token scan is not a
replacement for a transitive kernel/axiom audit. Existing passed builds and
verification are reused. No Lean build, kernel replay, Comparator, preflight,
service verification, registration, publication monitor or arXiv upload was
repeated. Bibliographic passages were checked as recorded in B.7; no exhaustive
new literature search or independent novelty certification is claimed.

**Technical qualification outside the paper.** The v23 release report's
literal whole-file “byte-identical” description of the Palomar BibTeX has one
harmless exception: an additional trailing newline. The entry fields and
rendered citation are unchanged. This does not create a manuscript or proof
defect and is not included among the eight findings.

**Delivery.** Retained report:
`docs/reviews/V23_COMPLETE_HOSTILE_REPORT_2026-11-02.md`.
Downloads target:
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-V23-Review-20261102/V23_COMPLETE_HOSTILE_REPORT_2026-11-02.md`.
The report is delivered from committed bytes with byte/SHA-256 verification
and a separate receipt. The evidence contains public source metadata and
checks, not credentials, private responses or unregistered review material.
Only the report, evidence and delivery receipt are added; no manuscript or
Lean source is edited.

Strongest confirmed blocker: **none established**.
Strongest suspected unconfirmed blocker: **none supported by the evidence**.
Most important unchecked item: independent reconstruction of the entire
cut-elimination dependency and all transitive Lean proof bodies.
No finding in this report depends on material that remained unavailable.
Final formal referee recommendation: **unknown**. The audit supports local
expository repairs and supplies no mathematical basis for rejection; it is
not an independent journal decision.
