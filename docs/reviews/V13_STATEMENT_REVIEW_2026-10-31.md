# V13 statement and mathematical-writing review

31 October 2026. Author-side AI-assisted review of v12 at
`cbcd59ca1b9382bdcd0de8c648e4a351495ccf81`; corrections implemented in v13.
This is a new pass through the whole manuscript, not a rerun of a word filter.
The source has 929 lines; the revised source has 964. The introduction is the
manuscript's literature review. Bibliography databases were reviewed separately.

## Diagnosis and governing source

The central argument survives this pass. One literature sentence overstated
the scope of a cited lemma: *Isomorphic formulae*, Lemma 6, requires formulas
without negation. V12 omitted that restriction. The previous review missed it.
The paper's own isolation argument already requires equality of signed literals;
the error is in the introductory account of prior work.

The remaining changes add close antecedents, state the precise hypotheses and
conclusion of two cited results, and replace a compressed account of the
symmetric-fold proof by its intermediate equations. The revised prose follows
the authors' mathematical order: define the objects, give the maps and equations,
and make the deductions. No theorem is described as a “framework”, “mechanism”,
or “structural insight”. Standard terms are retained when they specify a method
or object; “structural induction on the formula” says exactly which induction
proves the renaming square.

Knuth, Larrabee and Roberts, *Mathematical Writing*, especially §§1 and 4–5,
was read for this pass. Its requirements concerning sentence structure,
definitions before use, unambiguous references, and mathematical prose govern
the revision. The source PDF and its hash are recorded in the source manifest.
Došen–Petrić's proofs in *The maximality of cartesian categories*, §5, and
*Proof-Theoretical Coherence*, §§9.7 and 12.5, provide the requested model of
exposition. The manuscript does not copy their sentences.

## Outline recorded before editing

The argument already has the required order. No section is moved. The two
collapse proofs remain distinct; the second is expanded where it occurs in §6.

| V12 lines | Part | Function |
| --- | --- | --- |
| 1–48 | Title, metadata and abstract | State nonempty P, closure operations and principal conclusion. |
| 49–110 | Introduction | Conjecture, reduction to projections, comparison of related results, notation and source edition. |
| 112–215 | The Boolean proof category | Define formulas, operations, witnessed zeros, congruences and maximality; state main theorem. |
| 217–358 | Occurrences and substitution | Faithful relational interpretation, nonthinness, exponential obstruction, normal forms, signed literals and substitution maps. |
| 360–464 | Isolating an occurrence | Construct selected one-edge relations and transport the contextual equation by substitution, including negative literals. |
| 466–585 | Contextual collapse | Identify q/e, prove thinness and main theorem, then obtain the model corollary by universal agreement. |
| 587–637 | Lean formalization | State syntax/quotient correspondence, both proof routes and registered declaration family. |
| 640–732 | Appendix A.1: profiles and their fibres | Define labelled blocks, gamma and chi; prove square identities. |
| 733–802 | Appendix A.2: finite ordinals | Prefix sums, encoding bijections, block locator, skeleton/profile reconstruction and worked example. |
| 804–836 | Appendix A.3: shared variables | Renaming square and positive/negative contextual instances. |
| 838–888 | Appendix B | Typed diagrams of three defining equations. |
| 890–912 | Appendix C | Correct two source rank sentences and justify each correction. |
| 914–929 | Disclosure and bibliography | Preserve authorized disclosure and identify exact sources. |

## Definitions, types and conventions

All arrows below are total categorical arrows. No partial-map or computability
claim occurs. Equality in B is the presented equality of arrows. Equality
modulo a congruence is written ≡ only after that convention is declared.

| Object or operation | Data and type | Laws and use checked |
| --- | --- | --- |
| B(P) | Objects: formulas over nonempty P. Morphisms: typed terms modulo the defining equations. | Composition applies the right-hand arrow first in manuscript notation. Empty hom-sets are allowed. |
| Product and coproduct | Pairing takes X→A and X→B to X→A∧B. Copairing takes A→X and B→X to A∨B→X. | Projection/injection equations and uniqueness used in isolation and both collapses have these endpoints. |
| Distributor | d: A∧(B∨C)→(A∧B)∨C. | First-injection equation has domain A∧B, codomain (A∧B)∨C. No inverse for d is asserted. |
| Negation | Contravariant functor Bᵒᵖ→B, sending f:A→C to ¬f:¬C→¬A. | Reverses composition; double-negation maps are isomorphisms. A one-arrow category X→Y does not permit treating this operation as covariant. The proof uses the stated variance. |
| η, ε, 0 | η_A:⊤→¬A∨A; ε_A:A∧¬A→⊥; 0_A:A→A. | The five-arrow path defining 0_A has matching consecutive endpoints. It is not the identity; G0_A is empty. |
| Witnessed zero | 0_{A,C}=f∘0_A, requiring an existing f:A→C. | The zero law gives independence and both absorption laws. Nothing supplies an arrow in an empty hom-set. |
| Congruences | Equivalence relations on hom-sets, stable under specified operations; substitution congruences also stable under all σ. | A single interpretation kernel is not silently treated as substitution-closed. The model proof uses agreement under every interpretation. |
| G | Covariant B→Rel_fin; A↦Occ(A), f↦its occurrence relation. | Relational composition and diagonal identities; projection/injection graphs, union for pair/copair, rebracketing for d. Coherence is used only in B. |
| Occ and labels | Finite positions; λ_A:Occ(A)→P. | Repeated labels have different tags. Constants have no positions. Negation preserves positions, not the sign attached to a literal. |
| F_σ | Covariant B(P)→B(Q), A↦A[σ], f↦f[σ]. | Presentation substitution rule preserves equations, identities, composition and operations. Q may be empty. No surjectivity is asserted. |
| D, E_σ | D is the finite dependent sum over Occ(A); E_σ is the sum over P. | E_σ need not be finite if P is infinite. The paper does not put it in Rel_fin. The block square is a square of functions. |
| NNF comparison | a_A:A→A° is an isomorphism. | Conjugation sends f:A→C to a_C∘f∘a_A⁻¹:A°→C°. Selectors are transported back with the displayed inverse directions. |
| q_A, e_A | q_A:(A∧⊥)∨⊤→A∨⊤; e_A:A∧A→A∧(A∨⊤). | Particular arrows are identified with source isomorphisms by their bijective occurrence relations, then substituted. No fullness of G is assumed. |
| Interpretation | B(P)→C for an object assignment P→Ob(C), preserving the named operations. | Composition with F_σ is another interpretation. Arbitrary target arrows are equated by target pairing, without assuming they are in a functor's image. |
| γ, χ, δ | γ:D→C, χ:Occ(M[Φ₀])→D, δ:[s_m]→[t_k]. | χ and the two encoders are bijections; γ and δ need not be. Empty blocks, repeated values and unused placeholders are permitted. |
| Renaming | ρ:C→Q, inducing Form(C)→Form(Q). | ρ need not be injective. Induction proves the formula square; occurrence positions remain distinct. |

The manuscript refers to the full presentation rather than reproducing every
generating equation. That declared dependence is retained. This review verifies
the equations used in the argument and the cited source passages; it is not a
new derivation of all of Boolean Coherence.

## Numbered statements

Each proof was checked from its explicit hypotheses. No unused hypothesis or
missing type was established in these seven statements.

| Statement | Hypotheses and use | Proof check |
| --- | --- | --- |
| Theorem 2.1, maximality | P≠∅; θ is a substitution congruence; distinct parallel f,g are identified. | Faithfulness supplies a differing edge. Isolation yields K_ℓ, and substitution yields every K_A. The q/e collapse equates both projections and hence every parallel pair. Equality and total congruence are distinct because the original projections differ. |
| Theorem 3.1, Boolean Coherence | The particular DP zero-identity Boolean presentation and its occurrence functor. | Checked against DP §14.2, p.321 and the source claim map. It is cited, not proved anew in this manuscript. In later applications arrows are parallel and coherence is invoked before taking the quotient. |
| Lemma 4.1, isolation | f,g:A→C distinct; original B; both signs allowed. | Normalize endpoints by isomorphisms. Choose an edge in the relational difference; its ends have the same signed literal. Recursive selector/coselector relations isolate exactly that edge. Coherence supplies the two equations and inverse comparisons restore original endpoints. |
| Proposition 4.2, all contexts | θ is stable under composition and uniform substitution and identifies distinct arrows. | Apply Lemma 4.1. For ℓ=p use p↦A. For ℓ=¬p use p↦¬A and conjugate by the displayed double-negation maps. Absorption transports the zero. An empty Occ(A) causes no exception. |
| Lemma 5.1, q/e isomorphisms | Every formula A; a variable p is available from P≠∅. | DP p.294 provides the endpoint isomorphisms for p. A one-element bijection fixes q_p. One of the two permutations makes the relation of e_p agree with the chosen isomorphism. Coherence identifies the arrows. Substitution preserves both inverse equations. |
| Lemma 5.2, contextual collapse | Proof congruence θ containing every K_A; substitution closure is not required here. | q_A becomes s∘! and remains invertible, making E=A∨⊤ terminal in the quotient. Therefore r:A∧E→A is invertible, as is e_A. Their composite π₁ is invertible with inverse Δ. Since π₂Δ=1, π₁≡π₂; pairing equates arbitrary arrows. |
| Corollary 5.3, models | P≠∅; f≠g in B; all interpretations in a zero-identity Boolean category C equate them. | Universal agreement is an operation- and substitution-closed congruence. It is total. Choose p and interpret it as any X, giving equal projections X∧X→X. Target pairing equates arbitrary a,b:Y→X. No fixed-kernel closure, fullness or essential surjectivity is used. |

## Other mathematical assertions

The introduction's literature assertions are checked separately in the
[literature review](V13_LITERATURE_REVIEW_2026-10-31.md). The following ledger
covers the constructions and deductions outside the seven statement environments.

| Anchor | Assertion and conditions | Derivation or check |
| --- | --- | --- |
| §2, zero law | f∘0_A is independent of f, when A→C exists. | For parallel f,g both f0_A and g0_A equal 0_Cg. Taking f=g gives commutation. Associativity then proves left and right absorption with existing composite witnesses. |
| §2, maximality definition | The only substitution congruences are equality and total. | If θ is not equality it contains a distinct pair. The theorem makes it total. Conversely this dichotomy implies every distinct-pair extension collapses. This is a restatement, not another theorem. |
| §3, finite coordinates | Occ(A) has a left-to-right finite ordinal bijection. | Induction: one variable position, empty constants, unchanged set under negation, concatenation at either binary connective. Equal labels never identify positions. |
| §3, occurrence functor | d has the rebracketing graph and zeros have empty graphs. | DP p.60 and pp.317–321; the tagged map preserves every original occurrence. It is a bijection of occurrence sets, not a claim that d is invertible in B. |
| §3, nonthinness | π₁,π₂:p∧p→p differ. | Their singleton relations have different source tags. Also 1_p has the nonempty diagonal and 0_p has the empty relation. |
| §3, no self-exponential | No object p⇒p for p∈P. | Occ(⊤)=∅ makes B(⊤,E) at most a singleton by faithfulness. B(p,p) contains distinct 1_p and 0_p. An exponential would biject these hom-sets, after the product unit isomorphism. |
| §3, Joyal result | CCC with initial ⊥ and A≅(A⇒⊥)⇒⊥ is thin. | The exact version on DP p.324 is now stated. Its cartesian-closed hypothesis fails for B by the preceding hom-set argument. This is comparison, not a step in maximality. |
| §3, normalization | Ga_A is a bijection graph. | The chosen NNF maps are isomorphisms; every isomorphism in Rel is the graph of a bijection. Source and target occurrences transport in the directions used in Lemma 4.1. |
| §3, signed edges | Every edge between NNF formulas preserves the signed literal. | In the atomic NNF presentation, η_p, ε_p and zero maps have empty relations. All other listed generators preserve signed labels. Composition and the binary operations preserve that property. The equivalence preserves G. |
| Eq. (4) | Occ(A[σ])≅Σ_x Occ(σ(λ_Ax)), for arbitrary Q. | Induction on A: singleton block for a variable, empty constants, tagged unions for binary connectives, unchanged positions under negation. Repeated outer positions create distinct copies. |
| Eq. (5) | pr_E∘λ̂=λ_A∘pr_D and the image criterion. | Both sides send (x,t) to λ_A(x). For the same well-typed inner t, equality of image pairs is exactly equality of old variable labels. No injectivity of λ_A is presumed. |
| §3, F_σ | Uniform substitution acts on source, target and arrow representative. | Every defining equation is closed under (su), so the term map descends to a functor. The empty variable-set case uses the same grammar. |
| K_A | Contextual zero equals the three-arrow composite through ⊥ and ⊤. | Both are existing parallel arrows A∧⊥→A∨⊤ with empty occurrence relation; apply original coherence. DP pp.215–216 provides the contextual comparison. |
| Lemma 4.1 selectors | b_V and t_V exist for every V and have empty relations. | b_V factors through ⊥ and t_V through ⊤. Product selection pairs with b_V; coproduct selection injects. The dual construction projects or copairs with t_V. Only the chosen path contributes an edge. |
| Proposition 4.2 square | The outer composite equals k_A. | Product projection cancels n_A⁻¹ on the input and the coproduct map applies n_A on the output. Their inverse equation leaves j_Aπ₁. The other side is zero by absorption. |
| Lemma 5.1 comparisons | The cited endpoint isomorphisms identify the particular q/e maps. | For q there is exactly one bijection of the singleton occurrence sets. For e, swap the two source occurrences if necessary. This does not infer an arrow from an arbitrary relation. |
| Lemma 5.2 quotient | Product/coproduct structure passes to θ-classes. | Pairing and copairing are well-defined by compatibility. Their beta/eta equations descend, proving uniqueness. This argument does not use coherence of the quotient. |
| Lemma 5.2 terminal E | q≡s! implies 1_E≡s!_E. | Compose with the retained inverse q⁻¹; uniqueness into ⊤ identifies !q⁻¹ with !_E. Also !_Es=1_⊤. These equations imply each arrow into E equals s! of its domain. |
| Lemma 5.2 equal projections | r e=π₁; π₂≡π₁. | r⁻¹=〈1,s!〉 by terminality of E. Thus π₁ is invertible. Its right inverse Δ is its inverse, so π₂=π₂Δπ₁=π₁ in the quotient. |
| §5, interpretations | Agreement over all interpretations is substitution-closed. | For σ and any I, I∘F_σ is among the quantified interpretations. Hence agreement of f,g gives agreement of their substituted images. The quantifier over all object assignments is essential. |
| §6, mix parameter | (π₁∨1)d(1∧ι₂) defines m independently of B. | Checked against DP (dm), p.234 and PresentationSymmetricFold.lean. The displayed codomain is A∨C; no arbitrary parameter affects the occurrence relation. |
| §6, fold symmetry | h=[1,1]m:A∧A→A satisfies h swap=h. | Symmetry of mix followed by the symmetric copair [1,1]. Source correspondence is fold_manuscript/fold_symmetric. |
| §6, first fold step | K with B=⊥ gives jh≡jπ₂. | This is ContextualCollapse.second_block in Collapse.lean, using the source equality for the first injected component and empty-relation equalities. Coherence is invoked in B. |
| §6, injection collapse | jπ₁≡jπ₂ implies j≡ι₂!. | Precompose the previous equation with swap and use h swap=h, then transitivity. Precompose with 〈1,0〉; the two composites become j and j0. The latter equals ι₂! by source coherence. |
| §6, second fold step | B=⊤ gives h≡π₁. | Coproduct equations first make A∨⊤ terminal. Coproduct symmetry gives ι₂^{⊤,A}≡ι₁^{⊤,A}!_A. Substitute in the mix expression; the first-injection equation reduces it to ι₁π₁, and [1,1] gives π₁. Fold symmetry yields π₂≡π₁. |
| §6, formal endpoints | Both maximality routes and the model corollary concern the generated presentation. | Read PresentationMaximality, PresentationShortMaximality, PresentationFragmentMaximality, Substitution, Collapse, SemanticModelCorollary, and the fold correspondence. This is source inspection against the existing claim map, not a new kernel run. |
| §6, registered family | Five selected declarations. | comparator.json selects both maximality routes, the dichotomy, nonzero variable identity, and no ⊤→⊥. The broader full-paper claims remain separate from this selection. |
| Appendix A.1, γ | The fibre squares specify a unique γ. | Each element of D has exactly one pair (r,t), and γ(r,t)=(o_M(r),o_{o_M(r)}(t)). The square gives this value on each injection. Empty blocks introduce no elements or extra choices. |
| Appendix A.1, projection square | p_Cγ=o_Mp_D. | Both values are o_M(r). Distinct outer positions r,r′ remain disjoint blocks even when their labels agree. |
| Appendix A.1, χ | Occ(M[Φ₀])≅D with label γχ. | Apply the occurrence-substitution induction to the inserted tagged patterns. Each position has unique outer and inner coordinates; the inserted local label is the displayed pair. |
| Appendix A.2, encoders | θ_D(r,t)=s_{r−1}+t and θ_C(i,s)=t_{i−1}+s are bijections. | Prefix intervals of positive-length blocks are disjoint and cover the ordinal. Zero-length intervals contain no elements. The unique containing interval supplies the inverse. |
| Appendix A.2, δ | δ=θ_Cγθ_D⁻¹ and the coordinate formula. | Substitute (r,t) into the composite. The block locator is the unique r with s_{r−1}<x≤s_r. Replacing t by x−s_{r−1} yields DP p.46. |
| Appendix A.2, skeleton | Skeleton plus profile determines a pattern. | The skeleton retains every constant and connective. Its variable positions are fixed; decorate each with the profile's label. V13 explicitly names the skeleton of M[Φ₀]. |
| Appendix A.2 example | δ=(4,3,4,1,2,4,3,4); δ(2)=3. | Outer profile (2,1,2) selects lengths (3,2,3). The two copies of N₂ each give (4,3,4), with N₁ giving (1,2). Position 2 maps (1,2)↦(2,1)↦3. |
| Appendix A.3, renaming | M[Φ₀][ρ]=M[σ] even when ρ repeats values. | At p_i both sides are σ(p_i); all constant and connective clauses agree. Structural induction proves the formula equality. Renaming changes labels, not position tags. |
| Appendix A.3, contextual endpoints | Positive and negative cases have the stated substituted types. | Positive p gives A∧⊥→A∨⊤. Negative ¬p with p↦¬A gives ¬¬A endpoints; the already displayed double-negation square transports them. V13 makes the first case explicitly conditional. |
| Appendix B | Three defining-equation diagrams commute. | Follow each path using the typed primitives listed above. The zero diagram is the five-arrow definition; the square uses arbitrary parallel f,g. No assumption f=g appears. |
| Appendix C, p.260 | The recursive comparison is r′<r. | Read the source rank definition and displayed reduction. The selected premise lowers the relevant one-sided rank while the other is unchanged and the cut formula stays fixed. |
| Appendix C, p.262 | “Right rank 1”, not “rank 1”. | The new ∨L principal formula has right rank 1. The opposite left rank remains positive. Total rank is their sum, at least 2. The analogous p.261 sentence confirms the intended comparison. |

## Consecutive line coverage

The ranges below partition all 929 v12 lines, including blank lines. Every
range was read; the result records its mathematical or editorial disposition.
“Retain” means no defect was established by this pass, not machine certification
of English. Details are in the ledgers above and the source comparison report.

| V12 lines | Check and disposition |
| --- | --- |
| 1–23 | Preamble, macros, hyperlink destinations and title metadata. Increment release metadata to v13; retain mathematical macros. |
| 24–40 | Abstract: nonempty P, congruence closure, contextual reduction and formalization scope. Retain. |
| 41–44 | MSC classification unchanged. |
| 45–48 | Keywords have specific mathematical referents. Retain. |
| 49–50 | Introduction heading. |
| 51–59 | Conjecture locator and maximality claim checked against DP p.322 and the proof. Retain. |
| 60–69 | Differing-edge reduction, relative-maximality context and q/e references checked. Retain. |
| 70–75 | Cartesian argument checked at §5. Add CCC antecedent and explain its inapplicability (L1). |
| 76–85 | Lattice/dicartesian and split-relation comparisons checked. Add zero-identity distributive antecedents (L2); restore negation-free hypothesis of Lemma 6 (L3). |
| 86–98 | Check precise LS category class and FP negation triangle. Add proof-net comparison (L4); state FP soundness/completeness as the quantified inequality assertion (L5). |
| 99–111 | Coordinate reference, section pointers, errata scope and edition convention checked. Retain. |
| 112–113 | Category heading and label. |
| 114–122 | Formula grammar, nonempty P and presented equality declared before use. Retain. |
| 123–140 | All product/coproduct, pairing/copairing, unit, identity and composition types checked. Retain. |
| 141–153 | Distributor and first-injection equation: endpoints match DP p.234. Retain. |
| 154–178 | Contravariant negation, η/ε, five-arrow zero and arbitrary-parallel-arrow zero law checked. Retain. |
| 179–183 | Remove the redundant Remark label and shorten the Appendix B announcement (P1). |
| 184–191 | Zero witness independence and two absorption equations derived. Retain. |
| 192–201 | Parallel arrows, full proof congruence and whole-arrow uniform substitution; check (su). Retain. |
| 202–206 | Total congruence, thinness and maximality definitions agree with theorem. Retain. |
| 207–214 | Theorem 2.1 checked as in numbered-statement ledger. Retain statement byte for byte. |
| 215–216 | Proof-location pointer correct. |
| 217–218 | Occurrences section and label. |
| 219–223 | Positions distinguished from labels. Retain. |
| 224–242 | Recursive Occ definition, labels and ordinal bijection include empty cases. Retain. |
| 243–265 | Rel_fin, G and generator relations checked; bijective Gd does not assert invertible d. Retain. |
| 266–271 | Boolean Coherence statement matches cited source. Retain byte for byte. |
| 272–275 | Distinct projection relations establish nonthinness. Retain. |
| 276–282 | Replace abbreviated Joyal description by exact initial-object/exponential condition; spell out p∈P (P2). |
| 283–291 | Signed literals, NNF and comparison directions checked. Retain. |
| 292–305 | Generator induction for signed-label preservation checked. Retain. |
| 306–326 | Substitution occurrence bijection checked in every grammar case. Retain. |
| 327–347 | Block square and image criterion checked pointwise; Eσ not claimed finite. Retain. |
| 348–359 | Arrow substitution functor, empty Q and preservation of all defining equations checked. Retain. |
| 360–361 | Isolation heading. |
| 362–374 | K_A and its zero alternative have identical endpoints and empty relation. Retain. |
| 375–389 | Lemma 4.1 including permitted interchange and signed literal checked. Retain statement. |
| 390–398 | Conjugation by NNF comparisons and restoration of original endpoints checked. Retain. |
| 399–410 | Selected edge and empty-relation arrows b_V,t_V checked. Retain. |
| 411–419 | All left/right product/coproduct selector cases checked. Retain. |
| 420–426 | Dual coselector cases and empty unselected summands checked. Retain. |
| 427–432 | Composite relation calculation and original coherence yield both equations. Retain. |
| 433–438 | Proposition 4.2 hypotheses/conclusion checked. Retain statement. |
| 439–447 | Positive substitution includes actual source/target operations. Retain. |
| 448–465 | Negative substitution, inverse directions and zero absorption checked. Retain. |
| 466–467 | Collapse heading. |
| 468–470 | Endpoint-isomorphism citation p.294 checked. |
| 471–483 | Lemma 5.1 exact q/e maps and types checked. Retain statement. |
| 484–490 | Unique one-occurrence bijection identifies q_p. Retain. |
| 491–500 | Two permutations, product symmetry and e_p checked; Lemma 7 is used with its stated scope. Retain. |
| 501–505 | Substitution preserves isomorphism equations. Retain. |
| 506–511 | Lemma 5.2 requires only proof congruence plus all contexts. Retain statement. |
| 512–532 | Quotient structure, q≡s!, inverse equations and terminality of E derived. Retain. |
| 533–552 | Inverse projection, r e=π₁, diagonal inverse and arbitrary-pair collapse derived. Retain. |
| 553–559 | Main theorem follows from Proposition 4.2 and Lemma 5.2. Retain. |
| 560–566 | Interpretation objects, functor and preserved structure specified. Retain. |
| 567–574 | Model corollary quantified over every interpretation. Retain statement. |
| 575–586 | Universal agreement, substitution closure and target-native pairing checked. Retain. |
| 587–588 | Formalization heading. |
| 589–596 | Typed syntax/Derives/quotient account checked against source map. No missing Lean typing. |
| 597–618 | Relative theorem inputs, mix formula and symmetry checked. Replace final compressed collapse sentence by intermediate equations (P3). |
| 619–624 | Actual-presentation instantiation checked in the source endpoint; no new kernel replay claimed. |
| 625–633 | Short route, models and appendix correspondences checked against existing ledger and relevant source endpoints. |
| 634–638 | Five declaration descriptions match comparator.json; do not equate selection with entire manuscript. |
| 639–641 | Appendix transition and label. |
| 642–649 | Generalized composition described as pattern substitution plus profile; p.46 checked. |
| 650–651 | Profiles subsection. |
| 652–657 | Finite ordinals, patterns and profiles defined before use; zero allowed. |
| 658–671 | Distinct local placeholders, disjoint Q_i, empty sets and nonsurjective profiles checked. |
| 672–701 | D,C, injections, fibre square and unique γ checked pointwise. Retain. |
| 702–715 | Projection square and disjoint repeated blocks checked. Retain. |
| 716–732 | Tagged patterns, Φ₀ and occurrence-label square checked. Delete unnecessary emphatic wording (P4). |
| 733–734 | Ordinal subsection. |
| 735–768 | Prefix encoders, inverse block locator, δ square and coordinate formula checked including zero blocks. Retain. |
| 769–782 | DP coordinate identification checked; specify the skeleton of M[Φ₀] (P5). |
| 783–803 | Every entry of the worked profile and the position-2 calculation checked. Retain. |
| 804–805 | Shared-variable subsection. |
| 806–827 | Noninjective renaming square checked by grammar induction. Retain the precise term structural induction. |
| 828–837 | Make the first contextual branch conditional on isolated literal p; retain the negative branch (P6). |
| 838–840 | Appendix B heading. |
| 841–856 | First-injection triangle and explanatory types checked. Retain unchanged. |
| 857–877 | Five-arrow zero diagram and all intermediate objects checked. Retain unchanged. |
| 878–889 | Zero-law square with arbitrary f,g checked. Retain unchanged. |
| 890–892 | Appendix C page break and heading. |
| 893–898 | Rank is sum of positive left/right ranks: source p.249 checked. |
| 899–905 | p.260 inequality reversal checked against reduction and rank definition. Retain unchanged. |
| 906–913 | p.262 right-rank/total-rank distinction checked against pp.249,261–262. Retain unchanged. |
| 914–920 | Authorized AI disclosure and author responsibility preserved verbatim. |
| 921–929 | Bibliography setup changed to v13 databases; all existing entries retained and two added. Final compilation resolves all citations. |

## Edits, final reading and limits

The eleven mathematical/prose changes are recorded with exact old and new text
in [editorial-decisions.json](../../provenance/manuscript-v13-review-20261031/editorial-decisions.json).
The [source diff](../../provenance/manuscript-v13-review-20261031/v12-to-v13.diff)
also includes version, date/metadata and bibliography-file changes. V13 was then
read continuously from beginning to end. No section rearrangement was necessary.

The exact theorem statements, twelve numbered displays, ten TikZ diagrams,
thirty labels, Appendices B and C, AI disclosure and supplied Palomar BibTeX are
preserved from v12. The fold expansion adds unnumbered intermediate equations;
it does not add a new formal theorem. Rendering and archive validation are
recorded in [the v13 report](../MANUSCRIPT_V13_REPORT.md).

This pass checks the mathematical manuscript and relevant Lean endpoints. It
does not replay the Lean kernel, repeat independent verification, or prove
originality by absence from search results. No formal proof defect was found.
The previous source-closure and registration evidence remains evidence for its
recorded commits. Windows Downloads is unavailable here; reports are retained
in the repository and have not been delivered there by this session.
