# Complete manuscript claim map

This is the active exact correspondence for all mathematical content of v7,
preserved in v8 with a formalization-status/date/citation refresh and in v9 with
the AI-disclosure/registry-citation publication update. V10, dated October 31,
2026, contains the terminology revision with the same mathematical definitions,
statements, proofs, labels and diagrams. The original v9 release is preserved.
V11 incorporates those corrections and the supplied Palomar BibTeX; empty
qualifiers and progress narration are revised, and terminology is explained.
All mathematical statements, displayed equations, ten diagrams and labels match
v10. V12 adds explicit notation and equations for these same claims after a full prose
and source review. V13 adds the second complete review, corrects the scope of
the introductory Lemma 6 citation, adds literature comparisons and spells out
the existing symmetric-fold deduction. V14, dated November 1, 2026, uses the
hostile and mathematical-writing plugins for the complete preprint. It gives
explicit arrow/functor types, uses literal and occurrence map, follows the
source's dissociativity terminology and displays the calculations through v_A
and w_A. The correspondences below apply also to v15–v25; see MANUSCRIPT_V14_REPORT.md
and its two review reports. Literal signs, theorem hypotheses and conclusions,
all numbered displays, diagrams, labels, Lean theorems and registered inputs
are preserved. The literal synonym and lemma captions change; no new Lean
verification is claimed. Lean identifiers containing Profile or ContextualCollapse
remain unchanged; they name the same functions and deductions.
Earlier
coverage/statement maps and reports remain as dated checkpoints. “Complete” here
means local pinned Lean proof/source closure; it does not mean independent replay,
Comparator, official/service verification, public release or publication.

V15 adds Appendix D explaining the existing registered declarations. Its
statements, term/quotient relations, assumptions and substitution square are
mapped below. All preceding v14 mathematical text and diagrams are preserved;
no Lean source or registered input changes. See MANUSCRIPT_V15_REPORT.md.

## Reverse content audit and v16 incorporation (1 November 2026)

The [Lean-to-paper audit](FORMALIZATION_TO_MANUSCRIPT_AUDIT_2026-11-01.md)
inventoried all production modules, including 95 outside the selected five
entry points' import closure, and proposed seven additions. The author accepted
them and requested a guide for mathematicians new to proof assistants. V16
incorporates all seven and supplies the worked declaration/proof correspondence.
The typed additions are mapped below. Source-reading depth remains as recorded
in the reverse audit; this revision does not claim a new all-proof-body audit,
Lean build or kernel replay. The full library is not asserted to be printed
in the paper. See [v16 report](MANUSCRIPT_V16_REPORT.md).

## V17 terminology and layout (1 November 2026)

V17 makes eight author-requested prose/layout edits: the u_A path occupies
one line; Appendix E is titled “Inverses of q_A and e_A”; the other uses of
“structural” name their generator or equation families, or say “induction on
the formula”. Cross-reference keys and Lean names remain fixed. The substitution
proof refers to tagged relations, accommodating diagonals and projections.
The seven statement bodies, twelve numbered displays, thirteen diagrams,
34 labels and all 49 declaration URLs are unchanged. The correspondences and
page anchors below remain valid. No proof source, selected type or frozen
input changes. See [v17 report](MANUSCRIPT_V17_REPORT.md).

The author confirmed retention of Appendix A and its main-text connections.
Section 3 refers to A.1–A.2; Proposition 4.2 points to A.3. The finite-ordinal
calculation supplies the exact correspondence with the source's substitution
operation, in addition to the block substitution used in the maximality proof.
This confirmation does not reduce the full-paper mathematical contract.

## V18 abstract (1 November 2026)

V18 replaces only the abstract and version/bibliography suffixes. The opening
orients readers to equations as proof identifications. The result retains
freeness, nonempty variables, distinct arrows with the same endpoints, closure
under every arrow operation and uniform substitution, and totality on parallel
arrows. The proof outline refers to coherence, occurrence selection, substitution
and the q/e isomorphisms without formula-specific notation. The model
consequence retains quantification over every variable interpretation; the
formalization and occurrence/ordinal correspondence are reported precisely.
These are summaries of the existing rows below, not additional claims.
All main-text and appendix correspondences, page anchors and source links remain.
See [v18 report](MANUSCRIPT_V18_REPORT.md).

## V19 citation, qualifiers and comparison display (1 November 2026)

The author supplied the version-2 BibTeX and requested a qualifier review and
one-line D.5 comparison definitions. V19 incorporates all three. The source
note and 49 declaration links now refer to registered version 2 at
5dbee39bea09539bd130f729e82636419f71f920. PrimitiveCongruence moved from
line 13 to 14, Closed from 28 to 31; all other linked line numbers are unchanged.
The active link records are in the v19 provenance. The exact v2 BibTeX, plain
and TeX abstracts, comments and submission fields are synchronized.

Eleven prose edits remove redundant qualifiers or identify the constructions
meant, including the two “particular” occurrences. Qualifications expressing
quantifiers, hypotheses, signs, coordinate origins, naturality or universal
properties remain. The c-arrow definition/type line breaks change without
changing mathematical tokens. All typed correspondences below remain; the
abstract, seven statement bodies, numbered equations, diagrams, labels, both
proof routes and Appendix A content/references are preserved. See
[v19 report](MANUSCRIPT_V19_REPORT.md).

## V20 descriptive collapse statement (1 November 2026)

The abstract and introduction state collapse after any nonderivable parallel
arrow equation, with arrow-operation and uniform-substitution closure. Section 2
defines the quotient and states thinness iff totality before Theorem 2.1.
The theorem now concludes that the quotient is a preorder. This is equivalent
to the preceding totality conclusion, by the existing
Congruence.quotient_thin_iff_total (CongruenceQuotient.lean:93).
The following paragraph explains the name maximality and its universal
quantifier. The theorem proof, model proof and D.4 translation are consistent.
No new proof or theorem obligation is introduced. See
[v20 report](MANUSCRIPT_V20_REPORT.md).

## V21 abstract and introduction (2 November 2026)

The abstract now states that Došen and Petrić conjectured the category is not
maximal, then gives the disproof by collapse. The general opening and redundant
elementary preorder paraphrases are omitted as requested. The §1 citation to
§14.2, printed p.322, remains. The descriptive universal collapse statement and
all mathematical hypotheses are unchanged. No correspondence row changes.
See [v21 report](MANUSCRIPT_V21_REPORT.md).

## V22 introduction of the formalization (2 November 2026)

The abstract introduces the Lean development as a formalization of the written
proofs and their dependencies. It retains Boolean Coherence and the substitution
correspondence within that scope. The body, all claims and declaration mappings
are unchanged. See [v22 report](MANUSCRIPT_V22_REPORT.md).

## V23 review implementation (2 November 2026)

The statements and declaration mappings are unchanged. Appendix C now identifies
cut elimination as an input to Boolean Coherence and spells out both strict
rank inequalities, including L+1<L+R for the fresh cut. The introductory proof
outline includes uniform substitution and double-negation transport. The
coherence appendix attributes the union-zero equation to the zero law together
with the product, coproduct and dissociativity equations, without faithfulness.
See [v23 report](MANUSCRIPT_V23_REPORT.md) and the retained v22 review.

## V24 review implementation (3 November 2026)

All theorem and declaration mappings remain. Appendix D.4 explicitly retains
substitution closure when applying the dichotomy. D.5 explains the weakening
step and describes the common factorization directly; the normal-form equality
is about the original morphism. The footnote identifies the normalized endpoint
hom-sets, and the faithfulness transfer points to the occurrence-preserving
equivalence in Section 3. Morphism terminology changes no formal statement.
See [v24 report](MANUSCRIPT_V24_REPORT.md) and
[implementation review](reviews/V24_IMPLEMENTATION_REVIEW_2026-11-03.md).

## V25 fixed release links (2 November 2026)

The release is `dosen-petric-v25-palomar-v3`. All 56 source link occurrences retain
their paths, line anchors and visible declaration names, replacing only the
Git ref. Metadata refers to this same release. Mathematical statements,
proofs, diagrams, labels, abstract and definitions are unchanged from v24.
The formalization bibliography identifies the release, and the registry
bibliography is prepared for v3. This is a candidate until that actual record
is confirmed at the tagged commit. No floating latest URL is used.
See [v25 report](MANUSCRIPT_V25_REPORT.md) and
[Codex handoff](PALOMAR_V25_CODEX_HANDOFF.md).

## Three milestones and full-paper endpoint

| Milestone | Actual result | Status |
| --- | --- | --- |
| I: intended nonthin source interface | Presentation.coherence/interpretation/interpretation_signedLabel; nonthin; empty_hom | Every coherence, structure, normalization and label input is instantiated in the actual equation-generated category. |
| II: general maximality argument | relative_maximality and ContextualCollapse.total | General theorem under explicit typed inputs, retained as such. |
| III: actual-presentation maximality | Presentation.maximality/congruence_dichotomy/raw_maximality; short_maximality | Actual full congruence and substitution bridges proved; both proof routes instantiated. |
| Complete paper | Rows below, including model and all three appendices | Complete mathematical scope, with exact local verification and committed-source evidence in provenance/wsl-appendix-a/. |

## Main text

| Manuscript anchor / mathematical assertion | Exact declaration correspondence | Scope |
| --- | --- | --- |
| §2 formulas and actual generated category | Formula; Presentation.Term/Equation/Derives/termSetoid/Hom/category | Complete primitive grammar and published generating equations; quotient equality is generated equality. |
| §2 products, coproducts, units, dissociativity | Presentation.operations, conjDiagonal/disjDiagonal, source product, coproduct, unit, associativity, symmetry and dissociativity laws | Native beta/eta and uniqueness equations, all endpoints explicit. |
| Eq. (1), first injection | Presentation.Laws.dist_inl; ManuscriptDiagrams.first_triangle | Exact actual source identity. |
| §2 contravariant negation and natural comparisons | Presentation.negate and its contravariant functor; PresentationNegationNaturality.lean; doubleNegationNaturalIso | Derived raw representative, actual involution/DN/De Morgan naturality; Reduced coordinate/recovery bridge proved. |
| Eq. (2), zero identity | Presentation.zeroConstruction/zeroConstruction_eq/zeroConstruction_structural; ManuscriptDiagrams.zero_diagram/zero_primitive | Exact five-arrow path and equality to primitive zero. |
| Eq. (3), zero law | Presentation.Laws.zero_law; zeroIdentity; ManuscriptDiagrams.zero_square | All parallel existing arrows; no missing hom-set is inhabited. |
| §2 witnessed zeros, independence and absorption | ZeroIdentity.zeroOf/zeroOf_independent/commute/precompose/postcompose | Existing-arrow witness required; no HasZeroMorphisms. |
| §2 proof/substitution congruence | Presentation.ProofCongruence/RawProofCongruence; raw_quotient_rel/quotient_raw_rel; fragment/fragment_closed and closure transfers | Every primitive arrow operation, derived pairing/copairing/negation and uniform whole-arrow substitution. |
| Theorem 2.1 | Presentation.maximality/congruence_dichotomy/raw_maximality; Presentation.short_maximality; Congruence.quotient_thin_iff_total (CongruenceQuotient.lean:93) | Every substitution congruence identifying a distinct parallel pair has a preorder quotient; equivalent to totality and the equality/total dichotomy. |
| §3 tagged occurrence definitions and labels | Formula.Occ/label; repeated_positions_distinct | Repeated equal labels retain distinct Sum tags; constants empty, negation preserves positions. |
| §3 finite left-to-right bijection | Formula.occurrenceCount/occurrenceIndex/occurrenceAt; occurrenceAt_index/occurrenceIndex_at; FiniteBlocks.oneBased/zeroBased and inverse laws | Explicit finite ordinal coordinates, including cardinality zero. |
| §3 functor G into finite sets/relations | FiniteSet.relationCategory; Presentation.occurrenceFiniteSet/finiteOccurrenceFunctor | Every source object has explicit finite coordinate bijections; identities/composition proved. |
| §3 G images of projections/injections/pair/copair/dissociativity/zero | Presentation.occurrence_fst/snd/inl/inr/pair/copair/dist/zero; original OccurrenceLaws | Exact tagged relations, rebracketing graph and empty zeros. |
| Theorem 3.1 Boolean Coherence | Gentzen.positive_coherence; Reduced.faithful/boolean_coherence; Presentation.coherence/finiteOccurrenceFunctor_faithful | Actual source coherence, not a supplied interface field. |
| §3 nonthinness and nonzero literal identity | Presentation.nonthin; literal_identity_ne_zero/identity_ne_zero/identity_ne_primitive_zero | Distinct repeated-tag projections, both signed literals, primitive/constructed zero. |
| §3 at most one global point and failure of cartesian closure | top_hom_subsingleton/fromTop_unique; ExponentialData.toGlobalPoint/fromGlobalPoint and both inverse laws; no_self_exponential/not_cartesian_closed | Exact printed p⇒p obstruction and hom/global-point bijection. |
| §3 NNF isomorphism and occurrence graph | Presentation.normalization; NegationNormalization comparisons; PresentationNormalizationTerms.lean | Actual forward/backward representatives, inverse equations and original-position transport. |
| §3 literal preservation and equivalence of presentations | Presentation.occurrence_literal/occurrence_signedLabel; Reduced reduction/inclusion functors and recovery equations | Both signs and constants, raw and quotient bridges; no target-category coherence. |
| Eq. (4), substitution occurrence bijection | Formula.expand/contract; contract_expand/expand_contract | Actual dependent blocks, all formulas/substitutions, independent variable universes. |
| Eq. (5), block square | Formula.InsertedOccurrences/blockLabel/block_square; contract_label/expand_label | Exact upper map (old tag,inner tag)↦(old variable,inner tag), and both projection routes. |
| §3 whole-arrow substitution functor and operations | Term.subst; Equation.subst/Derives.subst; Presentation.substitutionFunctor; substitute_negate/negate_subst_derives; full operation/zero laws | All 31 primitive families, raw and quotient, actual source/target formulas. |
| §3 complete arrow occurrence-block square | Term.substitution_coordinates; occurrence_substitute_coordinates/expanded; Relations.Fiber laws | Every edge retains old and inner coordinates; signed-label equality and empty/repeated blocks checked. |
| §3 substitution action laws | Formula.subst_identity/composition/ext; Term.subst_identity_heq/subst_composition_heq; Presentation.substitute_identity/composition/ext | Ordinary quotient equalities display both endpoint transports. |
| Context K_A and printed zero alternative | ContextualCollapse.K; Presentation.contextual_zero_alternative; ShortProof.context_zero_through_top | Exact three-arrow expression through bot/top equals witnessed contextual zero. |
| Lemma 4.1, selectors/coselectors | Isolation.selector/coselector and edge isolation; original_composite/original_witnesses; Presentation.occurrence_isolation | Actual original endpoints, signed literal, both equations and permitted interchange; normalized paths reattached explicitly. |
| Proposition 4.2, positive/negative branches | ContextualCollapse.all_contexts/context_retract; ManuscriptSubstitution.positive_all_contexts/negative_all_contexts | Uniform closure with actual source inputs and correct variance. |
| Proposition 4.2, fix-other-variable substitution and DN rectangle | ManuscriptSubstitution.replace/replace_at/replace_other/positive_single_context/negative_single_context; double_negation_square | Internally classical equality, no DecidableEq hypothesis. Actual neg neg A endpoints and source diagram identity. |
| Lemma 5.1 exact q_A/e_A | ShortProof.qTerm/qInverseTerm/eTerm/eInverseTerm; q_definition/e_definition and all four inverse equations; ten substitution laws | Both particular displayed arrows are actual isomorphisms for every formula, with constructed inverses. |
| Lemma 5.2 quotient structure retained | Congruence.homSetoid/QuotientHom/quotientCategory/quotientFunctor/quotientStructure/quotientZeroIdentity | Actual quotient category and all product/coproduct/unit equations, witnessed zeros and empty-hom preservation. |
| Lemma 5.2 terminal E and invertible projection | ShortProof.q_zero_form/q_terminal/terminal_id/terminal_hom/terminal_pair; r_i/i_r/e_r and projection_id/diagonal_u/projections/total | Exact q/e short collapse, not replaced by the alternative fold argument. |
| Quotient preorder iff congruence total | Congruence.quotient_thin_iff_total | Equality of quotient classes corresponds exactly to the original congruence relation. |
| Corollary 5.3 / full-source model semantics | PresentationSemantics.Model; evaluate_derives/evaluateHom/evaluationFunctor/canonicalInterpretation; Source.model | Every actual primitive/equation and model law instantiated in intended category; native target bicartesian/zero laws explicit. |
| Corollary 5.3 / full interpretations and uniform agreement | Interpretation.precompose/object_evaluation/raw_evaluation/hom_evaluation; Agreement.fragment_closed/congruence/closed/iff_valuations | Complete interpretation family; full closure proved through independent fragment dichotomy, never assumed for one kernel. |
| Corollary 5.3 conclusion | PresentationSemantics.model_corollary/model_corollary_interpretations | Nonempty source P chooses p; constant valuation and native pairing equate arbitrary target arrows. No surjectivity or arrow existence assumed. |
| §6 alternative fold/mix formulas and symmetry | Presentation.tensor_prodMap/fold_source_mix/fold_manuscript/mix_parameter_independent/fold_parameter_independent/fold_symmetric | Exact displayed copair(id,id);mix identification and projection-pair symmetry, original coherence only. |
| §6 expanded projection-equality deduction in v14 | ContextualCollapse.second_block/injected_projections/terminal_injection/terminal_retraction/terminal_hom/other_injection/fold_top/equal_projections/total | Existing source proves jh≡jπ₂, equality of injected projections, j≡ι₂!, terminal A∨top, h≡π₁, equal projections and arbitrary-pair collapse. These intermediate deductions are now printed; no new theorem or source change. |

## Appendix A: every construction, example and diagram

| Anchor | Exact declaration correspondence | Status |
| --- | --- | --- |
| Finite pattern occurrence maps and zero cardinalities | Formula.profile/profile_index; ProfileComposition.Data | Arbitrary outer and inner functions; no assumed injectivity/nonempty blocks. |
| D,C and injections a_r,b_i | Data.Domain/Codomain/a/b/a_injective/b_injective/a_disjoint/b_disjoint | Dependent Sigma blocks retain repeated outer positions and disjoint local placeholders. |
| Eq. (6), fibre square; unique gamma | Data.gamma/fibre_square/gamma_unique/gamma_fibre | Exact pointwise formula and uniqueness on every block. |
| Eq. (7), occurrence-map square | Data.profile_square | Both routes send (r,t) to outer(r). |
| Tagged inserted N_i and Phi_0 | PatternProfiles.tag/insertion/data/taggedBlock | Actual renamed patterns over C, not merely abstract cardinalities. |
| Actual chi bijection and Eq. (8) | taggedBlock_injective/surjective; chiInverse/chi; both inverse laws; unique_coordinates/occurrence_label_square | Every actual substituted occurrence has its unique old/local finite coordinates and the correct tagged label. |
| Prefix sums and consecutive numbering | FiniteBlocks.total/prefixSum/encode/decode/encode_value; encode_decode/decode_encode; total_concat/prefix_concat_left/right | Actual left-to-right order, arbitrary zero lengths; explicit source/target encodings. |
| Eq. (9), unique delta square | Data.delta/ordinal_square/delta_unique | Exact change of coordinates. |
| Eq. (10), one-based formula | Data.coordinate_equation/coordinate_oneBased/book_locator/book_formula; FiniteBlocks.oneBased/zeroBased/locator_bounds/locator_unique/zero_block_has_no_position | Exact unique nonempty containing block and local x−s_(r−1), including intervening empty blocks. |
| Actual finite-ordinal/book correspondence | Formula.substitution_count/substitution_index; PatternProfiles.composite_count/chiInverse_index/chiInverse_encoding/actual_ordinal_square/composite_profile | Block encoders agree with actual formula occurrence indices; no arbitrary finite bijection substituted for the printed order. |
| Skeleton/occurrence-map equivalence and generalized composite | Formula.skeleton/decorate/skeletonProfile/fromSkeletonProfile/skeleton_profile_reconstruction/skeleton_profile_unique/skeleton_rename; generalized_composite_skeleton/flattened_profile/generalized_composite_reconstruction | Restores complete syntax, not only variable labels; identifies the actual generalized composite with skeleton plus delta. |
| Worked occurrence maps, sizes and eight outputs | PatternProfiles.Example.outer_profile/first_profile/second_profile/source_sizes/eight_positions | Actual M=q∧(p∨q), N1=a∧b, N2=d∧(c∨d); [4,3,4,1,2,4,3,4]. |
| Worked position 2 | Example.source_position_two/gamma_position_two/target_encoding_three/delta_two | Source pair (1,2), target pair (2,1), theta_C=3 and delta(2)=3 in one-based notation. |
| Eq. (11), shared-variable renaming | Formula.rename_substitution/renameOcc_injective/rename_label/rename_index_value/profile_renaming; PatternProfiles.renaming_square; Example.noninjective_renaming | Arbitrary common variable universe and noninjective rho; labels may coincide while positions remain distinct. |
| Appendix A final positive/negative specializations | ManuscriptSubstitution.positive_context/negative_context; four block maps, exhaustiveness/contract laws; positive/negative single_context/all_contexts; double_negation_square | Both endpoints have one copy of Occ(A); exact A or neg neg A context before the actual retraction. |

## Appendices B and C and proof dependencies

| Anchor | Actual declarations / retained evidence | Status |
| --- | --- | --- |
| Appendix B triangle | ManuscriptDiagrams.firstUpper/firstRight/firstDiagonal/first_triangle | All paths typed, actual source equation. |
| Appendix B five-arrow zero | ManuscriptDiagrams.zeroStart/zeroEta/zeroDistributor/zeroEpsilon/zeroEnd/zeroPath; zero_diagram/zero_primitive | Exact printed path and its equality to primitive zero. |
| Appendix B zero square | ManuscriptDiagrams.zero_square; zeroIdentity.law | Arbitrary parallel existing f/g, with correct arrow order. |
| Appendix C p.260 | BlockedLeftDisj.gamma_equation and original-child gamma rank inequalities; GENTZEN_LEFT_GAMMA_DISJ_REPORT and subsequent all-blocked records | Both original recursive children have strict original-rank descent; actual source equation proved. |
| Appendix C p.262 | BlockedDisjFirst.source_equation; fresh_principal_rank/fresh_total_rank/fresh_total_rank_ge_two; blockedL_disjunctionFirst_rank_step | Fresh right rank one and total h.rho.right+1≥2; fresh_clean_and_rank proves strict descent from the original cut since its contracted right rank exceeds one. The opposite premise is unchanged; full Clean and exact original source are proved. |
| Cut-elimination published dependency | Reducibility/Blocked-w/simultaneous atomized blocked cleaning; all twelve logical binary cases and all fourteen blocked source/rank steps; cut_elimination/atomized_cut_elimination | Constructor/tag dispatch, original selected-rank and strong degree induction instantiated; no assumed handlers remain. |
| Positive/Boolean coherence published dependency | G.mix_normal_form, actual pure/normal positive coherence and represented normal retracts, Gentzen.positive_coherence, Reduced.faithful/boolean_coherence, Presentation.coherence | Finite unions require existing-arrow witnesses; one-sided normalization recovery laws are proved; full intended source bridge instantiated. |
| Full source/negation/normalization bridge | Reduced quotient reduction/inclusion, normalization natural isomorphism, recovery and derived dual/negation equations; source congruence and closure correspondence | Actual intended categories and coordinate transports; both literal signs and empty hom-sets preserved. |

All declaration sources are below 10,000 physical lines and use the pinned core
Lean toolchain. Exact public checks, negative controls and transitive axiom/source
closure are recorded in the final evidence. No mathematical claim in the paper's
current scope remains assigned to an unproved field or deferred implementation
target. Historical reports are not independent verification of this final scope.

## Appendix D: registered statements and proof correspondence (v25)

All names below have prefix DosenPetric unless stated otherwise. These are
existing proofs retained in both immutable registered sources, not new results.
V24 preserves v19's hyperlinks targeting version 2, 5dbee39bea09539bd130f729e82636419f71f920,
matching the author's newly supplied bibliography. Exact paths, declaration
lines and hashes for all 49 linked names are in the v19 linked-declarations
record. The preceding v16–v18 sources and version-1 link records remain preserved.

| Manuscript anchor | Declaration | Exact scope |
| --- | --- | --- |
| D.1 terms and generated equality | Presentation.Term/Equation/Derives; termSetoid/Hom/ofTerm; sound; Palomar.PrimitiveCongruence.raw_distinct_iff | Quotient by the defining equations, equivalence, composition and both binary operations; [f]=[g] iff Derives f g. |
| D.1 primitive zero | Presentation.zeroConstruction_eq | The class of Term.zero A equals the manuscript's zero endomorphism. |
| D.1 substitution square | Presentation.Term.subst; Derives.subst; substitute; substitutionFunctor | Arbitrary σ:P→Formula Q; the source and target of each substituted term change. The quotient square commutes by the definition of substitute. |
| D.1 relation and properties | Palomar.PrimitiveCongruence; Palomar.PrimitiveCongruence.Closed/Total | Equivalence on parallel terms, containing Equation and preserved by comp/tensor; Closed uses self-substitution; Total quantifies over existing terms. |
| D.3 maximality | Palomar.maximality | P nonempty; R primitive, Closed; R f g and not Derives f g imply Total. Symmetric-fold route via fragment_maximality. |
| D.3 short_maximality | Palomar.short_maximality | Same hypotheses/conclusion; literal isolation, all_contexts and ShortProof.total give the q_A/e_A route. |
| D.3 congruence_dichotomy | Palomar.congruence_dichotomy; Palomar.PrimitiveCongruence.of_derives | P nonempty and Closed; R=Derives on all parallel terms or Total; generating induction proves Derives⊆R. |
| D.3 identity_ne_zero | Palomar.identity_ne_zero; Presentation.identity_ne_primitive_zero | Given p:P, not Derives (id p) (zero p); diagonal versus empty occurrence relation. |
| D.3 no_top_to_bot | Palomar.no_top_to_bot; Presentation.Truth; Term.preserves_truth; empty_hom | Every P, including empty; no Term top bot. The all-true variable valuation is preserved by every term constructor. |
| D.4 term-to-arrow relation | Palomar.PrimitiveCongruence.quotientRel/quotientRel_ofTerm/fragment/fragment_closed | Derives⊆R proves representative independence; comp/tensor give pairing/copairing; Closed descends through the quotient. |
| D.4 negation after dichotomy | Presentation.fragment_dichotomy; Presentation.ProofCongruence.of_closed_fragment; Palomar.PrimitiveCongruence.full/full_closed/full_raw_rel/negate_admissible | Equality and totality each preserve negation. No preservation of negation is assumed to obtain fragment maximality. |
| D.4 converse and totality | Palomar.PrimitiveCongruence.ofFull/ofFull_closed/ofFull_full_rel/full_ofFull_rel/full_total_iff/ofFull_total_iff | Pull back a substitution congruence on arrows to terms, with exact relations and totality; distinct representatives invoke either selected maximality proof. |
| D.4 additional results | Presentation.coherence; PresentationSemantics.model_corollary | Theorem 3.1 and Corollary 5.3; the model corollary is a further result, not asserted to be a dependency of all five selections. |
| D.4 expanded symmetric calculations | ContextualCollapse.second_block/fold_top/terminal_retraction; Presentation.fold_manuscript/fold_symmetric | The Section 6 fold is the abstract fold under the intended presentation; the injected second projection, first projection and terminal retraction are existing theorems. |


## V16 additions from the formal proof

All declaration names below have prefix DosenPetric. Slash-separated names
share the namespace of the first name. These rows distinguish
native statements, transfer through the proved equivalence and explanatory
mathematical derivations. The manuscript contains the typed statements and
proofs; these rows identify their source locations.

| Item / manuscript anchor | Declaration correspondence | Exact scope |
| --- | --- | --- |
| R1, Section 3 pp.5–6 | Presentation.occurrence_substitute_expanded; Relations.Fiber.lift_composition | Relation on dependent old/inner blocks; equality of labelled inner positions in E_sigma; full square and composition, including repeated and empty blocks. |
| R2, E.1 p.20 | Presentation.ShortProof.qInverseTerm/q_qInverse/qInverse_q | Explicit inverse of the particular q_A, both equations, all formulas including empty occurrence sets. |
| R2, E.2 p.21 | Presentation.ShortProof.sourceConjTerm/sectionTerm/eInverseTerm/e_eInverse/eInverse_e | Explicit typed five-arrow c path and section; copair with zero witnessed by Delta_A pi_1; both e inverse equations. |
| R3, Section 6 p.10 | Reduced.union_assoc/union_comm/union_idem/union_pre/union_post/union_id_zero; Reduced.finiteUnion.eq_of_members; Reduced.reduceHom/recoverHom | Named Reduced algebra; transfer to B(P) through inverse hom maps. Printed definition and faithfulness prove the native expression's laws. No Presentation.union name is asserted. Empty union and bottom require an inhabited hom. |
| R4, Section 3 p.6 | Formula.subst_identity/subst_composition/subst_ext; Presentation.substitute_identity/substitute_composition/substitute_ext | Independent P,Q,R, pointwise composed substitution and both endpoint identifications. |
| R5, Section 4 p.7 | ContextualCollapse.context_retract | i:A→B,r:B→A,ri=1_A; K_B modulo the same congruence implies K_A. No two-sided inverse is needed. |
| R6, Section 3 pp.4–5 | Presentation.occurrence_signedLabel; Reduced.Term.dual_relation; Presentation.occurrence_negate | Arbitrary formula sign preservation and exact converse relation at original occurrence positions. |
| R7, D.5 pp.18–19 | Reduced.union_pre/union_post/union_comm/union_assoc/union_idem/union_id_zero | Source-equation derivations, used before faithfulness; separate from Section 6's consequence of coherence. |
| R7, D.5 p.19 and E.3 pp.21–22 | Reduced.Gentzen.DistributiveEpi.section_comparison; Reduced.Gentzen.DistributiveMono.comparison_retraction; Reduced.Gentzen.Rules.sourceConj; Reduced.Term.mixedDisj | Explicit s,t terms; c-wedge s=id and t c-vee=id by the product, coproduct, associativity, symmetry, dissociativity and mix equations and component calculations. No reliance on the quotient dual functor. |
| R7, D.5 p.19 | Reduced.Gentzen.dnf_expansion/cnf_expansion | i:A→D_A,r:D_A→A,ri=id and the corresponding C_A retract. Not distributivity isomorphisms. |
| R7, D.5 p.19 | Reduced.Gentzen.G.mix_normal_form; Reduced.Gentzen.HasPureNormalForm.faithful; Reduced.Gentzen.pure_positive_coherence/represented_coherence/positive_coherence | Positive means no eta/epsilon constructors; pure paths are projection/injection composites; finite unions and one-sided recovery give equality. |
| R7, D.5 pp.19–20 | Reduced.commonAtomicFactor/faithful_of_positive_coherence; Reduced.boolean_coherence; Presentation.coherence | Common A',B',u,v,f_0,g_0 and injective occurrence embeddings with direct-image relation equations; positive equality→Reduced equality→original source equality. |
| D.2 pp.16–17, reading a declaration | Palomar.maximality; Palomar.PrimitiveCongruence; Palomar.PrimitiveCongruence.Closed/Total | The displayed header matches the selected type after Not expansion. P:Type u, nonemptiness, implicit formulas, terms, proofs and conclusion are explained. Total quantifies over all existing parallel terms. |
| D.2 p.17, short-proof table | Palomar.short_maximality; Palomar.PrimitiveCongruence.raw_distinct_iff; Isolation.normalized_literal_context; ContextualCollapse.all_contexts; Presentation.ShortProof.total | Raw inequality→quotient inequality→literal K→all K→collapse, with R.fragment and the actual interpretation/normalization/substitution/doubleNegation arguments explained. |

The five separately selected Palomar declarations remain the five in D.3.
These additional source links do not create new selections or a registration.
The full-paper endpoint, both proof routes and every old claim-map row remain.
No extra empty-P/constant-substitution/cardinality deduction is added to v16.


