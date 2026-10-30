# Complete manuscript claim map

This is the active exact correspondence for all mathematical content of v7,
preserved in v8 with a formalization-status/date/citation refresh and in v9 with
the AI-disclosure/registry-citation publication update. V9 has exactly the same
mathematical text, labels and diagrams. Earlier
coverage/statement maps and reports remain as dated checkpoints. “Complete” here
means local pinned Lean proof/source closure; it does not mean independent replay,
Comparator, official/service verification, public release or publication.

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
| §2 products, coproducts, units, distributor | Presentation.operations, conjDiagonal/disjDiagonal, source structural laws | Native beta/eta and uniqueness equations, all endpoints explicit. |
| Eq. (1), first injection | Presentation.Laws.dist_inl; ManuscriptDiagrams.first_triangle | Exact actual source identity. |
| §2 contravariant negation and natural comparisons | Presentation.negate and its contravariant functor; PresentationNegationNaturality.lean; doubleNegationNaturalIso | Derived raw representative, actual involution/DN/De Morgan naturality; Reduced coordinate/recovery bridge proved. |
| Eq. (2), zero identity | Presentation.zeroConstruction/zeroConstruction_eq/zeroConstruction_structural; ManuscriptDiagrams.zero_diagram/zero_primitive | Exact five-arrow path and equality to primitive zero. |
| Eq. (3), zero law | Presentation.Laws.zero_law; zeroIdentity; ManuscriptDiagrams.zero_square | All parallel existing arrows; no missing hom-set is inhabited. |
| §2 witnessed zeros, independence and absorption | ZeroIdentity.zeroOf/zeroOf_independent/commute/precompose/postcompose | Existing-arrow witness required; no HasZeroMorphisms. |
| §2 proof/substitution congruence | Presentation.ProofCongruence/RawProofCongruence; raw_quotient_rel/quotient_raw_rel; fragment/fragment_closed and closure transfers | Every primitive arrow operation, derived pairing/copairing/negation and uniform whole-arrow substitution. |
| Theorem 2.1 | Presentation.maximality/congruence_dichotomy/raw_maximality; Presentation.short_maximality | Exact additional-equation collapse and equality/total dichotomy. |
| §3 tagged occurrence definitions and labels | Formula.Occ/label; repeated_positions_distinct | Repeated equal labels retain distinct Sum tags; constants empty, negation preserves positions. |
| §3 finite left-to-right bijection | Formula.occurrenceCount/occurrenceIndex/occurrenceAt; occurrenceAt_index/occurrenceIndex_at; FiniteBlocks.oneBased/zeroBased and inverse laws | Explicit finite ordinal coordinates, including cardinality zero. |
| §3 functor G into finite sets/relations | FiniteSet.relationCategory; Presentation.occurrenceFiniteSet/finiteOccurrenceFunctor | Every source object has explicit finite coordinate bijections; identities/composition proved. |
| §3 G images of projections/injections/pair/copair/distributor/zero | Presentation.occurrence_fst/snd/inl/inr/pair/copair/dist/zero; original OccurrenceLaws | Exact tagged relations, rebracketing graph and empty zeros. |
| Theorem 3.1 Boolean Coherence | Gentzen.positive_coherence; Reduced.faithful/boolean_coherence; Presentation.coherence/finiteOccurrenceFunctor_faithful | Actual source coherence, not a supplied interface field. |
| §3 nonthinness and nonzero literal identity | Presentation.nonthin; literal_identity_ne_zero/identity_ne_zero/identity_ne_primitive_zero | Distinct repeated-tag projections, both signed literals, primitive/constructed zero. |
| §3 at most one global point and failure of cartesian closure | top_hom_subsingleton/fromTop_unique; ExponentialData.toGlobalPoint/fromGlobalPoint and both inverse laws; no_self_exponential/not_cartesian_closed | Exact printed p⇒p obstruction and hom/global-point bijection. |
| §3 NNF isomorphism and occurrence graph | Presentation.normalization; NegationNormalization comparisons; PresentationNormalizationTerms.lean | Actual forward/backward representatives, inverse equations and original-position transport. |
| §3 signed-literal preservation and equivalence of presentations | Presentation.occurrence_literal/occurrence_signedLabel; Reduced reduction/inclusion functors and recovery equations | Both signs and constants, raw and quotient bridges; no target-category coherence. |
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
| §6 alternative fold/mix formulas and symmetry | Presentation.tensor_prodMap/fold_source_mix/fold_manuscript/mix_parameter_independent/fold_parameter_independent/fold_symmetric; original ContextualCollapse proof | Exact displayed copair(id,id);mix identification and projection-pair symmetry, original coherence only. |

## Appendix A: every construction, example and diagram

| Anchor | Exact declaration correspondence | Status |
| --- | --- | --- |
| Finite pattern profiles and zero cardinalities | Formula.profile/profile_index; ProfileComposition.Data | Arbitrary outer and inner functions; no assumed injectivity/nonempty blocks. |
| D,C and injections a_r,b_i | Data.Domain/Codomain/a/b/a_injective/b_injective/a_disjoint/b_disjoint | Dependent Sigma blocks retain repeated outer positions and disjoint local placeholders. |
| Eq. (6), fibre square; unique gamma | Data.gamma/fibre_square/gamma_unique/gamma_fibre | Exact pointwise formula and uniqueness on every block. |
| Eq. (7), profile square | Data.profile_square | Both routes send (r,t) to outer(r). |
| Tagged inserted N_i and Phi_0 | PatternProfiles.tag/insertion/data/taggedBlock | Actual renamed patterns over C, not merely abstract cardinalities. |
| Actual chi bijection and Eq. (8) | taggedBlock_injective/surjective; chiInverse/chi; both inverse laws; unique_coordinates/occurrence_label_square | Every actual substituted occurrence has its unique old/local finite coordinates and the correct tagged label. |
| Prefix sums and consecutive encoders | FiniteBlocks.total/prefixSum/encode/decode/encode_value; encode_decode/decode_encode; total_concat/prefix_concat_left/right | Actual left-to-right order, arbitrary zero lengths; explicit source/target encodings. |
| Eq. (9), unique delta square | Data.delta/ordinal_square/delta_unique | Exact change of coordinates. |
| Eq. (10), one-based formula | Data.coordinate_equation/coordinate_oneBased/book_locator/book_formula; FiniteBlocks.oneBased/zeroBased/locator_bounds/locator_unique/zero_block_has_no_position | Exact unique nonempty containing block and local x−s_(r−1), including intervening empty blocks. |
| Actual finite-ordinal/book correspondence | Formula.substitution_count/substitution_index; PatternProfiles.composite_count/chiInverse_index/chiInverse_encoding/actual_ordinal_square/composite_profile | Block encoders agree with actual formula occurrence indices; no arbitrary finite bijection substituted for the printed order. |
| Skeleton/profile equivalence and generalized composite | Formula.skeleton/decorate/skeletonProfile/fromSkeletonProfile/skeleton_profile_reconstruction/skeleton_profile_unique/skeleton_rename; generalized_composite_skeleton/flattened_profile/generalized_composite_reconstruction | Restores complete syntax, not only variable labels; identifies the actual generalized composite with skeleton plus delta. |
| Worked profiles, sizes and eight outputs | PatternProfiles.Example.outer_profile/first_profile/second_profile/source_sizes/eight_positions | Actual M=q∧(p∨q), N1=a∧b, N2=d∧(c∨d); [4,3,4,1,2,4,3,4]. |
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
| Appendix C p.262 | BlockedDisjFirst.source_equation; fresh_principal_rank/fresh_total_rank/fresh_total_rank_ge_two; blockedL_disjunctionFirst_rank_step | Fresh right rank one and total h.rho.right+1≥2, with unchanged opposite premise, full Clean and exact original source. |
| Cut-elimination published dependency | Reducibility/Blocked-w/simultaneous atomized blocked cleaning; all twelve logical binary cases and all fourteen blocked source/rank steps; cut_elimination/atomized_cut_elimination | Constructor/tag dispatch, original selected-rank and strong degree induction instantiated; no assumed handlers remain. |
| Positive/Boolean coherence published dependency | G.mix_normal_form, actual pure/normal positive coherence and represented normal retracts, Gentzen.positive_coherence, Reduced.faithful/boolean_coherence, Presentation.coherence | Finite unions require existing-arrow witnesses; one-sided normalization recovery laws are proved; full intended source bridge instantiated. |
| Full source/negation/normalization bridge | Reduced quotient reduction/inclusion, normalization natural isomorphism, recovery and derived dual/negation equations; source congruence and closure correspondence | Actual intended categories and coordinate transports; both literal signs and empty hom-sets preserved. |

All declaration sources are below 10,000 physical lines and use the pinned core
Lean toolchain. Exact public checks, negative controls and transitive axiom/source
closure are recorded in the final evidence. No mathematical claim in the paper's
current scope remains assigned to an unproved field or deferred implementation
target. Historical reports are not independent verification of this final scope.
