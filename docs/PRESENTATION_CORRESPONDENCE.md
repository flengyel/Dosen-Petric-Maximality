# Published presentation correspondence

## Current complete full-paper formalization (29 October 2026)

All mathematical content of v7 is now proved for the actual equation-generated
Došen–Petrić presentation, with the status/citation refresh preserved in v8.
This includes both maximality routes, the full-source model corollary, all
unnumbered claims, the complete substitution action and actual occurrence/block/
profile/ordinal/renaming/skeleton constructions, all examples and all three
appendices' equations and diagrams. All published inputs used by the actual
proofs are proved or supplied by compatible verified core Lean constructions;
no uninstantiated handler/coherence/conclusion field remains at those endpoints.

The active exhaustive ledger is [MANUSCRIPT_COMPLETE_CLAIM_MAP.md](MANUSCRIPT_COMPLETE_CLAIM_MAP.md).
See [completion report](FULL_PAPER_COMPLETION_REPORT.md),
[hostile review](reviews/FULL_PAPER_COMPLETION_HOSTILE.md) and
[writing review](reviews/FULL_PAPER_COMPLETION_WRITING.md), plus the separate
FULL_SOURCE_MODELS_REPORT.md and all preserved earlier reports. The three old
milestones are explicitly separate rows in the current map. Full-paper closure
includes every additional appendix/model/operation obligation; it is not inferred
from actual maximality alone. Exact mathematical-source commit: 630c4b6e47da16a1434476a211fd29ce6adc5569.

Local checks cover 883 Lean files, 14,849 declarations, all 35 public files,
full transitive dependency/source closure and 74 expected rejections. Exact exits,
hashes, checked/committed archive and delivery paths are in provenance/wsl-appendix-a/.
Both reviews are local author-side. Independent replay, Comparator, official
preflight, service verification and publication were not performed. The repository
remains private. The original stash and all preceding source/results/receipts persist.

V8 updates the date and the abstract/introduction/section 6 formalization status,
and cites the immutable completed proof source. V4–v7 remain preserved; all
mathematical text, all appendices and ten diagrams are unchanged. Three stable
TeX passes and visual inspection cover all 13 pages and the updated citation.
FP-SCOPE-20261029 and FP-CITATION-20261029 are resolved. Older dated checkpoints
below retain their historical open statuses and are superseded by this complete
map; they are not new outstanding mathematical tasks.


## Retained full-source models and model corollary checkpoint (29 October 2026)

The v7 model corollary is now proved for the actual complete primitive source
presentation. Full interpretations, all-valuation canonical functors, substitution
composition and free evaluation correspondence are constructed; Source.model
instantiates every model law in the intended category. Universal agreement is a
uniformly substitution-closed full proof congruence. Actual maximality and the
native target product laws prove that all existing target hom-sets are
subsingletons. Nonempty source variables are used exactly to choose p. No
surjectivity, fixed-kernel closure, new arrow existence or mathematical axiom is
assumed. Target object/hom and source-variable universes are independent.

| Manuscript/source claim | Exact declarations | Scope/status |
| --- | --- | --- |
| Full model semantics | PresentationSemantics.Objects/Primitives, formula, Primitives.evaluate/SatisfiesTheory | All 31 raw constructor families and every actual Equation schema. |
| Quotient functor and full interpretations | evaluate_derives/evaluateHom/evaluationFunctor/canonicalInterpretation, Interpretation | Generated soundness and every finite primitive/object preservation law are proved. |
| Substitution composition and evaluation | Interpretation.precompose/object_evaluation/raw_evaluation/hom_evaluation | Independent variable universes, explicit object equalities and exhaustive constructor induction. |
| Intended model witness | Source.equations/bicartesian/model | Fully instantiated, including Nat nonthinness and Empty/top/bot checks; no unproved model bridge. |
| Universal agreement | Agreement.fragment_closed/congruence/closed/iff_valuations | Full family, equivalent to all canonical valuations. Additional derived-negation closure follows from proved fragment_dichotomy/of_closed_fragment, not an assumed kernel law. |
| cor:models | model_corollary/model_corollary_interpretations | All native target arrows collapse using equal projections and both native product beta laws. |
| Remaining whole paper | Arrow-action transports; Appendix A profiles/gamma/chi/ordinals/renaming/example; FP-SCOPE-20261029 | Open. All earlier reduction/coherence/main/short-proof/Appendix B and C results remain preserved. |

Exact declarations, immutable local evidence and committed-byte delivery paths
are in provenance/wsl-full-source-models/. Required local verification comprises
strict full dependency/source audit, all 34 public files and 66 rejection controls.
See [report](FULL_SOURCE_MODELS_REPORT.md),
[hostile review](reviews/FULL_SOURCE_MODELS_HOSTILE.md) and
[writing review](reviews/FULL_SOURCE_MODELS_WRITING.md). Both reviews are local
author-side. Independent replay, Comparator, official/service verification and
publication were not performed. All nine manuscript blobs and the stash remain
preserved. The final manuscript scope refresh remains pending before whole-paper
certification. Dated checkpoints below retain their historical scope.


## Retained original isolation and complete substitution square checkpoint (29 October 2026)

The printed original-endpoint isolation theorem, source nonzero identities and
cartesian-closure obstruction, all Appendix B paths and exact symmetric-fold
correspondence now have actual declarations. All 31 primitive constructors and
the actual quotient satisfy the whole-arrow occurrence-block substitution square;
substitution commutes with derived negation and the full arrow operations. Both
proved actual maximality routes are preserved. The model corollary, remaining
substitution-action composition and Appendix A profile/ordinal claims continue.

| Manuscript/source anchor | Exact declarations and files | Scope/status |
| --- | --- | --- |
| Lemma 4.1 original witnesses | Isolation.original_composite/original_witnesses; Presentation.occurrence_isolation; OriginalIsolation.lean | Original l∧bot→A and B→l∨top, both equations and permitted interchange; all actual inputs instantiated, arbitrary P : Type u. |
| §3 nonzero identity/global points | top_hom_subsingleton, literal_identity_ne_zero/identity_ne_zero/identity_ne_primitive_zero; PresentationConsequences.lean | Both literal signs, primitive/constructed zero, no hom-set existence added. |
| §3 cartesian-closure obstruction | ExponentialData.hom_unique; no_projection_exponential/not_cartesian_closed; CartesianClosureObstruction.lean | Standard evaluation/beta/eta; global-point uniqueness and unit retraction, distinct projections, actual variable p required. |
| Appendix B, three diagrams | first_triangle, zero_diagram/zero_primitive, zero_square; ManuscriptStructuralDiagrams.lean | Every displayed path component typed and exact original source equalities proved. |
| §6 displayed symmetric fold | tensor_prodMap, fold_source_mix/fold_manuscript, mix/fold_parameter_independent, fold_symmetric; PresentationSymmetricFold.lean | Exact mix;codiagonal/copair identities and pair-of-projections symmetry, original coherence only. |
| Actual substitution label square | contract_injective/contract_eq_iff/contract_label/expand_label/fiber_identity; FormulaSubstitutionCoordinates.lean | Actual dependent block bijection, labels, empties, repeated tags; arbitrary source/target variable universes. |
| Complete raw and quotient block square | Term.substitution_coordinates; occurrence_substitute_coordinates/expanded; PresentationSubstitution*.lean | Exhaustive 31 primitive constructors, exact inner-coordinate equality, old signed-label invariant; no injective-label or nonempty-block assumptions. |
| Full substitution operation preservation | substitute_negate/negate_subst_derives/substitutionFunctor; tensor/pair/copair/zero laws; PresentationSubstitutionOperations.lean | Actual derived-negation compatibility, raw admissibility, categorical id/comp and all source arrow operations. |
| Formula substitution action | subst_identity/subst_composition/subst_ext; FormulaSubstitutionLaws.lean | Actual object-level identities between independent variable universes. General arrow-action composition transports remain separate. |
| Remaining full-paper scope | Model, arrow-action composition, Appendix A profiles/gamma/chi/ordinals/renaming/example and final manuscript scope refresh | Open; do not equate the complete block theorem with the entire Appendix A or certify the whole paper. |

Evidence: provenance/wsl-full-paper-claims/. Strict pinned verification, all 33
public files and 61 rejection controls have exact counts/exits/hashes in
FINAL_VERIFICATION.json. Checked sources are archived, read back and compared
with committed bytes. See [report](FULL_PAPER_CORRESPONDENCES_REPORT.md),
[hostile review](reviews/FULL_PAPER_CORRESPONDENCES_HOSTILE.md),
[writing review](reviews/FULL_PAPER_CORRESPONDENCES_WRITING.md). Reviews are local
author-side; independent replay, Comparator, official/service verification and
publication were not performed. DELIVERY_REGISTER.json retains exact verified
conflict-preserving repository/Downloads paths. The stash and all nine manuscript
blobs remain preserved. V7's dated §6 status paragraph is historical after these
proofs; a coordinated scope refresh is explicitly pending before full-paper
certification. No false mathematical theorem was established.

Continue the full-paper contract: construct full-source model interpretations,
their substitution composition and universal-agreement congruence, then prove
the model corollary and every remaining Appendix A claim. Complete general arrow-
substitution action transports and the final manuscript scope refresh. Preserve
all completed proofs, both maximality routes and every accepted correction.
The retained dated checkpoints below preserve their historical scope.


## Retained short q_A/e_A proof checkpoint (29 October 2026)

The particular manuscript q_A and e_A now have explicit raw primitive-arrow
inverses and both original inverse equations. The distinct short collapse proof
is proved directly modulo congruence and connected to actual maximality by
`Presentation.short_maximality`. The existing `Presentation.maximality` symmetric-
fold route and dichotomy remain unchanged. Full-paper completion stays separate:
the model, remaining operation/substitution/isolation/appendix claims continue.

| Claim / manuscript anchor | Exact declarations and files | Scope/status |
| --- | --- | --- |
| Lemma 5.1, particular q_A | ShortProof.qTerm/qInverseTerm, q_definition, q_qInverse/qInverse_q; PresentationShortQ.lean | Arbitrary P : Type u and every formula A. Actual raw inverse and both original equations. |
| Lemma 5.1, particular e_A | sourceConjTerm/sectionTerm/eTerm/eInverseTerm, e_definition, e_eInverse/eInverse_e; PresentationShortE.lean | Actual section and explicit zero witness fst;diag; both original inverse equations. Distribution itself is not invertible. |
| Lemma 5.1, substitution transport | Ten *_subst/*_substitute theorems; PresentationShortSubstitution.lean | Whole-arrow raw and quotient substitution between independent variable universes, with exact endpoint types. |
| Lemma 5.2, terminal E=A∨top modulo Q | context_zero_through_top, q_zero_form, q_terminal, terminal_id/hom/pair; PresentationShortTerminal.lean | Every K_A and exact Congruence closure; q inverse is original. No symmetric-fold collapse is invoked. |
| Lemma 5.2, projection/diagonal collapse | i_r/e_r/r_i/projection_id/diagonal_u/projection_diagonal/projections/total; PresentationShortProjection.lean | Original e inverse and quotient-terminal uniqueness; direct modulo-congruence proof, no quotient coherence or cancellation of j_A. |
| thm:main by the short route | Presentation.short_maximality; PresentationShortMaximality.lean | Actual full proof congruence and uniform closure, actual isolation/all-contexts/substitution inputs, arbitrary P. |
| Existing alternative route | Presentation.maximality/congruence_dichotomy/raw_maximality | Preserved unchanged, with all actual source inputs and full congruence correspondence. |
| Remaining full-paper scope | Universal-model corollary, further operation/substitution laws, original isolation witnesses, non-cartesian-closure and appendix correspondences | Open; the three milestones and both maximality routes do not certify the whole paper. |

All completed cut elimination, coherence, source negation/naturality, quotient
functors and congruence bridges remain preserved. No new manuscript defect was
established; all nine manuscript blobs, three appendices, ten diagrams, accepted
corrections and the stash are unchanged. Evidence: provenance/wsl-short-proof/.
Strict pinned verification, all 32 public files and 55 rejection controls have
exact counts/exits/hashes in FINAL_VERIFICATION.json. The checked source archive
is read back and compared with committed bytes. See [report](SHORT_QE_REPORT.md),
[hostile review](reviews/SHORT_QE_HOSTILE.md),
[writing review](reviews/SHORT_QE_WRITING.md). Reviews are local author-side;
independent replay, Comparator, official/service verification and publication
were not performed. DELIVERY_REGISTER.json retains exact byte-verified conflict-
preserving repository/Downloads paths.

Continue the unchanged full-paper contract. Complete derived-negation/substitution
compatibility and general substitution operation/coordinate laws, the universal-
model corollary and every remaining v7 claim. Preserve both proved maximality
routes and all settled mathematical decisions. The retained dated checkpoints
below preserve their historical scope, superseded by this active theorem table.


## Retained actual source maximality and derived negation checkpoint (29 October 2026)

`Presentation.maximality`, `congruence_dichotomy` and `raw_maximality` are proved
for the actual equation-generated quotient and full proof congruences. Every
relative-maximality input is instantiated. P is arbitrary, hence includes the
manuscript's nonempty case. Totality ranges only over existing hom-sets. The three
milestones remain distinct from complete-paper certification. The short q_A/e_A
proof, model corollary and remaining operation/appendix claims continue.

| Manuscript/source claim | Exact declarations and files | Scope/status |
| --- | --- | --- |
| Quotient reduction and inclusion | Reduced.reduceHom, reductionFunctor/inclusionFunctor; ReducedQuotientReduction.lean, ReducedReductionFunctor.lean | Actual typed quotient lift, identities, comp/tensors, equality reflection and explicit recovery casts; arbitrary P : Type u. |
| Normalization equivalence laws | normalizationNaturalIso, reduction_inclusion, recover_reduceHom/reduce_recoverHom; ReducedReductionFunctor.lean, ReducedRecovery.lean | Source-side natural isomorphism and reverse recovery at exact endpoint casts. |
| §2 contravariant negation | Reduced.Term.dual, dual_relation, dualHom_involutive; Presentation.negationFunctor; ReducedDual*.lean, PresentationNegationFunctor.lean | Complete raw reflection, quotient descent, id/reversed comp; no Gentzen-proof duality assumption. |
| Natural DN/DM comparisons | dnOut_natural/dnIn_natural, all four dmConj/Disj Out/In_natural, doubleNegationNaturalIso; PresentationNegationNaturality.lean | Actual original-category naturality and existing two-sided comparison laws, including constant inverse laws. |
| Explicit source negation syntax | forwardTerm/backwardTerm, their denotation laws, Term.negate/negateTerm_denotes/negate_derives; PresentationNormalizationTerms.lean, PresentationNegationTerms.lean | Uses only the existing primitive source grammar and generated equality. |
| Original negation occurrence graph | toOcc_neg; occurrence_negate; PresentationNegationCoordinates.lean, PresentationNegationOccurrence.lean | Exact converse at original tags, both signs and repeated positions. |
| Full proof-congruence correspondence | ProofCongruence, RawProofCongruence, fragment, toRaw/toQuotient, raw_quotient_rel/quotient_raw_rel; PresentationProofCongruence.lean | All primitive arrow-argument operations and actual derived negation; pair/copair derived; both pointwise inverse correspondences. |
| Uniform closure correspondence | toRaw_closed/toQuotient_closed, fragment_closed; PresentationProofCongruence.lean | Explicit endosubstitution closure transfers at both typed levels. No fixed-kernel closure assumption. |
| thm:main | Presentation.maximality, congruence_dichotomy, raw_maximality; PresentationMaximality.lean | Actual source theorem, equality/total dichotomy and raw generated-equality formulation; every relative input proved. |
| Remaining full-paper scope | Short q/e proof, model corollary, further operation/substitution/ordinal/diagram claims | Open. In particular derived-negation/whole-arrow-substitution compatibility is not inferred from the congruence correspondence. |

The original symmetric-fold route supplies this actual maximality instance; its
source, all completed cuts/coherence, prior reports, stash and manuscript versions
remain preserved. Milestone I's intended faithful interface and milestone II's
conditional theorem remain complete. Milestone III's actual maximality theorem
and its raw/quotient closure bridge are now instantiated. This is not the full-
paper endpoint: prove the separate short proof and every remaining v7 claim.

Evidence: provenance/wsl-full-source-bridges/. Strict pinned verification, all
31 public check files, actual source witnesses and 52 expected rejection controls
are recorded with exact counts, exits and hashes in FINAL_VERIFICATION.json.
The checked source archive is read back and compared with committed bytes.
See [report](SOURCE_MAXIMALITY_REPORT.md),
[hostile review](reviews/SOURCE_MAXIMALITY_HOSTILE.md),
[writing review](reviews/SOURCE_MAXIMALITY_WRITING.md). Reviews are local author-
side. Independent replay, Comparator, official/service verification and publication
were not performed. DELIVERY_REGISTER.json records verified conflict-preserving
repository/Downloads copies. No manuscript defect was established; all nine
manuscript blobs and ten diagrams remain unchanged.

Current continuation: construct the particular q_A/e_A inverses and prove the
short collapse route directly modulo congruence, preserving the symmetric-fold
route. Complete negation/substitution compatibility and whole-arrow substitution
operation/coordinate laws, the universal-model corollary and every remaining
claim in the three v7 appendices. Reuse all completed results without reopening
settled source/rank/atomization decisions. Historical checkpoints below preserve
their dated scope; this active table supersedes their earlier open statuses.


## Retained Positive, Reduced and Boolean coherence checkpoint (29 October 2026)

`Gentzen.positive_coherence : PositiveCoherence P`, `Reduced.faithful : Faithful P`
and `Presentation.coherence` are proved for arbitrary P. The full intended
`Presentation.interpretation P` and its signed-label invariant are instantiated.
The public Nat instance is nonthin; Empty/constants and the original empty
Hom(top,bot) are preserved. Milestone I's complete intended faithful-interface
requirement is met. The conditional maximality theorem remains proved; the full
source congruence/substitution correspondence and actual maximality instantiation
remain to be completed. The three milestones and full-paper endpoint are distinct.

| Claim / source scope | Actual declarations | Exact status |
| --- | --- | --- |
| Positive cut-free representation | positive_cutFree_represented; positive_mix_represented | Actual CutFree/Atomized witnesses, exact original tags, pure-endpoint mix fragment. |
| Signed atomic paths | PurePort.position_ofPosition/position_injective; PureEdge.relation | Independent source/target positions; singleton relation; constants have no ports. |
| Finite atomic normal forms | finiteUnion laws; PureEdge.evaluate_faithful; G.mix_normal_form | Witnessed empty union, exact rule constructions and reversed-block mix; no assumed normalizer. |
| Restricted positive coherence | pure_positive_coherence; normal_positive_coherence | Pure base, then DNF source/CNF target via actual universal properties. |
| General formula expansions | NormalRetract; dnf_expansion/cnf_expansion | Explicit represented maps with only forward;backward=id_original. No distributive isomorphism. |
| Unrestricted positive coherence | Gentzen.represented_coherence; positive_coherence | Complete actual normal-form argument for arbitrary P. |
| Full Reduced coherence | Reduced.faithful | Existing common atomic factorization instantiated with proved PositiveCoherence. |
| Boolean coherence of the source quotient | Reduced.boolean_coherence; Presentation.coherence | Existing signed reduction, representation and original normalization transfers instantiated. |
| Intended full occurrence interface | Presentation.interpretation; interpretation_signedLabel | Every field is constructed in the equation-generated category, including faithfulness. |

All unrestricted cut elimination, twelve binary branches, fourteen blocked families,
Reducibility, Blocked-w, simultaneous cleaning and both Appendix C concrete rows
remain proved. All nine manuscript blobs, source decisions, stash and receipts
are preserved. No new manuscript defect was found. Coherence is used in the
original category; a fixed-valuation kernel is not assumed substitution-closed.

See [report](GENTZEN_COHERENCE_REPORT.md),
[hostile review](reviews/GENTZEN_COHERENCE_HOSTILE.md),
[writing review](reviews/GENTZEN_COHERENCE_WRITING.md).
Evidence: provenance/wsl-gentzen-positive-coherence/. Strict pinned verification,
all thirty public check files and 48 expected rejections have exact counts,
commands, exits and hashes in FINAL_VERIFICATION.json. Checked source archives
are read back and compared with committed bytes; DELIVERY_REGISTER.json retains
verified conflict-preserving repository/Downloads paths. Reviews are local
author-side; independent replay, Comparator, official/service verification and
publication remain separate unperformed statuses.

Next complete the full source congruence/uniform-substitution correspondence,
instantiate actual maximality, formalize the short q_A/e_A proof while retaining
the symmetric-fold route, and finish the model corollary and every remaining
mathematical claim in all three v7 appendices. Continue under the existing full-
paper authorization. Retained checkpoints below keep their historical scope;
this current table supersedes their earlier open coherence/normalization statuses.


## Current manuscript: v7 with the authorized errata appendix

V7, dated 28 October 2026, preserves all v6 mathematical content and adds the
exact author-requested Appendix C plus its introduction roadmap sentence.
Appendix C records the source p.260 inequality r' < r and p.262 right-rank-one
qualification. The entire Appendix C is on PDF p.12, followed by the unchanged
disclosure; references are on p.13. The final local TeX build resolves all
references/citations and has no overfull/underfull boxes or warnings. All ten
TikZ diagrams, Appendices A–B, the disclosure and bibliography are unchanged
in source. The v4/v5/v6 source/PDF pairs remain byte-identical.

Active source: `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.tex`,
SHA-256 `70b4f82c03e165e6a6da36d869968531a509341b93f90eedde964506568c8e96`. Active PDF: the same basename with .pdf,
SHA-256 `957048538137ef085c0a581b399272db753377b76c6a83c1adc307ad8b2e256a`. Evidence: `provenance/wsl-manuscript-v7/`;
report: `MANUSCRIPT_V7_ERRATA_REPORT.md`; reviews:
`reviews/MANUSCRIPT_V7_ERRATA_HOSTILE.md`, `reviews/MANUSCRIPT_V7_ERRATA_WRITING.md`.

The manuscript addition is complete; its concrete blocked-reduction Lean
correspondence remains open. Selected-cut positivity and native fresh-principal rank-one laws now compile;
the concrete blocked reductions remain open. Global cut elimination, coherence and all other full-paper obligations
retain their current status. The underlying v6 target is supplemented, not reduced.

## Retained opposite logical checkpoint (28 October 2026)

`CutCommutation.opposite_conjL` and `opposite_disjR` prove the two actual opposite
unary logical commuting families at arbitrary selected gaps and original output
sequents. Their `eliminated` lemmas rebuild actual cut-free atomized witnesses.
`opposite_conjL_descent`/`opposite_disjR_descent` reuse the completed addressed
selected-predecessor inheritance to prove complete cleanliness and strict original
selected-rank descent. Both `rank_step` lemmas recurse on that exact child before
reconstructing the logical rule; no unchanged-degree cleaning or routed-rank
substitution occurs.

`prefixSide` and its actual join/split comparison laws support prefixed native
logical rules. `suffixLogicalSide_join`/`split` prove both side suffix diagrams,
including units and association transports. The required `assocL_pentagon` is
proved from established product coordinates and instantiated with actual side
laws. `PrefixedLogical` and `SuffixedLogical` give native rules with checked
Reduced denotations, cut counts and Atomized laws. No unproved coherence or
duality input is assumed.

Checked: **510 screened Lean files / 11,669 audited project declarations**.
Strict build/transitive audit, eight exact public type files, five expected
negative control rejections, public closure, all manuscript hashes and whitespace
pass. Evidence: `provenance/wsl-gentzen-opposite-logical-cuts/`; report:
`GENTZEN_OPPOSITE_LOGICAL_CUTS_REPORT.md`; reviews:
`reviews/GENTZEN_OPPOSITE_LOGICAL_CUTS_HOSTILE.md`,
`reviews/GENTZEN_OPPOSITE_LOGICAL_CUTS_WRITING.md`.

Reuse all principal, structural, opposite logical, selected-predecessor,
Reducibility and simultaneous clean-cut work. Continue the same-side logical and
binary commutations, all fourteen blocked families and the complete constructor
dispatcher; then prove the all-ranks clean theorem, strict degree induction and
global elimination. DegreeBelow remains uninstantiated globally. The full-paper
endpoint, all later coherence/intended-presentation/substitution/maximality/model
and appendix obligations remain active. Appendix C's concrete blocked reductions
remain open. All three milestone statuses and all accepted corrections persist.

## Retained structural selected-cut checkpoint (28 October 2026)

Historical scope at f4a8da3; the current checkpoint proves the opposite logical
families recorded as open here. The structural scope and atomization decision remain.


`CutCommutation.same_right` and `same_left` prove both actual same-side structural
commuting equations at the original selected output sequent. `Route.SingleFiber`
requires one upper preimage of the exact lower tag, across all formula labels.
`Route.residual_square` proves the component diagram; the residual route is
realized by actual structural rules. `exchange_singleFiber`, `thin_singleFiber`
and `contract_singleFiber` instantiate exchange, every old thinning position and
every unselected contraction position. Equal fixed labels and empty blocks remain
explicit. The selected lower contraction belongs to the still-open blocked cases.

`leftAddress`/`rightAddress` prove the actual original-proof addresses and exact
step lengths. Their ascent laws and existing address inheritance give the same
recursive child's CutFree, Atomized and complete AllBlockedAt condition.
`rank_same_right`/`rank_same_left` prove strict original selected-rank decrease for
nonempty programs. `same_right_rank_step`/`same_left_rank_step` use that exact
clean smaller-rank child. Residual reconstruction is atomized only after its cut
is eliminated; no output-rank or output-blockedness claim is inferred.
`selected_opposite_left`/`selected_opposite_right` and both descent lemmas extend
the completed opposite structural results to arbitrary selected gaps.

Checked: **500 screened Lean files / 11,626 audited project declarations**.
Strict build/transitive audit, seven exact type files, five expected negative
control rejections, public closure, all manuscript hashes and whitespace pass.
Evidence: `provenance/wsl-gentzen-structural-cuts/`; report:
`GENTZEN_STRUCTURAL_CUTS_REPORT.md`; reviews:
`reviews/GENTZEN_STRUCTURAL_CUTS_HOSTILE.md`, `reviews/GENTZEN_STRUCTURAL_CUTS_WRITING.md`.

Reuse both principal equations, both conditional degree steps, exhaustive
rank-two classification/step, all structural results, Reducibility and simultaneous
clean-cut construction. The current checkpoint proves the opposite logical
families. Continue the remaining same-side logical and binary commutations, all
fourteen blocked families and the complete constructor dispatcher. Then prove
the all-ranks clean theorem, discharge DegreeBelow and prove global elimination.
At unchanged degree recurse on the inherited original clean child with proved
smaller selected rank; at smaller degree allow arbitrary returned ranks. Coherence
and all later full-paper obligations retain their open statuses. Appendix C's
concrete blocked correspondences remain open. All three milestones stay distinct.

## Retained disjunction and principal degree checkpoint (28 October 2026)

Historical scope at ef25f48. The current checkpoint above supersedes its open
same-side structural status; its principal/degree scope and source decisions remain.


`PrincipalDisjunction.selected_equation` proves the actual positional disjunction
principal reduction at every selected gap, in Reduced and at the original output
sequent. It cuts B, then A, with all component, unit and association transports
explicit. The reduction has two component cuts and preserves the conjunction of
the three Atomized predicates. `MirrorInterpretation` identifies the reflected
diagrams with the actual `Rules.sourceConj` and cut splice; all reflected laws
are proved from Reduced. No unproved quotient-arrow duality is assumed.

`HeadRouting.front_arrow`, `front_split` and `front_singleton` prove the exact
selected exchanges; all prefix/head/tail tags and empty contexts are included.
`PrincipalConjunction.degree_step` and `PrincipalDisjunction.degree_step` construct
cut-free atomized witnesses by eliminating the inner component cut before the
outer cut, using strictly smaller formula degrees and arbitrary returned ranks.
`PositionalCut.rank_two_degree_step` now exhausts selected rank-two elimination
under the explicit `DegreeBelow` hypothesis. That hypothesis is the strict outer
induction hypothesis; it is not discharged globally. `CutElimination` and
`AtomizedCutElimination` remain unproved endpoint definitions.

Checked: **491 screened Lean files / 11,561 audited project declarations**.
Strict build/transitive audit, six exact type files, five expected negative
control rejections, public closure, manuscript hashes and whitespace pass.
Evidence: `provenance/wsl-gentzen-principal-disjunction/`; report:
`GENTZEN_PRINCIPAL_DISJUNCTION_REPORT.md`; reviews:
`reviews/GENTZEN_PRINCIPAL_DISJUNCTION_HOSTILE.md`,
`reviews/GENTZEN_PRINCIPAL_DISJUNCTION_WRITING.md`.

Reuse all completed principal, positional, Reducibility, simultaneous clean-cut,
predecessor and opposite structural results. The same-side structural cases recorded as open here are now proved.
Continue the remaining logical and binary commutations and all fourteen blocked
families; then prove the all-ranks clean theorem, discharge the degree induction and prove
global elimination. Unchanged-degree recursion requires actual inherited
cleanliness and strict selected-rank descent; do not re-clean and infer a bound.
At smaller degree, arbitrary returned ranks are allowed. Coherence and all later
full-paper obligations retain their open statuses. Appendix C's concrete blocked
correspondences remain open. All three milestones remain distinct.

## Retained principal conjunction checkpoint (28 October 2026)

Historical scope at dff2994; the current checkpoint above supersedes its open
disjunction and principal-recursion status. Its source-order decision remains.


`PrincipalConjunction.selected_equation` proves the actual principal conjunction
reduction at every selected gap, in Reduced and at the unchanged output sequent.
The native construction cuts A then B, with explicit component and list-fold
transports. It is a directly proved alternative to the displayed source p.254
order. `selectedReduction_count` records its two component cuts;
`selectedReduction_atomized` preserves the exact Atomized conjunction. Both
component degrees are strictly smaller, with no returned-rank hypothesis.
This is a reduction equation; its cut-free representative still requires the
smaller-degree recursive calls in the full induction.

`CutDistribution.mixed_strength`, the product-coordinate adapters and
`PrincipalConjunction.equation` prove the categorical diagram without a coherence
premise. Canonical triple-fold inverses and every association tag are checked.
`LogicalHeadRouting.square`, `G.conjL_toHead` and `G.disjR_toHead` transport a
selected logical formula by moving its two component tags below a fresh native
rule, including empty contexts and repeated labels. No wrapper inherits a
rank-one claim. At this retained checkpoint the dual disjunction principal
equation was open; the current checkpoint proves it.

Checked: **474 screened Lean files / 11,403 audited project declarations**.
Strict build/transitive audit, five exact type files, five expected control
rejections, public closure, v4/v5/v6/v7 manuscript hashes and whitespace pass.
Evidence: `provenance/wsl-gentzen-principal-conjunction/`; report:
`GENTZEN_PRINCIPAL_CONJUNCTION_REPORT.md`; reviews:
`reviews/GENTZEN_PRINCIPAL_CONJUNCTION_HOSTILE.md`,
`reviews/GENTZEN_PRINCIPAL_CONJUNCTION_WRITING.md`.

Reuse the completed positional interface, complete rank-two classification,
atomic elimination, selected clean normalization, strict predecessor inheritance
and opposite-side structural commutations. The dual principal equation and its
conditional degree branch are now proved. Continue the remaining parametric and
fourteen blocked reductions, then discharge the
outer degree/inner all-ranks induction and global elimination. Coherence and all
later full-paper obligations retain their open statuses. All three milestones
remain distinct; the v7 manuscript and Appendix C blocked correspondences are
unchanged by this checkpoint.

## Retained selected-cut checkpoint (28 October 2026)

The positional interface and complete least-rank classification now compile.
`PositionalCut.atomic_rank_two` returns a cut-free atomized witness with Reduced
equality at the exact positional output for every literal and both constants.
`rank_two_classification` exhausts all selected rank-two cuts: this atomic branch
or the conjunction/disjunction principal pair. At this retained checkpoint the
compound principal equations were open; the current checkpoint proves both
equations and their conditional strict-degree elimination steps. `CutElimination` and `AtomizedCutElimination` are endpoint definitions,
not proved theorems.

`At.erase`, `retain`, `toHead_get` and `toHead_get_retain` retain every tag;
head routing is identity. `PositionalCut.rank` measures the original premises.
`routed_rank_eq` separately accounts for zero/one exchange per routed selection.
`AllBlockedAt` has exact cluster and head correspondences, branch characterization
and complete address/predecessor inheritance. `clean_premises` reuses the completed
simultaneous clean-cut theorem at arbitrary original selected sequents, without a
rank bound. The actual predecessor clean/rank lemmas justify smaller subcuts.

Fresh native principal occurrences have rank one and no tied lower contraction,
independently of the returned inner proof sizes. Source disjLLast exchange
wrappers remain separate. `CutCommutation.opposite_left` and `opposite_right`
prove actual Reduced equations for all opposite-side structural programs,
including contractions, using fixed-context transports. The remaining same-side,
logical, binary and fourteen blocked reductions remain open.

Checked: **464 screened Lean files / 11,310 audited project declarations**.
Strict build/dependency audit, four exact signature files, five expected control
rejections, public source closure, v4/v5/v6/v7 hashes and whitespace pass.
Evidence: `provenance/wsl-gentzen-positional-cuts/`; report:
`GENTZEN_POSITIONAL_CUTS_REPORT.md`; reviews:
`reviews/GENTZEN_POSITIONAL_CUTS_HOSTILE.md`,
`reviews/GENTZEN_POSITIONAL_CUTS_WRITING.md`.

| Source / target | Exact declaration | Status |
| --- | --- | --- |
| Selected cut and residual tags | `PositionalCut.cut`, `head`, `count`, `atomized`, `congr`; `At.toHead_get_retain` | Compiled, actual existing G rules and transports. |
| Original selected measure | `rank_ge_two`, `rank_two_iff_leaves`, `routed_rank_eq` | Compiled; native exchange cost is explicit. |
| Clean recursive premises | `AllBlockedAt.inherit`, `clean_left/right_predecessor`, `rank_left/right_predecessor` | Compiled for actual selected ancestry; no re-cleaning rank inference. |
| Simultaneous selected normalization | `PositionalCut.clean_premises` | Compiled at original sequents, without rank bound. |
| §11.2 pp.253–254, §11.5, §12.5 | `atomic_rank_two`, `rank_two_classification` | Exhaustive atomic base elimination and complete least-rank classification; compound branch remains to eliminate. |
| Fresh principal rank argument | `rank_fresh_disjL`, `rank_fresh_conjR`, both strict comparison lemmas | Native rank one compiled; concrete sequential blocked reductions remain open. |
| Opposite structural commutations | `CutCommutation.opposite_left`, `opposite_right` | Compiled equations; remaining commutations and global induction open. |

Continue the full-paper contract. Actual compound equations, all remaining
commutations and blocked reductions, global cut elimination, coherence, actual
presentation/congruence/substitution bridges, short q_A/e_A, maximality, model
corollary and every appendix claim remain the authorized work. The three
milestones and the whole-paper endpoint remain distinct. V7 is unchanged.

## Completed-run review and successor (28 October 2026)

The [review of 5c72a84](reviews/GENTZEN_5C72A84_REVIEW.md) supports the clean-cut
checkpoint and distinguishes source/log inspection from a new build. The
[successor instruction](CODEX_AFTER_5C72A84_CUT_ELIMINATION.txt) specifies
selected-position transport, degree/rank induction and the nested fresh-principal
argument for global elimination. Its new construction targets remain unproved.
Two source typos at printed pp.260 and 262 are recorded in
[the correction ledger](MANUSCRIPT_CORRECTIONS.md). The author subsequently
requested both in the arXiv paper. V7 implements the exact Appendix C and
roadmap sentence, preserving v6. Local insertion, PDF build, rendered review
and updated manuscript/claim anchors are complete; see the v7 report above.
The earlier six Downloads deliveries remain complete. This successor's
instruction, two reviews and the new v7 artifacts are included in the current
committed-byte delivery, certified by the post-commit receipt.

## Retained simultaneous clean-cut checkpoint (28 October 2026)

`DosenPetric.Reduced.Gentzen.clean_cut_premises` proves simultaneous atomization
and blockedness for arbitrary P and every topmost cut, at the original sequents.
The same f',g' are cut-free and Atomized, have individual Reduced equalities,
and satisfy AllBlockedR f' and AllBlockedL g'. `clean_cut_normalization` gives
cut equality and the expanded universal tied-contraction clauses. There is no
coherence, Nonempty P, DecidableEq P or supplied compatibility hypothesis.

The construction atomizes first. `Route.atomic_program` realizes routes with
atomic omitted positions using only atomic thinnings. Positional residual
preimages and actual exchange/contraction/thinning support are proved.
`reducibility_left_atomized` and `reducibility_right_atomized` cover all actual
input schemas with one joint CutFree/Atomized/equality/descendant-bound witness.
`rank_replacement_for` uses that chosen witness; the existing finite enumeration,
outside correspondence, multiset descent and no-eligible-site argument are reused.
Unrestricted Reducibility, Blocked-w and the negative atomizer example remain.

The formalization continues with `CutBase.identity_identity`, `zero_identity`,
`identity_zero`, `zero_zero`, `thinned_thinned`, `endomorphism_thinning`,
`thinning_endomorphism`, `top_thinning` and `thinning_bot`. These are actual
Reduced equations for the atomic/zero/thinning and constant base patterns,
with explicit empty-context transports and cut-count laws for their repairs.
They do not yet give the exhaustive rank-two classification or global cut elimination.

Checked: **442 Lean files / 11,105 audited project declarations**. Strict
verification, all three exact-signature files, five expected control rejections,
public source closure, manuscript hashes and whitespace pass. Evidence:
`provenance/wsl-gentzen-clean-cuts/`; report: `GENTZEN_CLEAN_CUTS_REPORT.md`;
reviews: `reviews/GENTZEN_CLEAN_CUTS_HOSTILE.md` and
`reviews/GENTZEN_CLEAN_CUTS_WRITING.md`.

| Source / claim | Exact declaration | Scope |
| --- | --- | --- |
| §11.2 p.253 clean cuts | `clean_cut_premises`, `clean_cut_normalization` | Same formula and contexts; both invariants for the same witnesses. |
| Atomic-omission realization | `Route.atomic_program`, `atomic_program_arrow` | All typed positions; both product and opposite coproduct arrows. |
| Residual support | `ContractionSelection.factor_route_preimage`, `factor_route_support` | Preimage of each remaining tag, including repeated labels. |
| Joint local repairs | `reducibility_left_atomized`, `reducibility_right_atomized` | Every containing address and every rebuilt eligible descendant. |
| Descent with that witness | `ReducibleL/R.rank_replacement_for`, `blocked_normalization_left/right_atomized` | Existing rank multiset and well-founded relation, with Atomized invariant. |
| §11.2 pp.253–254 / §12.5 p.291 | `CutBase.identity_identity`, `zero_identity`, `identity_zero`, `zero_zero`, `endomorphism_thinning`, `thinning_endomorphism`, `thinned_thinned` | Base equations, including both signs; exhaustive rank classification remains open. |
| §11.5 p.273 | `CutBase.top_thinning`, `thinning_bot`; `thinned_thinned` at top/bot | Both constants, actual repairs and explicit list transports. |

Global cut elimination, restricted mix/positive coherence, Reduced.Faithful,
Boolean Coherence, actual source/congruence/substitution bridges, the short
q_A/e_A proof, unconditional maximality, the model corollary and remaining v6
appendix claims remain open under the unchanged full-paper contract. Milestones
I–III and whole-paper completion remain distinct. No manuscript defect is inferred.

## Retained earlier checkpoints

The following sections retain their historical source and verification scope.

## Historical Blocked-w checkpoint (28 October 2026)

`DosenPetric.Reduced.Gentzen.blocked_w` proves the actual Blocked-w endpoint:
for arbitrary P and a topmost cut, the same cut formula and contexts have cut-free
representatives with equal Reduced cut denotation and both universal tied-contraction
blockedness clauses. `blocked_w_premises` also preserves each premise's denotation.
Both full Reducibility theorems and their complete descendant quantifiers are reused.

Containing preservation covers all fourteen source envelopes with arbitrary
same-sequent replacements at proper lower-contraction occurrences. Complete
outside eligibility equivalence, exclusion of new strict containing sites,
finite typed enumeration and exact multiset replacement compile on both sides.
The multiset proof retains multiplicities and uses fixed-support count vectors.

Checked: **412 Lean files / 10,906 audited project declarations**. Strict
verification, both exact signature files, five expected control rejections,
manuscript checksums and whitespace checks passed. Evidence:
`provenance/wsl-gentzen-blocked-w/`; report: `GENTZEN_BLOCKED_W_REPORT.md`.

The next obligation is simultaneous atomization and blockedness. The compiled
`AtomizationBlockedBoundary.cutFree_equal_atomized` gives a cut-free Empty-variable
counterexample to preservation of AllBlockedL by the existing G.atomize.
Its new unblocked tied contraction has path [0,0,0,0]. This is a boundary of that
construction, not a manuscript defect or a refutation of clean-cut existence.
Clean cuts, cut elimination, coherence, actual-presentation maximality, the model
corollary and remaining v6 appendices stay open. Milestones I–III remain distinct.

| Source / claim | Exact declaration | Scope |
| --- | --- | --- |
| Containing shapes | `BlockedL.replace_lower`, `BlockedR.replace_lower` | Arbitrary D and replacement; proper address and actual same-side lower contraction. |
| Complete eligible-site correspondence | `ReducibleL/R.outside_iff`, `new_site`, `outside_or_same` | Typed actual suffixes, inserted root, strict containing exclusion, positional uniqueness. |
| Finite descent | `EligibleSites.left/right`, `ReducibleL/R.rank_replacement`, `FiniteRank.descent_wf` | R_old permutes to r::O; R_new to I++O; every I rank is less than r. |
| §11.2 printed p.253 Blocked-w | `blocked_normalization_left/right`, `blocked_w_premises`, `blocked_w` | Actual cut-free witnesses and Reduced equality; no coherence or supplied normalization input. |
| Atomization boundary | `AtomizationBlockedBoundary.before_blocked`, `atomize_not_blocked` | Existing atomize does not preserve the needed blocked predicate. |

The completed `ba5af8b` run was checked in the
[source/evidence review](reviews/GENTZEN_BA5AF8B_REVIEW.md) and
[writing review](reviews/GENTZEN_BA5AF8B_WRITING.md). The
[successor instruction](CODEX_AFTER_BA5AF8B_CLEAN_CUTS.txt) specifies a proposed
route construction with atomic omissions, atomized local repair witnesses,
and preservation of atomization during the existing finite descent. These
are open proof obligations; this documentation pass adds no Lean theorem.

## Retained earlier checkpoints

All sections below describe their own earlier source/evidence snapshots and
are superseded by the current checkpoint above wherever their open statuses differ.

## Historical full Reducibility checkpoint (26 October 2026)

Both `DosenPetric.Reduced.Gentzen.reducibility_left` and
`reducibility_right` compile for arbitrary P, contexts, proofs and selected
positions, with the unchanged complete `ReducesL/R` conclusions. No Binary or
Unary premise, caller reduct/decomposition, coherence or reflection assumption.
The source-terminal one-premise W6 packages, unrestricted exchange and every
remaining unary/basis input are internally covered. Outside transport for all
incomparable addresses preserves actual proof values, paths, ancestry and
whole-formula cluster membership.

Checked: **398 Lean files / 10,606 audited project declarations**. Only propext,
Quot.sound and Classical.choice are permitted. Strict build, exact public types,
all five negative controls, import closure and manuscript checksums passed.
Exact hypotheses, commands, hashes, construction and limitations:
[GENTZEN_FULL_REDUCIBILITY_REPORT.md](GENTZEN_FULL_REDUCIBILITY_REPORT.md),
[author-side hostile review](reviews/GENTZEN_FULL_REDUCIBILITY_HOSTILE.md),
[author-side writing review](reviews/GENTZEN_FULL_REDUCIBILITY_WRITING.md).
Evidence: `provenance/wsl-gentzen-full-reducibility/`.

The next missing result is preservation of a blocked contraction containing a
proper lower-contraction replacement, on each side. Outside cluster transport
alone does not preserve the entire Reducible predicate. Finite multiset descent,
Blocked-w, clean-cut/cut elimination, positive/reduced/Boolean coherence, actual
instances/maximality, model corollary and the entire v6 appendix ledger remain
open. Generic routing repairs preserve CutFree; no general Atomized witness is
claimed. All accepted corrections and the full-paper contract remain active.

| Source anchor | Current correspondence |
| --- | --- |
| §11.2 p.250 Lemma, p.252 dual | Full ReducesL/R exports, with every addressed rebuilt eligible descendant. |
| p.251 W1–W3 | Typed selected-fiber factor replaces the cited Semilattice Coherence calculation; all categorical squares proved by existing component universal properties. |
| p.251 W4 / p.252 dual | Fixed-principal component naturality; selected-principal source repair, explicit exchanges, singleton-aware inner operations. |
| p.252 W6 and `(dL nat)` | TerminalOne first/second source packages; old S+3k+3, repair S+δ(k)+6, actual blocked source middle. |
| p.253 corollary | Blocked-w still requires containing transport and a proved finite descent; it is not inferred from the local theorem alone. |

Source hash remains e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
No new equation, syntax constructor, rank definition or coherence instance.

## Retained historical records

The following snapshots describe their own earlier commits; open-status text
below is historical and is superseded by the current checkpoint above.

Latest upstream integration (edb86cb): retain the author's division of work,
correction procedure and tagged-substitution requirements. The new W6 analysis
is an instruction at its historical source anchor. The two-premise terminal-
source left family and all native binary producers compile here; the general
one-premise terminal-source left displayed families/ranks in its §3 remain
open as separately specified source constructions. Native one-premise repairs
and source singleton blockedness exclusions do not discharge those exact
source-rank statements. See the current continuation. No manuscript defect or
completed full-paper proof is inferred.

Upstream integration: accepted commits 0af6a0e, 810dcdb and e4f2f0b after
the checked proof commit f4bc6ff. They add manuscript v6 and the full-paper
contract, with no Lean-source changes. The current manuscript is v6; upstream
v5/v6 files are retained byte-for-byte, and v4 remains preserved. Both full
Reducibility and the broader v6 contract remain incomplete. The supplied
1e967bc instruction remains the exact immediate proof target.

## Historical binary-input integration (25 October 2026)

**Both full Reducibility Lemmata remain open.** Every actual contraction over
native `mix`, `conjR` or `disjL` now has a left and a right producer, with internal
positional selection matching and the complete eligible-descendant bound.
`BinaryReducer.left/right` assemble these cases; a binary cut premise is ruled
out by the cut-freeness already contained in reducibility. The right-W4 repair
now includes one parametric copy plus the fresh compound, using a node-free
singleton inner operation. Source W6, native/source repairs and all three
source singleton blockedness exclusions compile. General unary dispatch,
including exchanges crossing selected copies, is still missing. Outside-site
transport, multiset descent, Blocked-w, cut elimination and coherence remain open.

Measured checked sources: **330 Lean source files / 9,737 audited project
declarations** (818 additional audited declarations, including generated
helpers; this is not a count of new mathematical theorems). Exact results:
[GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md](GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md),
[author-side hostile review](reviews/GENTZEN_REDUCIBILITY_INTEGRATION_HOSTILE.md),
[author-side writing review](reviews/GENTZEN_REDUCIBILITY_INTEGRATION_WRITING.md).
The governing instruction is [CODEX_AFTER_1E967BC_REDUCIBILITY.txt](CODEX_AFTER_1E967BC_REDUCIBILITY.txt).
This checked integration does **not** complete that instruction's final target.

| Source | Published construction | Lean correspondence and qualification |
| --- | --- | --- |
| §11.2 pp.248–250 | Whole-formula clusters, all-node rank, tied/blocked/reducible contractions, Reducibility statement | Existing `rho`, `ReducibleL/R`, fourteen blocked frames and entry uniqueness are reused unchanged. |
| p.251 W1 | Parametric unary commutations, including exchange absorption | Opposite-side families have full adapters; arbitrary crossing/multigap/absorption exchange dispatch is still open. No Semilattice Coherence assumption is imported. |
| p.251 W4; p.252 right analogue | Contract parametric compounds before logical introduction and use a blocked middle | `W4.NonemptyRight`; n counts parametric copies, and the fresh compound is an additional selected copy. |
| pp.251–252 W5, `(m nat)` | One-branch or two-branch contraction through mix | Internal `Split`, lower-context/old-proof comparison, `MixReducer.left/right`. |
| p.252 paragraphs following W5, `(w γ 2)`, `(w γ 3)`, `(dL nat)` | Binary conjunction and disjunction W5 | `ConjunctionReducer` / `DisjunctionReducer`; actual `Rules.conjRight`, `Rules.disjLeft`, sourceConj/mixedDisj naturality and product/coproduct component laws. |
| p.252 W6, `(w ∨ 1–3)` | Parametric copies in one/both premises plus a fresh disjunction; blocked source middle | Source uses terminal `disjLLast`, with explicit head/input/output exchanges. `SourceLeft`, `NativeLeft`, `OneHeadDisjunction`, separately typed `HeadRight`, and internally matched native dispatch. |
| p.252, final right-analogue paragraph | Right Reducibility construction | Implemented independently with coproduct variance; no contravariant arrow-negation operation is assumed. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants and atomic-zero extension | Existing leaves, empty contexts, syntax/equations and witnessed-zero policy are preserved. No new generator or special empty-sequent leaf. |


## Historical follow-up at 1e967bc (superseded above)

The [concrete W6 instruction](CODEX_W6_CONSTRUCTION.md) now specifies six
left/right selected-principal constructions, their rank targets and complete
addressed conclusions. It derives separate targets for the actual left
`disjLLast` macro and native right `conjR`; it supplies no new checked Lean
correspondence. Implementation, general dispatch and native/source-macro
transport remain open. See its [hostile audit](reviews/W6_CONSTRUCTION_HOSTILE.md)
and [writing review](reviews/W6_CONSTRUCTION_WRITING.md).

**Both full Reducibility Lemmata remain open.** From the unchanged ReducibleL/R
hypotheses, cut-entry uniqueness now compiles via all fourteen actual blocked
premise frames and a typed first-separation argument. Arbitrary-address left W4
no longer requires InjectiveAscend. The repaired right W4, including two copies,
now proves equality, cut-freeness and the complete eligible-descendant bound.
The old terminal right candidate has a compiled reducible-root rank-tie regression.
Mixed-premise mix W5 now has both addressed descendant theorems for constructed
chained selections, including singleton branches and independent multiplicities.
Native binary logical context-route comparisons are proved; logical W5/W6
producers, arbitrary selection/profile dispatch and remaining macro/primitive
comparisons are not. Blocked-w, cut elimination and coherence remain open.

See [the exact follow-up report](GENTZEN_REDUCIBILITY_FOLLOWUP_REPORT.md),
[author-side hostile review](reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_HOSTILE.md),
and [writing review](reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_WRITING.md).
The governing task is [the supplied continuation](CODEX_AFTER_05C6BC8_REDUCIBILITY.txt),
with the unchanged full targets in CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt.
This is verified progress, not completion of that task. Final sources:
**249 Lean files / 8,919 audited declarations**. Earlier checkpoint
sections below retain their historical scope and are superseded where necessary.


This map concerns Došen and Petrić, *Proof-Theoretical Coherence*, September
2007 revision, [author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
The downloaded PDF has SHA-256
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
All page numbers below are printed pages. The corresponding zero-based PDF
page index is the printed number plus 11 (the one-based PDF page number is the printed number plus 12).
The source PDF and extracted text are local consultation evidence, not
redistributed as repository source.

## Retained Reducibility correspondence: verified partial follow-up

The governing endpoint remains both full Reducibility Lemmata in
[the active instruction](CODEX_AFTER_05C6BC8_REDUCIBILITY.txt).
See [the follow-up report](GENTZEN_REDUCIBILITY_FOLLOWUP_REPORT.md) and
[hostile](reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_HOSTILE.md)/[writing](reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_WRITING.md) author-side reviews.

| Source §11.2 (printed pages) | Proved bridge | Exact limitation |
| --- | --- | --- |
| 248–249 clusters and rank; 250 blocked ancestors | Typed first separation, fourteen actual premise frames, ReducibleL/R.entry_unique | Uniqueness is over the distinguished cut entry, not global address injectivity. |
| 251 W4 | Arbitrary-address left W4 has its full eligible-descendant bound from ReducibleL alone | Terminal selected-conjunction family; no exhaustive producer dispatch. |
| 252 right analogue | Explicit two-copy candidate-failure test; repaired head W4 has equality, stage ranks and full addressed descendant bound | Repaired root is L+5 and need not decrease. The proved path argument bounds eligible contractions by L. |
| 252 mixed mix W5 | Arbitrary nonempty p/q chained selections give both Reduced equalities, actual gammaMix blockedness, independent rank sums and addressed descendant bounds | Singleton branches included. Extracting every original profile into these actual input shapes remains separate. |
| 252 logical W5/W6 | Native conjunction-right antecedent-route and disjunction-left succedent-route comparisons | Full logical producers, selected principals and source-macro ancestry/rank transports remain open. |
| 250 (w∨3), 252 W6 | Native freshBoth remains a compiled unblocked example despite its selectedBoth profile | A profile is not blockedness or certified dispatch. |
| 253 Blocked-w | Existing address/cluster/replacement transport and local descendant bounds | Both complete producers, outside-site transport and finite multiset induction remain open. |

No source anchor supplies an assumed coherence proof. Generating equations,
blockedness, reducibility and ranks are unchanged. The previous correspondence
and access history remain available in the historical reports and Git history.

## Objects and arrow grammar

`Formula P` is the source language with variables, top, bottom, conjunction,
disjunction, and negation. `Presentation.Term P A B` is indexed by both
endpoints. `comp f g` applies f and then g, hence represents the book's
`g ∘ f`. The interpretation uses the existing `Formula.Occ`; both binary
connectives have disjoint tagged occurrence sets, constants have empty sets,
and negation preserves the underlying positions. Repeated letters retain
different position tags.

| Source anchor | Source family / operation | Lean constructor or definition | Status / convention |
| --- | --- | --- | --- |
| §§2.7–2.8; §14.2, pp.316–317 | identities and composition | `Term.id`, `Term.comp` | Primitive identity family and binary arrow operation. |
| §§2.7–2.8; §14.2, p.316 | bifunctorial ∧, ∨ on arrows | `Term.tensor .conj`, `.disj` | The only other primitive arrow operations; negation on arrows is derived in the source. |
| §4.4 and §6.2; equation lists pp.332–333 | b in both directions | `Term.assocR`, `Term.assocL` for each `Op` | `assocR` has type A ξ (B ξ C) → (A ξ B) ξ C. |
| §5.1, p.107; §6.3–6.4, p.121 | symmetries | `Term.swap` | `swap .conj A B` is c∧_(A,B); `swap .disj A B` is c∨_(B,A). |
| §9.1, pp.185–186; §9.4; §9.6, p.207 | w-k | `Term.diag`, `codiag`, `fst`, `snd`, `inl`, `inr` | Primitive families; product/coproduct universal properties are derived. |
| §4.6, p.101; §6.4 and §9.6 | δ-σ | `Term.rightOut`, `rightIn`, `leftOut`, `leftIn` | Each `Op` has its own unit, top for conjunction and bottom for disjunction. |
| §8.2 and §8.4; §14.2 | mix | `Term.mix` | Primitive family A ∧ B → A ∨ B. |
| §7.2, p.132; §7.6, p.145; §11.1, p.234 | d = dL | `Term.dist` | Primitive A ∧ (B ∨ C) → (A ∧ B) ∨ C. |
| §12.5, pp.287–288; §14.2 | 0_A | `Term.zero` | Original primitive endomorphism; no primitive arrow for every pair of objects. |
| §14.1, p.310 | n→, n← | `Term.dnOut`, `dnIn` | Primitive mutually inverse arrows. |
| §14.1, p.310 | r∧→, r∧←, r∨→, r∨← | `Term.dmConjOut`, `dmConjIn`, `dmDisjOut`, `dmDisjIn` | Primitive De Morgan comparisons. |
| §14.1, p.312 | ρ∧→, ρ∧←, ρ∨→, ρ∨← | `Term.negTopOut`, `negTopIn`, `negBotOut`, `negBotIn` | Primitive constant comparisons. |
| §14.2, p.316 | η_A, ε_A | `Term.excludedMiddle`, `contradiction` | Primitive families; no guessed naturality equations. |
| §9.1, p.187; §9.4, p.198 | pairing and copairing | `Term.pair`, `copair`; quotient `pair`, `copair` | Derived using w and tensor. |
| §9.2, p.191; §9.6, p.207 | κ to top / from bottom | `Term.toTop`, `fromBot` | Derived from δ and k; uniqueness is proved in `CartesianFromDiagonal`. |
| §7.6, p.145, `(dR c)` | right dissociativity | `Term.distRight` | Derived, expanded in equation schemas; no extra primitive constructor. |
| §9.1, p.186, c-m; dual list p.336 | medial arrows | `Term.medial` | Derived associator/symmetry composite; the disjunctive dual has permuted arguments. |
| §14.2, p.317, `(0ηε)` | zero from η, ε and d | `Term.zeroConstruction`, `zeroConstruction_eq`, `zeroIdentity` | Construction is proved equal to primitive zero in the equation quotient. |
| §14.1, pp.311,315–316; §14.2 | negation on arbitrary arrows | No arrow-negation function yet | Derived, not primitive; definition and proof of independence of representatives remain open. |

## Generating equations and closure

The source inheritance is E(B) = E(ZIDL_top,bottom) ∪ E(I^neg_top,bottom)
(p.317), with E(ZIDL) obtained by adding `(0I)` (pp.288–291).
E(DL_top,bottom) is E(DL) ∪ E(L_top,bottom) **minus** `(m e∧)` and
`(m e∨)` (§11.5, p.270). Those two equations are not generators here.
The right-d equations are retained after expanding dR by `(dR c)`; the
source explicitly permits this eliminable abbreviation (p.145).

`Equation` has 71 Lean constructors. A constructor parameterized by `Op`
represents both connective schemas, so 71 is not a count of individual
source equation instances. Each row below identifies the constructor and
its quotient theorem `Presentation.Laws.<name>`; the exact typed equation
is in `PresentationEquations.lean`. The quotient theorems allow arbitrary
classes as arrow parameters, by induction on representatives.

| Source equation / printed page | `Equation` constructor and `Laws` theorem |
| --- | --- |
| (cat 1), p.332 | `id_comp` |
| (cat 1), p.332 | `comp_id` |
| (cat 2), p.332 | `assoc` |
| (xi 1), p.332 | `tensor_id` |
| (xi 2), p.332 | `tensor_comp` |
| (bR nat), p.332 | `assocR_nat` |
| (bL nat), p.332 | `assocL_nat` |
| (b b), p.333 | `assocR_L` |
| (b b), p.333 | `assocL_R` |
| (b 5), p.89; list p.333 | `pentagon` |
| (c nat), p.333; disjunctive indices reversed | `swap_nat` |
| (c c), p.107; list p.334 | `swap_swap` |
| (b c), p.107; list p.334 | `hexagon` |
| (delta/sigma nat), pp.332–333 | `rightOut_nat` |
| (delta/sigma nat), pp.332–333 | `rightIn_nat` |
| (delta delta)/(sigma sigma), p.101 | `rightOut_In` |
| (delta delta)/(sigma sigma), p.101 | `rightIn_Out` |
| (delta/sigma nat), pp.332–333 | `leftOut_nat` |
| (delta/sigma nat), pp.332–333 | `leftIn_nat` |
| (delta delta)/(sigma sigma), p.101 | `leftOut_In` |
| (delta delta)/(sigma sigma), p.101 | `leftIn_Out` |
| (b delta sigma), p.101 | `triangle` |
| (w nat), p.333 | `diag_nat` |
| (w nat), p.333 | `codiag_nat` |
| (k1 nat), p.333 | `fst_nat` |
| (k1 nat), p.333; disjunctive indices translated | `inl_nat` |
| (k2 nat), p.333 | `snd_nat` |
| (k2 nat), p.333; disjunctive indices translated | `inr_nat` |
| (b w), p.186 | `diag_assoc` |
| (b w), dual p.186; list p.336 | `codiag_assoc` |
| (c w), p.186 | `diag_swap` |
| (c w), dual p.186; list p.336 | `codiag_swap` |
| (b c w), p.186 | `diag_tensor` |
| (b c w), dual p.186; list p.336 | `codiag_tensor` |
| (b k), p.186 | `fst_assoc` |
| (b k), dual p.186; list p.336 | `inl_assoc` |
| (c k), p.186 | `snd_swap` |
| (c k), dual p.186; list p.336 | `inr_swap` |
| (w k), p.186 | `diag_fst` |
| (w k), dual p.186; list p.336 | `inl_codiag` |
| (w k), p.186 | `diag_snd` |
| (w k), dual p.186; list p.336 | `inr_codiag` |
| (k delta), p.191 | `fst_top` |
| (k delta), dual p.191; list p.338 | `inl_bot` |
| (c bottom)/(c top), p.121, inherited by p.207 | `constant_swap` |
| (dL nat), p.333 | `dist_nat` |
| (dR nat), p.333, dR defined by p.145 | `distRight_nat` |
| (dL and), p.132 | `dist_conj` |
| (dL or), p.132 | `dist_disj` |
| (dR and), p.132 | `distRight_conj` |
| (dR or), p.132 | `distRight_disj` |
| (d b and), p.132 | `dist_b_conj` |
| (d b or), p.132 | `dist_b_disj` |
| (m nat), p.333 | `mix_nat` |
| (b m), section 8.2; list p.336 | `mix_assoc` |
| (c m), section 8.4; list p.336 | `mix_swap` |
| (w m), p.219 | `diag_mix_codiag` |
| (d k and), p.234 | `dist_snd` |
| (d k or), p.234 | `dist_inl` |
| (d m), p.234 | `dist_mix` |
| (0I), p.288, inherited p.317 | `zero_law` |
| n-r/rho isomorphism equations, pp.310,312 | `dnOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `dnOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `dmConjOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `dmConjOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `dmDisjOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `dmDisjOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `negTopOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `negTopOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `negBotOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `negBotOut_out` |

`Derives` is equivalence closure plus congruence for composition and the two
tensors, with injections of these 71 schemas. This is syntactic generated
equality. `Term.subst`, `Equation.subst`, and `Derives.subst` prove the
source substitution rule `(su)` admissible, including endpoint substitution
and the positive-letterless side condition. No relation-kernel equality is a
generator. Closure under each primitive arrow operation therefore descends
to `Hom`; derived operations are composites of descended operations.

The following source consequences are **not** inserted as generators:
`(w k k)` (p.187), terminal/initial uniqueness (pp.191,207), `(b δ)`,
`(b σ)`, `(δ σ)` (p.101), `(c δ σ)` (§5.3), `(0I ξ)` (p.288),
`(0ηε)` (p.317), arbitrary-arrow negation, and the naturality of n-r
obtained by coherence (p.316). The universal properties and `(0ηε)` are
proved here; the other consequences are not all supplied as named lemmas.
The positive-letterless condition in `Constant` means precisely the language
in the source side condition on p.121; it excludes variables and negation.

## Occurrence assignment

The assignment is the tagged-coordinate version of the source functor G to
relations (introduced in §2.7 and extended in §§14.1–14.2; η/ε are assigned
empty relations on p.317). It has the following explicit Lean realization.
The equality-preservation proof is separate from this definition.

| Constructor / derived operation | Relation in `Term.relation` or quotient declaration |
| --- | --- |
| identity, composition | `Relations.graph id`, `Relations.comp` |
| either tensor | `Relations.sumMap` on the two component relations |
| `assocR`, `assocL` | graphs of `Relations.reassoc`, `Occurrence.unassoc` |
| `swap` | graph of `Occurrence.exchange` |
| `diag`, `codiag` | `Relations.pair` / `copair` of two identity graphs |
| `fst`, `snd`; `inl`, `inr` | `Relations.fstRel`, `sndRel`; graphs of `Sum.inl`, `Sum.inr` |
| `rightOut`, `leftOut`; `rightIn`, `leftIn` | graphs of `Occurrence.dropRight`, `dropLeft`; graphs of `Sum.inl`, `Sum.inr`; unit positions are Empty |
| `mix`, n/r/rho comparisons | identity graphs on their definitionally matching position types |
| `dist`; derived `distRight` | graphs of reassociation / inverse reassociation; the latter is proved in `Term.relation_distRight` |
| primitive and constructed zero | empty relation; quotient `occurrence_zero` uses `zeroConstruction_eq` |
| η, ε | empty relations; `occurrence_excludedMiddle`, `occurrence_contradiction` |
| derived pairing/copairing | relation pairing/copairing, proved by `occurrence_pair`, `occurrence_copair` |
| derived arrows to top / from bottom | empty relations, proved by `occurrence_toTop`, `occurrence_fromBot` |

## Quotient and interpretation boundary

`Hom A B` is `Quotient (termSetoid A B)` where the setoid relation is
`Derives`, not equality of interpreted relations. `comp` and `tensor` use
`Quotient.liftOn₂` and their explicit congruence proofs. `category` proves
the category laws from `Laws`. `operations` derives the entire `Structure`
interface from the published equations, using the generic diagonal argument
in `CartesianFromDiagonal`. `zeroIdentity` uses the constructed zero.

The historical presentation report records the occurrence equations and
operation-preservation laws, keeping well-definedness distinct from
faithfulness. The normalization construction below now supplies manuscript
§3 object normal forms, both inverse comparisons, and their occurrence
correspondence. Boolean Coherence (§14.2, conclusion p.321) is now proved by
Presentation.coherence through actual positive/reduced coherence. The original
quotient remains generated equational equality; it is not redefined as relation equality.
Presentation.interpretation supplies the full intended faithful interface. Full
source congruence/substitution correspondence and maximality remain continuing duties.


## Actual normalization comparisons (current checkpoint)

`Presentation.normalization P` instantiates the existing `Normalization` record
for every `P : Type u`. It constructs the object assignment and comparison
isomorphisms on printed pp.313–314. It does not claim the complete source
functor F, its naturality, the p.314 Auxiliary Lemma, or the equivalence.
The following are derived arrows, not additional primitive operations or
new generating equations. `NN` denotes `Presentation.NegationNormalization`
and `NC` denotes `Presentation.NormalComparison` in this table.

| Source anchor / zero-based PDF page | Typed comparison and available equations | Lean construction / status |
| --- | --- | --- |
| §14.1 p.310 / 321, n displays | n→ : ¬¬A → A and reverse n←; both inverse displays | `NC.doubleNeg`, using existing `dnOut/dnIn` and `Laws.dnOut_in/out`. |
| p.310 / 321, r∧ displays | r∧→ : ¬(A∧B) → ¬A∨¬B and reverse; both inverse displays | `NC.deMorganConj`, using `Laws.dmConjOut_in/out`. |
| p.310 / 321, r∨ displays | r∨→ : ¬(A∨B) → ¬A∧¬B and reverse; both inverse displays | `NC.deMorganDisj`, using `Laws.dmDisjOut_in/out`. |
| p.312 / 323, rho displays | ρ∧→ : ¬top → bot and ρ∨→ : ¬bot → top, their reverses, both inverse displays | `NC.negTop/negBot`, using `Laws.negTopOut_in/out` and `negBotOut_in/out`. |
| p.313 / 324, F on objects | Negation only at signed variable leaves; constants retained/swapped as appropriate | `NN.form A false` normalizes A, `form A true` normalizes ¬A; structural recursion on A. |
| p.313 / 324, i_A and i_A^-1 clauses | Variable and negative variable identities; connective tensors; i_¬¬A = i_A ∘ n→; negative connective via r→ then tensor negative comparisons; inverses reverse the order | `NN.comparison`, with `NC.refl/trans/conj/disj`; arrows and inverse proofs are built simultaneously. |
| p.314 / 325, constant clauses and following identities | Constants use identities, negative constants use ρ→/ρ←; i_A^-1 ∘ i_A = 1_A and i_A ∘ i_A^-1 = 1_FA | `NN.forward/backward`, `forward_backward/backward_forward`, `Presentation.normalization`. Inverses use only existing category, tensor, and comparison equations. |
| p.314 / 325, G clauses | G negA = GA and comparison images are identity relations | `NN.toOcc/fromOcc`, inverse coordinate laws, `forward_graph/backward_graph`. In tagged coordinates tensors use Sum.map, so distinct occurrences stay distinct. |
| Manuscript §3, relation transport | Normal-form transport uses backward_A, f, forward_B | `NN.transport_relation/transport_apply/transport_coordinates`; categorical recovery/injectivity reuse the old `Normalization` lemmas. |

For each Out : X → Y and In : Y → X above, the source's unnumbered displays
are In ∘ Out = 1_X and Out ∘ In = 1_Y. The Lean equations are
`comp Out In = id X` and `comp In Out = id Y`. No extra equation labels are
invented. The inverse proofs do not compare relations to conclude equality.

`Formula.signedLabel` records the letter and parity along a tagged occurrence
path; it agrees with `NormalForm.literalAt` on normal forms. The coordinate
maps preserve this full literal in both directions. Constants have Empty
occurrences, handled by empty elimination; `NN.no_occ` covers any empty source
occurrence type, and `repeated_negative_tags` checks distinct negative repeats.
This comparison statement is not signed-label preservation along every arrow.

The n/r naturality consequences discussed on pp.311/316, rho naturality,
derived contravariant arrow negation, and the p.314 Auxiliary Lemma/equivalence
remain unproved. No such consequence has been added to `Equation` to complete
this construction. The raw occurrence preservation proof and its quotient
well-definedness were reused unchanged. Full Boolean Coherence remains open.
See [the normalization report](NORMALIZATION_REPORT.md) for exact hypotheses,
declarations, verification, evidence hashes, and both review boundaries.


## Global signed-edge invariant (current checkpoint)

`Presentation.Term.relation_signedLabel` proves the complete literal invariant
by induction on all 31 primitive constructor schemas in `Term`. The parameters
are arbitrary P, formulas A,B, term t : A → B, positions x,y, and an edge.
There is no nonemptiness, decidable-equality, or coherence premise.

| Source grammar / interpretation anchor | New proof correspondence |
| --- | --- |
| §2.7, §14.2 p.316: id, composition, both tensors | Equal position; intermediate occurrence and transitivity; matching Sum branches and child invariants. |
| b,c,w-k,delta/sigma,m,d families indexed above | Graph equalities and branch decomposition retain the signed subformula label. Unit branches are Empty; diagonals and codiagonals copy/merge without identifying tags. |
| §14.1 p.310 and G clause p.314: n/r | Both double-negation directions use `Literal.flip_flip`; all four De Morgan cases preserve the flipped child label on each branch. |
| p.312 and G clause p.314: rho | Empty occurrence endpoints; no chosen dummy coordinate. |
| §12.5 and §14.2 pp.316–317: 0,eta,epsilon | Empty assigned relations, hence no edge to check. |
| Existing generated-equation quotient | `occurrence_signedLabel` uses quotient induction and `occurrence_ofTerm`; no equation or definition of equality changes. |
| Manuscript v4 §3 signed-literal paragraph | `occurrence_literal` specializes through `signedLabel_eq_literalAt`; letter/polarity and both opposite-sign exclusions follow. |
| Existing normalizer coordinate theorems | `NegationNormalization.transport_literal/transport_literal_coordinates` use `transport_apply`, `literal_fromOcc`, and `transport_coordinates`. |

This direct invariant does not rely on the source's unconstructed signed-literal
equivalence. It proves a property of the well-defined occurrenceMap, not its
faithfulness. `diag_copies` and `codiag_merges` exhibit edges between repeated
letters and distinct tags, so neither functionality nor injectivity of each
relation follows. The unchanged `SignedLabelPreservation` definition still
requires a separately supplied faithful interpretation. See
[the signed-label report](SIGNED_LABEL_REPORT.md) and both linked reviews.


## Signed-literal syntactic reduction (current checkpoint)

Source §14.2 p.318 (one-based PDF p.330) defines C with normal-form objects,
positive structural families and zero endomorphisms, plus only atomic eta_p
and epsilon_p. Reduced.Term has 21 constructor schemas. Arbitrary eta/epsilon
and n/r/rho are not reduced constructors. Equation has exactly the 61 inherited
positive ZIDL schemas; Derives is their equivalence/operation congruence closure.
Reduced.Hom is the quotient by Derives, independent of inclusion or relations.

The schema correspondence is exact by name; source anchors below are inherited
from the earlier positive equation index. Op packages both connectives. The
constant side condition excludes all literal leaves. No extra atomic eta/epsilon
or (0eta-epsilon) equation is inserted, and the two source-omitted (m e) laws
remain omitted. Equation.toFull and Derives.toFull compile for every schema.

| Source anchor | Reduced.Equation and matching Presentation.Equation |
| --- | --- |
| (cat 1), p.332 | `id_comp` |
| (cat 1), p.332 | `comp_id` |
| (cat 2), p.332 | `assoc` |
| (xi 1), p.332 | `tensor_id` |
| (xi 2), p.332 | `tensor_comp` |
| (bR nat), p.332 | `assocR_nat` |
| (bL nat), p.332 | `assocL_nat` |
| (b b), p.333 | `assocR_L` |
| (b b), p.333 | `assocL_R` |
| (b 5), p.89; list p.333 | `pentagon` |
| (c nat), p.333; disjunctive indices reversed | `swap_nat` |
| (c c), p.107; list p.334 | `swap_swap` |
| (b c), p.107; list p.334 | `hexagon` |
| (delta/sigma nat), pp.332–333 | `rightOut_nat` |
| (delta/sigma nat), pp.332–333 | `rightIn_nat` |
| (delta delta)/(sigma sigma), p.101 | `rightOut_In` |
| (delta delta)/(sigma sigma), p.101 | `rightIn_Out` |
| (delta/sigma nat), pp.332–333 | `leftOut_nat` |
| (delta/sigma nat), pp.332–333 | `leftIn_nat` |
| (delta delta)/(sigma sigma), p.101 | `leftOut_In` |
| (delta delta)/(sigma sigma), p.101 | `leftIn_Out` |
| (b delta sigma), p.101 | `triangle` |
| (w nat), p.333 | `diag_nat` |
| (w nat), p.333 | `codiag_nat` |
| (k1 nat), p.333 | `fst_nat` |
| (k1 nat), p.333; disjunctive indices translated | `inl_nat` |
| (k2 nat), p.333 | `snd_nat` |
| (k2 nat), p.333; disjunctive indices translated | `inr_nat` |
| (b w), p.186 | `diag_assoc` |
| (b w), dual p.186; list p.336 | `codiag_assoc` |
| (c w), p.186 | `diag_swap` |
| (c w), dual p.186; list p.336 | `codiag_swap` |
| (b c w), p.186 | `diag_tensor` |
| (b c w), dual p.186; list p.336 | `codiag_tensor` |
| (b k), p.186 | `fst_assoc` |
| (b k), dual p.186; list p.336 | `inl_assoc` |
| (c k), p.186 | `snd_swap` |
| (c k), dual p.186; list p.336 | `inr_swap` |
| (w k), p.186 | `diag_fst` |
| (w k), dual p.186; list p.336 | `inl_codiag` |
| (w k), p.186 | `diag_snd` |
| (w k), dual p.186; list p.336 | `inr_codiag` |
| (k delta), p.191 | `fst_top` |
| (k delta), dual p.191; list p.338 | `inl_bot` |
| (c bottom)/(c top), p.121, inherited by p.207 | `constant_swap` |
| (dL nat), p.333 | `dist_nat` |
| (dR nat), p.333, dR defined by p.145 | `distRight_nat` |
| (dL and), p.132 | `dist_conj` |
| (dL or), p.132 | `dist_disj` |
| (dR and), p.132 | `distRight_conj` |
| (dR or), p.132 | `distRight_disj` |
| (d b and), p.132 | `dist_b_conj` |
| (d b or), p.132 | `dist_b_disj` |
| (m nat), p.333 | `mix_nat` |
| (b m), section 8.2; list p.336 | `mix_assoc` |
| (c m), section 8.4; list p.336 | `mix_swap` |
| (w m), p.219 | `diag_mix_codiag` |
| (d k and), p.234 | `dist_snd` |
| (d k or), p.234 | `dist_inl` |
| (d m), p.234 | `dist_mix` |
| (0I), p.288, inherited p.317 | `zero_law` |

| Source / result | Lean correspondence and scope |
| --- | --- |
| §14.1 pp.313–314 | NormalForm.dual/dual_dual; form_true/normal_formula/normal_neg_formula; forward_formula/backward_formula after endpoint casts, and transport_formula. |
| p.317 eta/epsilon connective and constant displays | Term.etaNF/epsilonNF use atomic primitives, symmetry for negative literals, both constant units, and the explicitly typed mixedDisj/mixedConj composites. These are not the same-connective medial. No general equality with a particular e'-abbreviation is claimed. |
| p.317 zero-arrow argument | Compatibility.etaNF/epsilonNF, using fromTop_unique/toBot_unique from actual category/zero laws, not relational faithfulness. |
| p.318 C syntax included into B | Term.toFull, Equation.toFull, Derives.toFull, inclusion and its identity/composition/tensor preservation. |
| Normalization transport on every full constructor | red and red_sound cover all 31 full constructor schemas; structural naturality, comparison inverses, zero_law and compound witnesses suffice. |
| Full normal-form hom-sets | representation proves every existing full arrow is inclusion of a reduced quotient arrow. It does not prove equality reflection or a quotient-level red function. |
| Source G on C and normalization coordinates | Independent Term.relation; relation_toFull, occurrence_inclusion, occurrence_red, Coordinates.red_apply/red_coordinates. All occurrence tags are retained. |
| Coherence transfer | normal_faithful_of_reduced/global_faithful_of_reduced are explicitly conditional on Reduced.Faithful P. No proof/axiom/instance for that premise is supplied. |

The contextual g-eta/g-epsilon maps and factorizations on pp.318–320 are now
proved below, with direct reduced derivations of their needed structural
instances. Common atomic factorization and complete support are also proved.
General Distributive Dicartesian Coherence (§11.5) remains unformalized, and
the §12.5 coherence input on p.321 is now isolated as PositiveCoherence P.
The p.314 equivalence, derived contravariant negation and its laws remain
separate obligations.
See [the reduction report](SIGNED_LITERAL_REDUCTION_REPORT.md) and both reviews.

## Contextual factorizations in the reduced syntactic category

The September 2007 source, §14.2 printed pp.318–321 (one-based PDF
pp.330–333), selects one occurrence, rather than every equal subformula.
`Reduced.Context P` records that position by a hole and left/right binary
placements, each indexed by `Reduced.Op`. Fixed formulas are arbitrary
NormalForm P objects. Thus the two placements and two Op cases give exactly
four recursive cases. `plug` replaces only the distinguished hole.

Write X = K[top], Y = K[bot], E_p = neg p ∨ pos p, and
D_q = pos q ∧ neg q. Here pos/neg denote complete signed literal leaves.
For the following tables `aR_o = assocR o`, `aL_o = assocL o`,
`c_o = swap o`, `d = dist`, and `dR = Term.distRight` (the derived arrow
of (dR c), p.145). Each semicolon means execute the left arrow first.
The source writes these paths in reverse order using ◦. Subscripts name
actual source/target summands; source disjunctive symmetry indices follow
Table 2, p.49 and are reversed relative to the Lean swap argument convention.

| Source recursion | Typed path defining `Context.gConj` |
| --- | --- |
| p.318, hole | `top ∧ B --leftOut conj B--> B` |
| p.318, C ∧ K | `(C ∧ X) ∧ B --aL_conj--> C ∧ (X ∧ B) --(id C ∧ gConj K B)--> C ∧ K[B]` |
| p.318, K ∧ C | `(X ∧ C) ∧ B --c_conj--> B ∧ (X ∧ C) --aR_conj--> (B ∧ X) ∧ C --(c_conj B X ∧ id C)--> (X ∧ B) ∧ C --(gConj K B ∧ id C)--> K[B] ∧ C` |
| p.318, C ∨ K | `(C ∨ X) ∧ B --dR C X B--> C ∨ (X ∧ B) --(id C ∨ gConj K B)--> C ∨ K[B]` |
| p.319, K ∨ C | `(X ∨ C) ∧ B --c_conj--> B ∧ (X ∨ C) --d B X C--> (B ∧ X) ∨ C --(c_conj B X ∨ id C)--> (X ∧ B) ∨ C --(gConj K B ∨ id C)--> K[B] ∨ C` |

| Source recursion, p.319 | Typed path defining `Context.gDisj` |
| --- | --- |
| hole | `B --leftIn disj B--> bot ∨ B` |
| C ∨ K | `C ∨ K[B] --(id C ∨ gDisj K B)--> C ∨ (Y ∨ B) --aR_disj--> (C ∨ Y) ∨ B` |
| K ∨ C | `K[B] ∨ C --(gDisj K B ∨ id C)--> (Y ∨ B) ∨ C --(c_disj Y B ∨ id C)--> (B ∨ Y) ∨ C --aL_disj--> B ∨ (Y ∨ C) --c_disj--> (Y ∨ C) ∨ B` |
| C ∧ K | `C ∧ K[B] --(id C ∧ gDisj K B)--> C ∧ (Y ∨ B) --d C Y B--> (C ∧ Y) ∨ B` |
| K ∧ C | `K[B] ∧ C --(gDisj K B ∧ id C)--> (Y ∨ B) ∧ C --(c_disj Y B ∧ id C)--> (B ∨ Y) ∧ C --dR B Y C--> B ∨ (Y ∧ C) --c_disj--> (Y ∧ C) ∨ B` |

**Rendered-source discrepancy.** The displayed disjunctive hole case on
printed p.319 actually reads `B ⊢ top ∨ B`. This is not merely a text-extraction
artifact: the rendered PDF was inspected. The immediately preceding general
type is `K[B] ⊢ K[bot] ∨ B`, and Table 2, printed p.49, defines
sigma-disjunction-left-in as `B ⊢ bot ∨ B`. The implementation uses this
well-typed named unit map and records the discrepancy. It does not add an
arrow of the displayed, inconsistent type. Render/source hashes are retained
in `provenance/wsl-contextual-factorization/source-consultation.json`.

All four factorizations below are now theorems of Reduced.Hom. The source
instances are obtained by h = ofTerm(eta p) or h = ofTerm(epsilon q).
The Lean theorems prove the stronger version for every existing h of the
same unit-domain/codomain type. Write r+ = rightIn conj and
r− = rightOut disj; 0 means a zero endomorphism only.

| Source equation | Exact execution-order path and compiled declaration |
| --- | --- |
| (gη), p.319 | `K[eta p] = r+ X ; (id X ∧ eta p) ; (id X ∧ 0 E_p) ; gConj K E_p`, each path X → K[E_p]. `Context.gEta`. |
| (gε), p.320 | `K[epsilon q] = gDisj K D_q ; (id Y ∨ 0 D_q) ; (id Y ∨ epsilon q) ; r− Y`, each path K[D_q] → Y. `Context.gEpsilon`. |
| (gηf), p.320, f : B → X | `f ; K[eta p] = r+ B ; (id B ∧ eta p) ; (f ∧ 0 E_p) ; gConj K E_p`, from B to K[E_p]. `Context.gEta_comp`. |
| (gεf), p.320, f : Y → C | `K[epsilon q] ; f = gDisj K D_q ; (f ∨ 0 D_q) ; (id C ∨ epsilon q) ; r− C`, from K[D_q] to C. `Context.gEpsilon_comp`. |

| Proof input / source | Actual reduced derivation |
| --- | --- |
| Table 2 p.49; (b delta sigma), (b delta), unit inverses, p.101 | `ReducedLaws` lifts only the unchanged inherited schemas to Hom. `ReducedStructure.rightIn_tensor` derives the right-unit/associator equation from pentagon, triangle, naturality and cancellation of explicit inverse arrows. `rightOut_tensor` is its inverse form; shuffle laws additionally use hexagon and symmetry. |
| (sigma dL), (delta dL), §11.5 p.270 | `dist_top` follows from `dist_snd` and product unit isomorphisms; `dist_bot` follows from `dist_inl` and coproduct unit isomorphisms. `distRight_top`, `disj_shuffle_dist_top`, and `conj_shuffle_dist_bot` expand the actual derived dR when needed. No same-connective medial is substituted. |
| p.319 induction, (0I) and zero_top = id | Reduced product/coproduct structures are constructed via existing generic DiagonalData derivations. `zero_top`, `zero_bot`, `fromTop_unique`, `toBot_unique` are derived inside Reduced, not reflected from Presentation. |
| p.319, final sentence of (gη) induction | The source invokes Distributive Dicartesian Coherence (§11.5) for the other context cases. Here all needed identities are derived directly: `gConj_nat/gDisj_nat`, `gConj_top/gDisj_bot`, then zero-based uniqueness and naturality. No general positive-core faithfulness theorem is assumed or claimed. |
| p.320, relation comparisons following (gηf)/(gεf) | `Context.Fixed`, `encode/decode`, injective disjoint embeddings, and `occurrence_map` give exact context coordinates. `gEta_comp_relation` compares input x with Sum.inl x in B ∧ E_p; `gEpsilon_comp_relation` compares output y with Sum.inl y in C ∨ D_q. No cross-type equality of relations is asserted. |
| p.321, final common-atomic factorization argument | Source explicitly invokes Zero-Identity Distributive Dicartesian Coherence (§12.5) on f1'' and f2''. Common atomic η/ε factorization and complete support are now proved below. The positive-core theorem and Reduced.Faithful remain unproved. Contextual or common factorizations alone are not coherence. |

`Context.map_derives` precedes quotient action. `mapTerm_id/mapTerm_comp`
are actual reduced derivations (Quotient.exact of equalities in the quotient
whose defining relation is Derives). They do not use inclusion reflection.
The functor at a fixed context is covariant from Reduced.category P to itself,
with object map plug and arrow map map; `map_id/map_comp` prove its laws.
No object-duality arrow operation or descent of full raw reduction is used.

## Common atomic factorization and positive middle terms

Source: September 2007 §14.2, printed pp.320–321 / one-based PDF
pp.332–333. Let E_p = neg p ∨ pos p and D_q = pos q ∧ neg q.
These are normal-form objects, not new primitive arrows. Write X_0 = A,
X_{k+1} = X_k ∧ E_{p_{k+1}}, Y_0 = B and
Y_{j+1} = Y_j ∨ D_{q_{j+1}}. All folds are left-associated. Semicolon
executes the left arrow first; the source writes the reverse order with ◦.
The source's n and m count atomic occurrences, so repeated equal labels occupy
different list positions.

| Source notation / location | Exact types and order | Lean correspondence |
| --- | --- | --- |
| p.320, eta^0 / eta^{k+1} = eta^k ∧ eta_p | eta^n : A_top^n → X_n, with eta^0 = id A; A_top^{k+1} = A_top^k ∧ top | `AtomicPorts.unitObject conj A n`, `etaTensor (.id A) ps` |
| p.320, epsilon^0 / epsilon^{j+1} = epsilon^j ∨ epsilon_q | epsilon^m : Y_m → B_bot^m, epsilon^0 = id B; B_bot^{j+1} = B_bot^j ∨ bot | `unitObject disj B m`, `epsilonTensor (.id B) qs` |
| p.320, conjunctive delta^n | A → A_top^n; insert the next top after the existing unit insertion | `unitIn A n`; `prefix_separated` proves etaPrefix = unitIn ; etaTensor |
| p.320, disjunctive delta^m | B_bot^m → B; remove the last bot before the earlier removals | `unitOut B m`; `suffix_separated` proves epsilonSuffix = epsilonTensor ; unitOut |
| pp.320–321, zero^n / zero^m | Endomorphisms X_n → X_n and Y_m → Y_m; id on the original block and a zero endomorphism at each added port | `mask conj A ps`, `mask disj B qs`, using `zeros` with identity accumulator |
| p.321, h-conjunction | X_all → X_used. At a kept occurrence tensor the accumulator with id E_p. At an absent occurrence project X_all_previous ∧ E_p → X_all_previous before the accumulator | `Selection.keep/absent`, `Selection.all/kept`, `inputPad`; positivity and `inputPad_natural` compile. Selection records positions, without comparing labels. |
| p.321, h-disjunction | Y_used → Y_all. At a kept occurrence tensor with id D_q. At an absent occurrence postcompose the accumulator with the first injection Y_all_previous → Y_all_previous ∨ D_q | `outputPad`; positivity and `outputPad_natural` compile. |
| p.321, f_i' | Initial eta/epsilon-free positive raw middle term at the term's own expanded endpoints | `AtomicFactor.middle`, with `positive`, exact eta_list/epsilon_list and quotient factorization. Generated through the earlier contextual identities. |
| p.321, f_i'' = zero^n ; h_input ; f_i' ; h_output ; zero^m (execution order) | Completed positive middle at common endpoints, including padding and both zero factors | `CommonAtomicFactor.middle₁/middle₂`. The construction uses one extraction of t₁ ∧ t₂ and positive diagonal/projection padding, described below; it does not claim a syntactic identity with a separately chosen source f_i'. `masked_support` proves that the final masks remove every auxiliary edge. |
| p.321, equal relations of completed middles | Equality of the entire relations, not just the embedded original block | `CommonAtomicFactor.relations_equal`, from support₁/support₂ and the original relation equality |
| p.321, §12.5 appeal | Faithfulness for the eta/epsilon-free, zero-identity distributive dicartesian arrow fragment | `PositiveCoherence P` is an explicitly unproved proposition. `faithful_of_positive_coherence` proves only its conditional consequence. |

**Confirmed rendered discrepancy.** The kept h-disjunction branch on printed
p.321 displays identity at `q_{k+1} ∨ neg q_{k+1}`. The epsilon primitive has
domain `q_{k+1} ∧ neg q_{k+1}`, as does the expanded port displayed immediately
above on the same page. The branch requires identity at that conjunction.
The rendered PDF was inspected at high resolution; this is not merely an
extraction artifact. `outputPad` uses the correctly typed identity at D_q,
and the discrepancy is retained here. The earlier p.319 unit typo remains
recorded in the contextual section. Neither display is added as an equation.
Source and rendering hashes are in the current source-consultation record.

The positive fragment is the inductive `Term.Positive` predicate: all 19
non-eta/epsilon constructor schemas of the existing Term grammar, recursively
closed under comp and both tensors. Zero endomorphisms remain included.
Both signs of literal and both constants remain allowed as objects. There is
no additional quotient: ambient arrow equality is the unchanged Reduced.Hom
quotient generated by Reduced.Derives and its 61 Equation schemas.

`Term.atomicView` recursively selects the first atomic syntactic occurrence,
with a positive preterm, one typed context and a remaining postterm.
AtomicSplit's eta/epsilon list equations preserve all repeated occurrences.
Its composition and both tensor clauses prove equality in Reduced, using
category and tensor laws. Each remainder replaces one contextual eta/epsilon
by the already proved g maps and zero endomorphisms. The strictly smaller
atomicCount proves termination of `atomicFactor`. Its lists are exactly the
original traversal lists, rather than deduplicated collections.

For two parallel raw terms, `commonAtomicFactor` performs one extraction on
`t₁ ∧ t₂ : A ∧ A → B ∧ B`. Thus the common lists are exactly the two traversal
lists concatenated in order. If M is that positive middle, the two unmasked
middle terms are

```
lift conj (diag A) ps ; M ; lift disj (fst B B) qs
lift conj (diag A) ps ; M ; lift disj (snd B B) qs.
```

`AtomicFactor.remap` proves that the same etaPrefix A ps and epsilonSuffix B qs
are outer factors for both, by `prefix_natural/suffix_natural`, associativity
and the proved product projection laws. This supplies common endpoints in a
single construction, not two unrelated existential factorizations. The source's
keep/absent padding maps and their factor-compatibility laws are also compiled.
No port permutation is needed in this implementation: every construction uses
the same left-associated concatenated word, including repeated positions.
Reassociation of composites uses the existing category law; `expand_append`
records the left-fold object identity. No unproved permutation or equality
reflection is invoked.

`embed conj A ps` and `embed disj B qs` are the iterated tagged first-block
injections; both are injective. `prefix_relation` is their graph and
`suffix_relation` is the converse graph at the output. `zeros_relation` and
`mask_relation` prove complete support directly from the raw relation grammar.
For each completed middle, support₁/support₂ state

```
relation middle u v ↔ ∃ x y,
  u = embedA x ∧ v = embedB y ∧ relation original x y.
```

The zero masks retain exactly the original input/output blocks, not all blocks
with matching labels. The nil folds are identity terms/maps. When an original
occurrence type is Empty, the existential support statement has no witnesses,
so the completed relation is empty; no auxiliary edge remains. These relation
proofs interpret proved syntactic equalities in the forward direction only.

The zero-tensor and union-unit algebra, positive Gentzen representation,
unrestricted cut elimination, finite atomic mix normal forms, restricted DNF/CNF
coherence and actual PositiveCoherence P are now proved. Reduced.faithful and
Presentation.coherence instantiate the original faithful occurrence interface.
Contravariant arrow negation/naturality, the actual quotient reduction/inclusion
functors, both recovery laws and the full proof-congruence bridge are now proved.
The short q/e proof is now separately completed by Presentation.short_maximality.
The model, remaining substitution/operation laws and appendix correspondences
stay separate duties. The local construction ledgers
below preserve their historical scopes, superseded by the current theorem table.

## Positive-fragment zero and derived union algebra

Source: September 2007 §10.1, pp.219–220, §11.1 p.234, and §12.5,
pp.287–292. The target calculation on printed p.291 / one-based PDF p.303
was also checked in the rendered PDF. Semicolon executes the left arrow first.
All objects below are NormalForm P; P is arbitrary and literal signs unrestricted.

| Source label / location | Exact type, hypotheses and status in the source | Lean declaration (namespace Reduced) |
| --- | --- | --- |
| (0I), pp.287–288 | 0_A ; f = g ; 0_B for existing parallel f,g : A → B; inherited defining schema | Existing `Laws.zero_law`; new `zeroIdentity` packages it. |
| 0_(A,B) definition, p.288 | 0_A ; f : A → B requires a witness f : A → B; not a primitive arrow for every pair | `zeroOf`, `Term.zeroOf`, `ofTerm_zeroOf`. |
| p.288 two unlabelled independence consequences; (0 nat), §12.1 | Existing parallel witnesses give the same zero; a zero commutes with every existing arrow; composition absorbs witnessed zeros | `zeroOf_independent`, `zero_commute`, `zeroOf_pre`, `zeroOf_post`. |
| (00), p.288 | 0_A ; 0_A = 0_A, derived from (0I) | `zero_idempotent`, `zeroOf_zero`; `zeroOf_id` identifies the identity witness. |
| (0I ξ), p.288 | 0_A ξ 0_B = 0_(A ξ B), ξ = ∧ or ∨; a consequence, not an additional equation | `tensor_zero`, using reduced product/coproduct extensionality `conj_ext/disj_ext`. |
| (0 ξ), p.288 referring to §12.1 | For existing f : A → C and g : B → D, zeroOf f ξ zeroOf g = zeroOf (f ξ g) | `tensor_zeroOf`, from tensor composition and `tensor_zero`. Both factors are zeros. |
| Union definition, §10.1 p.220; (wm), p.219 | For parallel f,g : A → B: diag_A ; mix_(A,A) ; (f ∨ g) ; codiag_B | `Term.union` uses the equivalent diag_A ; (f ∧ g) ; mix_(B,B) ; codiag_B. `union_source` proves equality by (m nat); no primitive union constructor. |
| Generated congruence closure | Congruent f/f' and g/g' give congruent unions; positive inputs give positive union | `Derives.union` precedes quotient `union`; `Term.Positive.union`, `union_ofTerm`, `union_def`. |
| (∪ com), p.220 | Parallel f,g; consequence in ML, defining equation only in the alternative Gentzen GML system | `union_comm` derives it from diag/swap naturality, (c m) and codiag symmetry. |
| (∪ assoc), p.220 | Three parallel arrows; same source distinction | `merge_assoc`, `pair_assoc`, `union_assoc` derive it from (b m), mix naturality, and diagonal/codiagonal associativity. |
| (∪ idemp), p.220 | f ∪ f = f; consequence of (wm) in ML | `union_idem`, from diag naturality and `Laws.diag_mix_codiag`. |
| Both (∪ ◦), p.220 | h : X → A or k : B → C with parallel f,g : A → B | `union_pre` and `union_post`; `merge_nat` is the typed helper. |
| (∪0), pp.289–291 | Assumed in ZIML, but derived in ZIDL with (0I); the identity instance id_A ∪ 0_A = id_A suffices | `union_id_zero` uses the direct p.291 structural derivation, then `union_zeroOf` and `zeroOf_union` for any same-type existing witness. No (∪0) Equation is added. |
| G(f ∪ g) = Gf ∪ Gg, p.220 | Pointwise disjunction at the same tagged endpoints, independently of faithfulness | `Term.relation_union`, `occurrence_union`. |
| G0 empty, §12.5/§12.1 | Witnessed zero interprets as the empty relation; does not give equality reflection | `Term.relation_zeroOf`, `occurrence_zero`, `occurrence_zeroOf`. |

The derived union path has all intermediate types

```
A --diag--> A ∧ A --f ∧ g--> B ∧ B --mix--> B ∨ B --codiag--> B.
```

For the p.291 identity calculation, use B = A, f = id A and g = 0_A,
then expand mix by (d m), p.234. After diag and id ∧ 0, the remaining path is

```
A ∧ A --id ∧ inr--> A ∧ (A ∨ A) --d--> (A ∧ A) ∨ A
      --fst ∨ id--> A ∨ A --codiag--> A.
```

Witness independence replaces 0_A ; inr by 0_A ; inl. The middle
`(id ∧ inl) ; d` is `inl : A ∧ A → (A ∧ A) ∨ A` by (d k∨).
Injection naturality moves fst before inl. Projection naturality eliminates
the unused zero block, and diag ; fst = id, inl ; codiag = id finish.
These are reduced syntactic equalities; the alternative coherence appeal in
the source's last line is not used. No equality is inferred from relations.

Both-zero compatibility does not imply one-zero annihilation: for a literal p,
the second tagged edge survives in `0_p ∧ id_p` and `0_p ∨ id_p`.
Witnessed zeros require an existing arrow even when their relation is empty.
No hom-set bottom or semilattice typeclass is installed. The existing 21 raw
constructor schemas, 61 generating equations, and 19 positive schemas are
unchanged. The algebra actually holds for all existing Reduced arrows, so its
positive restriction requires no additional hypothesis beyond membership for
raw representatives. Positivity means eta/epsilon-free constructors, not
positive literal signs.

The direct merge/pair proofs replace only the §10.1 appeal to Lattice
Coherence for the union laws needed here. They do not replace Gentzenization,
cut elimination, restricted coherence, or the §12.5 faithfulness argument.
The historical dependency table in POSITIVE_ZERO_UNION_REPORT records the
then-open constructions. G0/G1 are now proved below; CODEX_NEXT_SESSION gives
the completed Atomic-k proof and the remaining cut-elimination dependencies. Signed-label preservation is not
fullness: no realization theorem for all signed-label-respecting relations is
assumed. Historical source discrepancies and access records are preserved.

## Typed positive Gentzen syntax and existential Gentzenization

Source: September 2007 §11.1 printed pp.238–246 (one-based PDF pp.250–258),
§11.5 pp.271–273 / PDF pp.283–285, and §12.5 pp.291–292 / PDF pp.303–304.
The pinned book hash is unchanged. The p.240 mixed composites were checked
in the rendered PDF. `Gentzen` below means `Reduced.Gentzen`; `G` is its
indexed syntax. All parameters P, signed normal forms and contexts are arbitrary.
Semicolon executes its left arrow first.

`fold o` is defined by structural recursion and `fold_as_foldr` proves equality
with List.foldr o.formula o.unit. Thus ante Γ = Γ.foldr conj top and
succ Δ = Δ.foldr disj bot, exactly the proposed objects. Empty lists have
different colours: ante [] = top, succ [] = bot. They are never identified.
Singletons are A∧top and B∨bot, with explicit right unit comparisons.

| Source / rule | Premises, conclusion and selected positions in G | Positive raw denotation / checked declaration |
| --- | --- | --- |
| p.240 identity basis; p.291 zero basis | identity l / zero l : G [lit l] [lit l], for every complete signed l | `encode (.id (.lit l))` / `encode (.zero (.lit l))`; `denote_identity/denote_zero`. No compound identity or zero leaf. |
| p.272 constant basis | topI : G [] [top]; botE : G [bot] [] | rightIn disj top : top → top∨bot; rightOut conj bot : bot∧top → bot. `denote_topI/denote_botE`. No G [] [] leaf. |
| cL, p.240 | G (Γ++X++Y++Θ) Δ → G (Γ++Y++X++Θ) Δ | Precompose `(exchange conj Γ X Y Θ).invTerm`; `denote_exchangeL`. Source swapped blocks are nonempty; the implementation also permits their explicit unital extensions. |
| cR, p.241 | G Γ (Δ++X++Y++Λ) → G Γ (Δ++Y++X++Λ) | Postcompose `exchange disj Δ X Y Λ`; `denote_exchangeR`. Lean swap arguments give execution-domain order; the book's disjunctive symmetry subscripts are reversed. |
| kL, p.241 | thinL inserts A at the selected gap Γ|Θ; source operation adds at the right | Product routing ignores just that new input. `thinLast` implements the source rightmost case with list-index transport and `thinLast_denote`. No search for all matching A. |
| kR, p.241 | thinR inserts A at Δ|Λ; the source front case is Δ=[] | Coproduct routing inserts the selected output branch; `denote_thinR`. |
| wL, p.241; y on pp.239,243 | gs=[Γ1,…,Γn], n≥2; premise repeated C gs ++ Θ, conclusion gaps gs ++ C::Θ | `copies C gs Θ` routes every selected C to the one retained position, fixes every gap/tail position, and uses product pairing. `denote_contractL`, `Route.product_get`, `product_positions`. |
| wR, pp.241,243 | Dual full separated multiple contraction. Primitive convention retains the last selected C; source retains the first | `contractRFirst` gives source order Δ ++ C::(gaps gs ++ Λ), n=1+length gs≥2. It composes the primitive with explicit block exchange and list transports; `contractRFirst_denote/count`. `denote_contractR`, `Route.coproduct_get`, `coproduct_positions` give component laws. No adjacent-contraction completeness theorem is assumed. |
| ∧L, p.242 | G (Γ++A::B::Θ) Δ → G (Γ++(A∧B)::Θ) Δ; principal pair selected by prefix/suffix | Precompose the prefix lift of assocL conj A B (ante Θ); `Rules.conjLeft`, `denote_conjL`. Θ=[] is the source's last-pair convention. |
| ∨R, p.242 | G Γ (Δ++A::B::Λ) → G Γ (Δ++(A∨B)::Λ) | Postcompose the prefix lift of assocR disj A B (succ Λ); `Rules.disjRight`, `denote_disjR`. Δ=[] is the source front-pair case, with its A/B names matched to position order. |
| ∧R, p.242 | f : Γ |- A,Δ; then g : Θ |- B,Λ; conclusion Γ++Θ |- A∧B,Δ++Λ | Input append inverse; f∧g; `mixedDisj A (succ Δ) B (succ Λ)` (source e'-disjunction indices A,B,succΔ,succΛ); output residue append. `Rules.conjRight`, `denote_conjR`, `sourceDisj_expansion`. Premise and residual order are preserved. |
| ∨L, p.242 | f : A,Γ |- Δ; then g : B,Θ |- Λ; conclusion A∨B,Γ++Θ |- Δ++Λ | Split residual input; swap principal sum to right; `Rules.sourceConj (ante Γ) (ante Θ) A B`; swap each product branch to principal-first order; f∨g; output append. `denote_disjL`. This is the source rule after explicit principal/premise-order comparisons, not an implicit reassociation. |
| mix, p.241 | f : Γ |- Δ; then g : Θ |- Λ; conclusion Θ++Γ |- Λ++Δ | Input append inverse; g∧f; mix_(succΛ,succΔ); output append. `Rules.mix`, `denote_mix`; order agrees with the displayed source. |
| contextual cut, p.241 | Head rule: f : Γ |- C,Δ, g : C,Θ |- Λ; result Θ++Γ |- Λ++Δ | Input append inverse; id_(anteΘ)∧f; d_(anteΘ,C,succΔ); ((swap_(anteΘ,C);g)∨id_(succΔ)); output append. `Rules.cut`, `denote_cut`. The distinguished occurrence is the head C in each premise. |
| full displayed cut, p.241 | f : Γ3 |- Δ2++[C]++Δ1; g : Γ1++[C]++Γ2 |- Δ3; result (Γ1++Γ2)++Γ3 |- Δ3++(Δ2++Δ1) | `cutAt` moves those selected C occurrences to the heads by block exchange, then cuts; `cutAt_denote/count`. List reassociation is transport of indices, not formula associativity. Extra equal C formulas remain fixed. |

The conjunction mixed comparison is transcribed directly from the rendered
p.240 definition. For X,Y,A,B its execution-order path is

```
(X∧Y)∧(A∨B) --id∧swap--> (X∧Y)∧(B∨A)
 --assocL--> X∧(Y∧(B∨A)) --id∧d--> X∧((Y∧B)∨A)
 --id∧swap--> X∧(A∨(Y∧B)) --d--> (X∧A)∨(Y∧B).
```

The old ReducedWitnesses.mixedConj is a separately typed witness composite;
no general equality with this source e' was available or used. It remains
unchanged. `sourceConj` supplies the actual source expression. The existing
mixedDisj does match the source e'-disjunction: `sourceDisj_expansion` proves
its expanded p.240 steps by tensor/category laws. Neither is same-connective
medial, and no new generator or equation identifies them.

`Iso` contains positive raw forward/backward terms with proved inverse laws.
`append`, `under` and `exchange` construct those comparisons from actual
associators, symmetries and units. `termTransport/reindex` transport only equal
list indices; their denote/count laws are proved by equality elimination.
`At` selects a whole-formula position by here/there. Route and copies preserve
fixed positions even when they contain the same C or repeated equal literals.
Their product/coproduct component laws and extensionality follow from the
already derived reduced universal properties, replacing a coherence appeal.

For actual singleton calculations, `appendNil_to`, `single_split/single_join`,
`append_insert/remove`, `mixedDisj_bot`, `disjInput_out/value` and `cut_pure`
prove the needed unit specializations. `cut_single` is composition after both
unit comparisons. No specialized d or mixed composite is merely declared an
identity. Empty residual contexts are top/bottom objects, never a shared ∅.
`G.no_empty` maps a putative G [] [] by denotation and inclusion to the proved
impossible full Hom(top,bot); it uses no faithfulness.

The source Gentzenization proof invokes associativity/symmetry coherence on
pp.245–246. Here `DiagonalData.assocR_fst/snd/assocR_pair/assocL_pair` derive
precise product formulas from the existing laws and the proved unit equation;
coproduct formulas use the opposite category. These provide the required
instances without assuming any earlier coherence theorem. The zero extension
uses `zeroNF_value`, both-zero tensor compatibility and zero_top/zero_bot.

`positive_represented` inducts on all 19 Positive schemas; the coverage table
in POSITIVE_GENTZENIZATION_REPORT identifies each branch. `gentzenization`
proves the requested singleton equation, and `gentzenization_decode` gives the
exact original-endpoint equation. These are existential results with cuts.
No canonical representative, cut elimination, Gentzen quotient, equation
preservation for a chosen translation or function on quotient arrows is claimed.

`G.relation` is the raw denotation relation; `occurrence_denote` connects it to
Reduced.occurrenceMap. `singletonOcc/singletonFrom` are inverse tagged maps
between each original occurrence type and its singleton fold. Their inverses
eliminate Empty unit branches. `gentzenization_occurrences` proves exact
pointwise relation agreement in those coordinates. Relations never prove
syntactic equality. Signed-label preservation is not fullness or faithfulness.

`cutCount`, `CutFree`, `Topmost` and `Atomized` are implemented analysis
interfaces. Atomic-k atomization, including denotation equality and preservation
of existing CutFree, is now proved as recorded below. The cluster/rank prerequisite
is also proved below. Blocked-contraction transformations, cut elimination,
restricted mix coherence, PositiveCoherence and Reduced.Faithful
remain open. No source citation supplies
those missing proofs, and no coherence premise is added to Gentzenization.

## Positive thinning atomization (Atomic-k)


The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
Its SHA-256 is
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12 (one-based). Formulas on printed pp.247 and
271 were inspected in rendering; render hashes/locations are recorded in
`source-consultation.json`. The source PDF stays in the ignored reference cache.

| Source location | Source role and exact scope used | Lean construction / replacement for source proof appeals |
| --- | --- | --- |
| §11.1 p.234, mixed structural equations; p.240 mixed-map definitions | The actual e′∧ has type `(X∧Y)∧(A∨B) → (X∧A)∨(Y∧B)`. e′∨ has type `(A∨X)∧(B∨Y) → (A∧B)∨(X∨Y)`. | Existing `Rules.sourceConj X Y A B` and `Term.mixedDisj A X B Y`; `sourceConj_nat`, `mixedDisj_nat` derive naturality of these composites. |
| §11.1 pp.241–243, exchange and separated multiple contraction | Exchange specifies prefix, two blocks, tail; contraction selects copies by the intervening gaps. Empty gaps and repeated equal formulas are legal. | Existing constructors are unchanged. New exchange components, `copies_index` and `Rewire.duplicate` derive block contractions from them. |
| §11.2 pp.246–247, Atomic-k; first compound-k rewrite | Left conjunction thinning becomes two sequential thinnings followed by conjunction-left; the dual handles right disjunction. | `conjLeft_head`, `disjRight_head`, `conj_thin_head`, `disj_thin_head`, `headThinL/R_denote`. Association is a proved arrow comparison. |
| §11.2 p.247, disjunctive compound-k rewrite; use of contraction and (m e∧) | Branch over A and B, then contract both duplicated surrounding contexts. The source invokes earlier coherence in its calculation. | `sourceConj_fst`, `branchL_core`, `branchL_denote`; proved using existing structural equations, constant specializations and union idempotence. |
| §11.2 p.247, dual compound-k case; §11.5 pp.270–271, omitted mixed equations | Right conjunction thinning requires the mixed arrow actually used by `Rules.conjRight`, and contraction on both sides. | `mixedDisj_inr`, `branchR_core`, `branchR_denote`; actual mixedDisj, injection naturality and `diag_mix_codiag`. |
| §11.5 pp.272–273, Atomic-k with constants | Atomic formulas include top/bottom; thinning by bottom on the left and top on the right is retained. The two empty folds have different colours. | `headThinL/R` retain actual primitive thinning at lit/top/bot; no constant-based replacement proof or empty-sequent leaf. |
| §12.5 pp.291–292, zero extension | Atomic zero leaves are among the bases; later zero cut-elimination cases are separate. | `atomize (.zero l) = .zero l`; existing atomic zero bases remain unchanged. Later zero reduction cases remain open. |

Neither omitted `(m e)` schema was added to `Reduced.Equation`. The results
below are sufficient projected/injected consequences, **not a claim to prove
both complete omitted schemas**. No new source discrepancy was confirmed in
this checkpoint; earlier correspondence entries and access records are retained.

## Categorical calculations before proof transformation

`sourceConj_fst X Y A B` proves, for all four normal forms:

```text
sourceConj X Y A B ; (fst X A ∨ fst Y B)
  = fst (X∧Y) (A∨B) ; mix X Y.
```

Both sides have type `(X∧Y)∧(A∨B) → X∨Y`. The left path goes through
`(X∧A)∨(Y∧B)`; the right through `X∧Y`. Its proof expands the actual
source-defined composite only in small structural lemmas, uses the existing
d-k/d-m laws and naturality, proves the top specialization, and maps A/B to
top. The specialization uses the established zero-derived top-domain
uniqueness. It does not use an interpretation to reflect equality.

The required dual calculation is `mixedDisj_inr A B X Y`:

```text
(inr A X ∧ inr B Y) ; mixedDisj A X B Y
  = mix X Y ; inr (A∧B) (X∨Y).
```

Both sides have type `X∧Y → (A∧B)∨(X∨Y)`. The left intermediate object is
`(A∨X)∧(B∨Y)`. The proof establishes the bottom specialization, its typed
unit inverse, and naturality along `fromBot A` and `fromBot B`. Initiality
and existing zero-derived bottom-codomain uniqueness justify the specialization.
There is no cancellation without an inverse and no appeal to full-Presentation
uniqueness. Both calculations are inside Reduced.Hom.

For `f : Hom X Y`, the branching left calculation has the complete path:

```text
(A∨B)∧X → (A∨B)∧(X∧X) → (X∧X)∧(A∨B)
 → (X∧A)∨(X∧B) → X∨X → Y∨Y → Y.
```

The arrows are `id ∧ diag`, swap, sourceConj, the two first projections,
`f∨f`, and codiag. `branchL_core` proves that this equals `snd ; f`.
After `sourceConj_fst`, its remaining duplicated-f expression is `f ∪ f`,
which equals f by the already proved syntactic union idempotence.

The branching right path is:

```text
X → X∧X → (A∨Y)∧(B∨Y) → (A∧B)∨(Y∨Y) → (A∧B)∨Y.
```

Its arrows are diag, `(f;inr A Y) ∧ (f;inr B Y)`, actual mixedDisj, and
`id ∨ codiag`. `branchR_core` proves equality to `f ; inr (A∧B) Y`.
The proof uses `mixedDisj_inr` and the existing diagonal–mix–codiagonal law.
No same-connective medial or older `ReducedWitnesses.mixedConj` is substituted.


The exact public endpoint is `Reduced.Gentzen.G.atomization`; its CutFree and
complete occurrence variants are `atomization_cutFree/atomization_occurrences`.
`headThinL/R` recurse on formulas and use no cuts. `atomThinL/R` move the
selected formula to an arbitrary gap by proved positional exchange. Rewire
scripts expand to existing exchange/contraction/reindex macros; all duplicated
context blocks are contracted with index and component proofs. The global
transformation covers all sixteen unchanged Gentzen schemas. It does not
give a decreasing rank, cut elimination, quotient translation or coherence.
See [the Atomic-k report](POSITIVE_THINNING_ATOMIZATION_REPORT.md), including
its four compound cases, constructor coverage, exact hypotheses and evidence.

## Typed whole-formula ancestors, finite clusters and cut rank

The September 2007 source and source hashes are unchanged. Printed pp.248–249
were inspected in rendering for this construction. The source's cluster
traces whole-formula positions and counts every node. Our existing positional
G rules use explicit context gaps and branch tags; their exact order appears
in the constructor table below.

| Source location | Definition / repository correspondence | Proved declaration |
| --- | --- | --- |
| §11.2 p.247, leaf formulae | Atomic identity leaves both sides. Thinning and logical introduction terminate at the selected principal whole formula. The source's rightmost/leftmost conventions are translated to the explicit list gaps of existing G, rather than matched by formula value. | `G.sourceArity`, `Leaf`; classification/count correctness and principal-leaf lemmas. |
| §11.2 pp.247–248, lower/upper contraction formulae | Lower position is `At.shift (gaps gs) (At.here C Θ)`; upper copies occur after each selected gap in `repeated C gs ++ Θ`. Fixed equal formulas in gaps are not selected copies. | `G.LowerContraction`, `selectedCopies`, `selectedCopies_length/nodup`, `contraction_predecessorsL/R`. |
| §11.2 p.248, parametric sequences | Each fixed position has one upper position in the designated premise, with the same side and whole formula. | `Premise.parent`, `G.predecessors_correct`, `sourceArity_correct`, `parametric_unique`. |
| §11.2 pp.248–249, finite cluster | Root is the selected conclusion position; leaves stop; contractions branch to all selected upper copies; parametric nodes have one successor. Node labels identify proof occurrences. | `TraceNode`, `ProofAddress`, `G.cluster_root`, `cluster_correct`, `cluster_address`, `TraceNode.cluster_children`. |
| §11.2 p.249, ρ | Total number of nodes, including the root and every branch; not longest-path length. | `G.rho_node_list`, `rho_eq`, `rho_one_iff_leaf`, `rho_child_lt`. |
| §11.2 p.249, contraction ranks | Apply ρ to the lower contraction position, for arbitrary proofs. | `contractionRankL/R`, `contractionRankL_eq/R_eq` give 1 plus the sum over every selected copy. |
| §11.2 p.249, left/right cut formulas and ranks | For `f : G P Γ (C::Δ)`, left cut formula is the right-side head of f; for `g : G P (C::Θ) Λ`, right cut formula is the left-side head of g. Sum their ranks. No Topmost premise is required. | `leftCutRank/rightCutRank/cutRank`, `cutRank_ge_two`, `cutRank_two_iff_leaves`. |
| §11.2 pp.249–250, tied contractions | A branching lower contraction node belongs to the chosen cut-formula cluster, on its specified side. | `TiedRight/TiedLeft`, both `tied*_iff_branching` theorems. Blocked forms and rewrites remain open. |
| §11.5 pp.272–273, constants | topI has a genuine target top position and botE a genuine source bot position; these are leaves although their literal-occurrence types are empty. Empty context colours remain distinct. | `topI_rank`, `botE_rank`; unchanged G/denotation/no_empty. |
| §12.5 pp.291–292, atomic zero extension | Both positions of an atomic zero basis term are leaves; later zero cut rewrites are not part of this construction. | `zero_leaf/zero_rank`; old zero grammar/equations unchanged. |

| Existing G schema | Selected conclusion positions and predecessor routing | Source arity |
| --- | --- | --- |
| identity | Both singleton literal positions are leaves. | 0 |
| zero | Both singleton literal positions are leaves. | 0 |
| topI | Only the target top position exists; it is a leaf. | 0 |
| botE | Only the source bot position exists; it is a leaf. | 0 |
| exchangeL | Source routed by inverse positional block exchange; target fixed. Parent map is the existing swapBlocks. | 1 |
| exchangeR | Target routed by inverse positional block exchange; source fixed. | 1 |
| thinL | Source principal at index Γ.length is a leaf; other positions invert existing Route.thin. | 0 or 1 |
| thinR | Target principal at index Δ.length is a leaf; other positions invert existing Route.thin. | 0 or 1 |
| contractL | Source at index (gaps gs).length branches to selectedCopies; fixed source/target positions have one predecessor. | gs.length or 1 |
| contractR | Dual target selection and every upper copy; fixed positions have one predecessor. | gs.length or 1 |
| conjL | Inserted whole A∧B at the source gap is a leaf. Upper A and B are not ancestors of it; fixed positions retain prefix/tail coordinates. | 0 or 1 |
| disjR | Inserted whole A∨B at the target gap is a leaf; fixed positions retain prefix/tail coordinates. | 0 or 1 |
| conjR | Source Γ++Θ routes to f/g respectively. Target head A∧B is a leaf; residual Δ++Λ routes to the appropriate premise, after its upper principal head. | 0 or 1 |
| disjL | Source head A∨B is a leaf; residual Γ++Θ routes to f/g after their principal heads. Target Δ++Λ routes directly to f/g. | 0 or 1 |
| mix | Conclusion is Θ++Γ and Λ++Δ: first blocks belong to g (branch 1), second to f (branch 0). | 1 |
| cut | Same conclusion order as mix. Surviving source Θ is in g after consumed C; Γ is in f. Surviving target Λ is in g; Δ is in f after consumed C. Neither consumed C is a conclusion position. | 1 |

`Premise.parent` is specified independently from inverse-fiber enumeration.
`predecessors_correct` proves local equivalence; `sourceArity_correct` connects
an independent rule/index classification to computed count. All source
classes are exhaustive and disjoint. Selected contraction copies have exact
count and are distinct positions even when labels agree.

`cluster_correct/cluster_children/cluster_address` give finite reachability,
immediate edges and valid proof-occurrence labels, with side and formula fixed
in TraceNode P s C. `rho_node_list` counts all explicit tree nodes;
`contractionRankL_eq/R_eq` sum all selected upper ranks. `cutRank_ge_two` and
`cutRank_two_iff_leaves` need no Topmost or atomization premise. Reindexing,
cut-free/atomized label propagation and tied-site characterization compile.
G.proofSize is the separate termination count, not rho or cutCount.

The cluster/rank prerequisite within G2 is complete. The two opposite-side
W1 thinning instances are now proved below. Source blocked patterns (p.250),
other W1 cases, W2–W6, Blocked-w, cut elimination and the positive coherence
inputs remain open. No relational reflection,
quotient rank or general transformation decrease is inferred by the cluster
construction alone. The local W1 rank decreases are proved separately below. See
[the report](GENTZEN_CLUSTER_RANK_REPORT.md) for exact hypotheses and evidence.

## Opposite-side thinning instances of W1

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.249–253, 272–273 and
291–292 were consulted; p.251 was also inspected in rendering. The verified
cache and access artifacts are recorded in source-consultation.json.
Historical source-access records are unchanged; no new discrepancy was confirmed.

| Source location | Typed correspondence and exact scope | Lean declarations / proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ = kR | Left contraction after right thinning equals right thinning after left contraction, on the unchanged antecedent copy positions. | `W1.oldL/innerL/newL`, `denoteL`; actual pre/postcomposition and `Reduced.Laws.assoc`. No Semilattice Coherence input. |
| §11.2 p.252, right analogue of Reducibility, applied to p.251 W1 | Right contraction after left thinning equals left thinning after right contraction. | `oldR/innerR/newR`, `denoteR`; separate checked associativity proof, no arrow-negation operation. |
| §11.2 pp.248–249, parametric clusters and rank; pp.251–252, rank condition | Opposite-side thinning has exactly one predecessor at the same At position. Contraction sums every selected upper copy. | `G.predecessors_thinR_left/thinL_right`, `rho_thinR_left/thinL_right`; existing `contractionRankL_eq/R_eq` and `selectedCopies_length`; `contraction_lossL/R`, `endpoint_lossL/R`. |
| §11.5 pp.272–273, constant basis and retained thinnings | Constants remain legitimate selected whole formulas. Left bot and right top thinning are retained operations, not replaced by special constant proofs. | Generic commutations allow all C,D; `emptyP_constantsL/R` at Empty. No literal-occurrence inhabitant is needed. |
| §12.5 pp.291–292, atomic zero basis and extension | Premise f is arbitrary and may contain atomic zero or cuts. These two calculations need no zero-specific rewrite or new zero. | Generic denotation/rank results depend only on constructors and categorical associativity/predecessor laws. Atomic-zero leaf and all existing zero laws are unchanged. |

These are derived local instances. They are not new defining equations,
the full W1 family, or a proof of the source's coherence appeal.

Both pairs preserve CutFree/Atomized equivalently, cutCount exactly and the
complete tagged relation. Let n = gs.length ≥ 2. contraction_lossL/R give
Rold = Rnew + n; endpoint_rankL/R give rho(new,x) = Rnew + 1;
endpoint_lossL/R give rho(old,x) + 1 = rho(new,x) + n. Both strict
inequalities compile for arbitrary P and arbitrary premises, including cuts.
Rank is syntactic and does not descend through reduced denotation. The
unchanged-endpoint relation comparison is a consequence of denotation equality.
See [the report](GENTZEN_W1_THINNING_REPORT.md) for full signatures, paths,
boundary examples and verification. No all-site rank control result is claimed.

## Opposite-side exchange instances of W1

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted;
p.251 was also inspected in rendering. The constant/zero extensions on
pp.272–273 and 291–292 were checked against the existing treatment.
Source-consultation.json records caches, hashes and access artifacts.
Historical source-access records are preserved; no new source discrepancy
was confirmed for these instances.

| Source location | Typed correspondence / scope | Lean declaration and actual proof input |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = cR | wL cR f = cR wL f; right exchange swaps the specified X,Y blocks and leaves antecedent contraction positions unchanged. | `W1.Exchange.oldL/innerL/newL`, `denoteL`; actual G.denote, ofTerm_comp, Reduced.Laws.assoc. |
| §11.2 p.252, right analogue of Reducibility | wR cL f = cL wR f; left exchange swaps X,Y and leaves succedent contraction positions unchanged. | `oldR/innerR/newR`, `denoteR`; separate checked associativity proof in the opposite direction. |
| §11.2 p.248, parametric sequences and predecessor definition | On the side opposite exchange, the exact typed At has one predecessor in the unique premise; no formula-label search. | `G.predecessors_exchangeR_left/exchangeL_right` from existing Premise.parent and TraceRoute.fiber_identity. |
| §11.2 p.249, rho and contraction rank; pp.251–252, rank requirement | Count all cluster nodes. Every selected upper copy contributes an exchange node. | `G.rho_exchangeR_left/exchangeL_right`; existing contractionRankL_eq/R_eq, selectedCopies_length and sum_map_one_add; `contraction_lossL/R`, `endpoint_lossL/R`, strict inequalities. |
| §11.5 pp.272–273, constants | Constants have whole-formula positions even with no literal occurrences. Empty folds are top/bot and remain differently coloured. | `emptyP_constantsL/R` use actual G Empty constant premises. Both-empty exchange still adds a node via rho equations. |
| §12.5 pp.291–292, atomic zero extension | Atomic zero leaves and arbitrary premises, including cuts, are allowed. No special zero law is needed for these two associativity calculations. | Generic results impose no restriction on f; atomic-zero constructor/zero equations are unchanged. No unwitnessed zero is added. |

The source invokes Semilattice Coherence for the larger W1 family. These two
local denotation equations are derived directly; the coherence theorem is
neither assumed nor claimed as a result. Binary context folds remain explicit,
with the actual exchange comparison arrows rather than strictified equality.

Both pairs preserve cutCount exactly, CutFree/Atomized equivalently and the
complete tagged relation. Unlike thinning, exchange adds no AtomicFormula
condition. With n = gs.length ≥ 2, contraction_lossL/R prove Rold=Rnew+n,
endpoint_rankL/R prove rho(new,x)=Rnew+1, and endpoint_lossL/R prove
rho(old,x)+1=rho(new,x)+n, with both strict inequalities. These rank facts
come from syntax and hold for empty blocks, never from denotation equality.
Other W1 cases and all-site rank control/reducibility remain open. See
[the exchange report](GENTZEN_W1_EXCHANGE_REPORT.md) for exact signatures,
intermediate types, checked examples and evidence.

## Opposite-side contraction instance of W1

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n corresponds to PDF page n+12, one-based. Printed pp.248–253 were
consulted, with p.251 also inspected in rendering. Constant and atomic-zero
extensions on pp.272–273 and 291–292 were checked against the existing
syntax. Access artifacts/hashes are retained; historical access records are
unchanged. No new source discrepancy was confirmed.

| Source location | Precisely used construction / condition | Lean correspondence / proof |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = wR | Move a left contraction through an opposite-side right contraction: wL wR f = wR wL f, with independent selected-copy lists. | `W1.Contraction.innerL/innerR/outerL/outerR`; `denote` uses actual pre/postcomposition and Reduced.Laws.assoc, not Semilattice Coherence. |
| §11.2 p.252, right-directed analogue of Reducibility | The same equality is used in reverse when targeting the right contraction. | `denote_reverse` is symmetry of denote; separate `right_directed_balance/decrease` prove the targeted right rank claim. No duplicate pair or arrow-negation construction. |
| §11.2 p.248, parametric sequences / clusters | A contraction has one proof premise. A position on its opposite side has one predecessor; its own lower contraction position branches to all selected upper copies. | `G.predecessors_contractR_left/contractL_right`, `rho_contractR_left/contractL_right`; existing parent/fiber and complete contraction-sum APIs. |
| §11.2 p.249, contraction rank; pp.251–252, directed rank requirement | Count all ancestry nodes, independently for the n selected left copies and m selected right copies. | `outerL_left/outerR_left/outerL_right/outerR_right`, inner-rank inequalities, two directed balances/decreases and named other-side increases. |
| §11.2 p.253, multiset-ordering argument for Blocked-w | Later elimination concerns contractions tied to a chosen cut and all affected sites; the displayed two-rank sum is not a supplied decreasing measure. | Only `endpointSum_balance` and equality for equal arities are proved. No all-site rank control, multiset measure, Reducibility or Blocked-w result is claimed. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants have whole-formula positions; atomic-zero bases are permitted and thinnings retained. | Arbitrary C,D/f in the theorem, actual constantTop/constantBot at Empty P, unchanged zero grammar and witnessed-zero policy. No new zero-specific equation is needed. |

The source's broader Semilattice Coherence appeal is not a Lean proof input.
These local instances follow from existing categorical equations and typed
ancestry. Context folds remain binary and explicitly typed; no strictification
or relation-kernel quotient is introduced.

With final selected positions x,y and inner ranks L,R, the exact table is:
outerL(left,x)=L+n; outerR(left,x)=L+1; outerL(right,y)=R+1;
outerR(right,y)=R+m. The left-directed move lowers left and raises right;
the reverse targets right and raises left. Both have equal Reduced denotation,
count/predicate preservation and complete tagged-relation equality.
endpointSum_balance gives S(outerL)+m=S(outerR)+n, with equality at n=m;
this is not a decreasing measure or unrestricted terminating rewrite system.
No arbitrary-context/all-site decrease is inferred. See
[the contraction report](GENTZEN_W1_CONTRACTION_REPORT.md) for exact signatures,
selected-copy proofs, examples, commands and evidence.

## Opposite-side unary logical instances of W1

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also in rendering. Constant/zero extensions on pp.272–273 and 291–292
were checked against the retained syntax. Source-consultation.json records
verified caches and access artifacts; historical access records remain intact.
No new source discrepancy was confirmed.

| Source location | Exact local use / types | Lean correspondence and actual proof input |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = ∨R | Left contraction commutes with unary right disjunction introduction at the specified gap. Both have source gaps gs ++ C::Θ and target Δ ++ (A∨B)::Λ. | `W1.Logical.oldL/innerL/newL`, `denoteL`; actual G.denote uses copies.product then f then Rules.disjRight.toTerm. Reduced associativity only. |
| §11.2 p.252, right analogue | Right contraction commutes with unary left conjunction introduction. Both have source Γ ++ (A∧B)::Θ and target gaps gs ++ C::Λ. | `oldR/innerR/newR`, `denoteR`; Rules.conjLeft.toTerm precedes f and copies.coproduct follows; reverse associativity. |
| §11.2 p.248, parametric clusters | Every unchanged-side position has one predecessor at the exact same typed At. | `G.predecessors_disjR_left/conjL_right`, `rho_disjR_left/conjL_right` from actual parent/fiber definitions. |
| §11.2 pp.247–249, logical leaf / all-node rank | Introduced whole formula is a leaf; tracing stops, without descending into premise A/B. An outer opposite-side contraction adds one node. | Principal Leaf proofs from sourceArity/index; sourceArity_correct proves empty predecessor lists; rho_leaf proves rank 1; `oldL/oldR_principal_rank` prove 2 and `newL/newR_principal_rank` prove 1. |
| §11.2 pp.249, 251–252, contraction rank and directed requirement | Sum every selected upper copy; each crosses one unary logical proof node. | Existing contractionRankL_eq/R_eq, selectedCopies_length and sum_map_one_add give exact contraction loss n and whole selected-endpoint loss n−1. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants remain whole formulas even when literal-occurrence types are empty; atomic zero leaves remain admitted. | Actual G Empty constant examples; arbitrary premises, including cuts/zero, in generic proofs. No new zero or coherence law is needed. |

The source's Semilattice Coherence appeal is not assumed. These are two
opposite-side unary logical instances only. Binary disjL/conjR, same-side
parametric W1 cases and all-site reducibility remain separate. The existing
syntactic quotient and non-strict binary context folds are unchanged.

Both directions prove Rold=Rnew+n, rho(new,x)=Rnew+1 and
rho(old,x)+1=rho(new,x)+n, with strict inequalities for n≥2. The introduced
principal has empty predecessors and rank 1 at the logical root; old/new
principal ranks are 2/1. Count, CutFree/Atomized and complete tagged relations
are preserved with no atomicity condition. These finish the specified
opposite-side unary W1 families (thinning, exchange, contraction, unary
logical introduction) and their duals. Same-side parametric W1 and binary
logical/reducibility cases remain separate/open. See
[the logical report](GENTZEN_W1_LOGICAL_REPORT.md) for signatures, paths,
fixed equal positions, next-task conditions and verification evidence.

## Same-side thinning at fixed gaps and terminal tails (W1)

The pinned source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA-256
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
including rendered p.251; pp.272–273 and 291–292 supply constant/zero context.
The verified caches and access artifacts are recorded in source-consultation.json.
Historical access records are preserved. No new source discrepancy was confirmed.

| Source location | Scope / positional condition | Lean construction and actual proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ=kL | Every displayed contracted copy remains parametric; insertion is in a specified fixed gap or terminal tail. | `GapInsertion.interior/terminal`; `W1.SameSideThinning.interior_left/terminal_left`, using the proved copies/thinning product square. |
| §11.2 p.252, right analogue of Reducibility, applied to W1 | Dual fixed-position kR/wR instance. | `interior_right/terminal_right`; independently typed coproduct square, with reversed route variance. |
| §11.2 pp.248–249, parametric cluster / all-node rank | An old position crosses thinning once; contraction sums all selected copies. | Complete singleton predecessors, `rho_thinL/R_embedded`, `selected_transport`, existing contractionRankL_eq/R_eq and selectedCopies_length. |
| §11.2 p.251 (W 2) | Inserted occurrence is selected for contraction. | Excluded here: `selected1_parametric` proves its index absent, even E=C. W2 remains open. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants/atomic zeros remain admitted; empty contexts retain their colours. | Existing unchanged syntax; actual constant proofs over Empty and arbitrary cut-containing premises are checked. |

The broader Semilattice Coherence invocation is replaced for these instances
by proved product/coproduct universal extensionality. Binary context folds,
generating equations and syntactic equality remain unchanged.

All four concrete results prove exact list/cast coordinates, the old-position
copies/thinning square, complete ordered selected-copy transport and its index
exclusion, retained transport and a separate inserted image/fixed singleton
fiber. Interior insertion is before the retained lower C, terminal insertion
after it, including E=C. Product/coproduct universal properties give Reduced
denotation equality. Full selected sums give Rold=Rnew+n, rho(new,x)=Rnew+1
and rho(old,x)+1=rho(new,x)+n, strictly decreasing for n≥2. Inserted ranks are
2→1. Both Atomized predicates equal AtomicFormula E ∧ f.Atomized; count,
CutFree/Atomized and complete tagged relations are preserved. No grammar,
equation or old analysis interface changed. See
[the report](GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md) and its two author-side
reviews. Remaining same-side exchange/contraction/logical and broader
reducibility/coherence work remain open.

## Fixed-parametric same-side exchange inside one gap or tail (W1)

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also in rendering. The verified existing cache was used. Constant and
zero extensions on pp.272–273 and 291–292 remain compatible with the unchanged
syntax. Source-consultation.json records caches, hashes and access artifacts;
historical access records remain intact. No new source discrepancy was confirmed.

| Source location | Precise local correspondence / side conditions | Lean declarations and actual proof inputs |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ=cL | Left exchange entirely inside one fixed gap or the fixed terminal tail commutes with left contraction. Every selected copy stays outside the exchanged interval. | `GapExchange.interior/terminal`; `W1.SameSideExchange.interior_left/terminal_left`; proved copies/exchange product square and associativity. |
| §11.2 p.252, right analogue | Right exchange at the corresponding fixed positions commutes with right contraction. | `interior_right/terminal_right`; independently typed coproduct square. |
| §11.2 pp.248–249, parametric ancestry and all-node rank | Exchange routes every whole-formula position bijectively; complete selected-copy sum counts one exchange node per copy. | At.swapBlocks inverse/injectivity; complete same-side predecessor singleton, rho_exchangeL/R_embedded; selected_transport and existing contraction sums. |
| §11.2 p.251, broader cL cases and absorption alternative | Exchanges across selected positions, across several gaps, or absorbed by contraction are not covered here. | No such theorem is supplied. The source's Semilattice Coherence appeal is replaced only for the four fixed-position cases by derived universal component laws. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants and atomic zero leaves remain admitted; empty sequent folds remain differently coloured. | Actual constant examples over Empty; generic premises including cuts/zeros. No new zero equation or arrow constructor. |

Composition is left-first throughout. The binary folds are not strictified;
all needed list equalities and endpoint transports are explicit.

All four concrete results compile with actual list/G/At/Route transports.
The all-position square gives structural p(c1);eUpperL=eLowerL;p(c0) and
eUpperR;q(c1)=q(c0);eLowerR, hence Reduced denotation equality. Complete ordered
selected transport uses interval exclusion, not global monotonicity. Retained
positions transport; fixed singleton fibers correspond. Exact contraction loss
n, whole retained endpoint loss n−1 and both strict decreases compile. Every
other same-side fixed endpoint has unchanged rank 2+rho(f,a); exchange adds no
principal leaf, including empty blocks. Both Atomized predicates equal
f.Atomized; count, CutFree and full tagged relations are preserved. Equal-label
fixed positions transpose even when context lists coincide. See
[the report](GENTZEN_W1_SAME_SIDE_EXCHANGE_REPORT.md) and both author-side reviews.
Cross-selected, multi-gap and absorption cases and broader W1/reducibility/
coherence remain open.

## Fixed-parametric same-side unary logical introduction (four W1 cases)

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA-256
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also rendered; constant/zero extensions pp.272–273 and 291–292 were
checked against the existing syntax. Verified caches/access artifacts are in
source-consultation.json; historical access records are preserved. No new
source discrepancy was confirmed.

| Source location | Exact local scope / condition | Lean counterpart and actual proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ=∧L | Left conjunction introduction wholly inside one fixed gap or terminal tail; every selected contraction copy is parametric. | `GapLogical.interior/terminal .conj`; `W1.SameSideLogical.interior_left/terminal_left`. Actual conjLeft.toTerm square, not a coherence assumption. |
| §11.2 p.252, right analogue | Right disjunction introduction at the dual fixed positions. | Concrete .disj data and interior_right/terminal_right; actual disjRight.toTerm coproduct square. |
| §11.2 pp.248–249, cluster and rank | Consumed whole-formula A/B positions have no descendant; introduced D is a leaf; surviving positions have one predecessor; sum every selected copy. | At.fixed partial map/reverse, complete ordered selected transport, exact predecessor singleton, existing principal-leaf theorems and contraction sums. |
| §11.2 p.251 W4 / broader configurations | A contraction involving the logical principal formula is a different case. | Excluded here by concrete gap/tail placement and positional distinctions even D=C; W4 and remaining W1/W2–W6 stay separate. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants/atomic zeros remain admitted; whole-formula constants still have positions. | Unchanged syntax, genuine Empty P constant proofs, arbitrary cut-containing premises and witnessed-zero policy. |

The source's broader Semilattice Coherence appeal is replaced for these four
instances by derived component calculations and universal properties. No
strictified equality or new presentation equation is assumed.

All four concrete results prove the exact list/count equalities with G/At/Route
casts. Both consumed whole-formula slots map to none; the all-position partial
square and ordered selected flatMap transport compile, with every selected
copy proved to survive and both lengths n. Both consumed categorical component
cases are separately derived before universal extensionality proves the actual
toTerm squares. Reduced denotation equality then follows with associativity.
Retained ranks lose n/n−1 at contraction/whole endpoint, principal ranks are
2→1, and all other final fixed ranks equal 2+rho of a computed original upper
position. Count/CutFree/Atomized/full tagged relations are preserved, with both
Atomized predicates equal f.Atomized. A=B=C and D=C are permitted positionally.
No new equation/primitive or coherence input. See
[the report](GENTZEN_W1_SAME_SIDE_LOGICAL_REPORT.md) and both author-side reviews.
Other W1 configurations, W2–W6 and general reducibility/coherence remain open.

## Fixed-gap disjoint same-side contractions (two W1 cases)

The directly consulted source is Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed pp.248–253 correspond to PDF pp.260–265, one-based. Printed p.251
was also inspected in rendering. Source-access artifacts and hashes are
retained; historical access records are unchanged. No new source discrepancy
was confirmed.

| Source location | Typed local condition | Lean construction / actual proof input |
| --- | --- | --- |
| §11.2 p.251 (W1), γ=wL | Inner E contraction is entirely inside one fixed outer C gap; every outer selected C occurrence is parametric through it. Independent n,m≥2. | `Disjoint.fixedGap`, all eight `Data.upper/lowerC0/C1/E0/E1` equalities, `W1.DisjointContraction.fixedGap_left`. |
| §11.2 p.252, right analogue | Same fixed-gap placement in the succedent, actual G.contractR constructor order. | `fixedGap_right`; separately typed coproduct square and denotation calculation, without arrow negation. |
| §11.2 p.248, clusters / upper parametric sequences | Selected copies of one family have singleton fibers through the other contraction, with all equal-label tags retained. | `selectedC/E_transport`, `selectedC/E_singleton`, `xC/xE_fiber`, `other_fiber`. |
| §11.2 p.249, rank counts all cluster nodes | Sum all n or m selected copies; count a single node on the other retained/fixed path. | Actual `ContractionBlock.rankL/R_sum/fixed`; four table entries for each side, both balances, strict comparisons and other-position 2+rho. |
| §11.2 p.251 (W3) | Shared-selected-copy contraction, where a retained inner position is itself selected by the outer contraction. | Separate from these W1 instances and now proved in the W3 section below; excluded here by fixed-gap separation and distinct retained indices, including C=E. |
| §11.2 pp.250–253, Reducibility/Blocked-w | Later applications tie a contraction to a cut and control replacement at all affected sites. | Not supplied by these two local commutations or the displayed two-position sum. |

The source's Semilattice Coherence appeal is replaced for these instances by
a concrete positional square and the already proved product/coproduct universal
component laws in Reduced.Hom. No source citation is treated as a Lean proof.
Constants and atomic-zero bases remain available through the unchanged Gentzen
syntax; no new constant/zero equation or empty-context identification is used.

The exact eight equalities/routes, ordered selected-list transports and both
families' complete fixed fibers are constructed from original Data only.
Retained E/C positions satisfy xE<xC even C=E. The rank table is old=(LC+n,LE+1)
and new=(LC+1,LE+m), independently on either sequent side. Other final fixed
positions have equal 2+rho at a unique common original coordinate. Exact
count/predicate/full tagged occurrence preservation follows without coherence;
S(old)+m=S(new)+n permits an actual 2/3 increase. See
[the report](GENTZEN_W1_DISJOINT_CONTRACTION_REPORT.md) and both author-side reviews.
Terminal-tail and shared-selected W3 cases are now proved below; interleaved
disjoint cases and broader W1/reducibility remain separate/open.


## Terminal-tail disjoint same-side contractions (two W1 cases)

The same hash-verified September 2007 source was consulted at §11.2,
printed pp.248–253/PDF pp.260–265, including rendered p.251. No new source
discrepancy is asserted; access evidence is retained under
`provenance/wsl-gentzen-w1-terminal-tail-contraction/source-access/`.

| Source location | Typed local condition | Actual Lean proof |
| --- | --- | --- |
| p.251, W1, γ=wL | E contraction lies in the fixed terminal tail of the C contraction; all C-selected copies remain parametric. | `TerminalContraction.terminalTail`, eight proved `Data.upper/lowerC0/C1/E0/E1` identities and `W1.DisjointContraction.terminalTail_left`. |
| p.252, right analogue | Same placement in the succedent with actual G.contractR. | `terminalTail_right`, separately typed coproduct square, no arrow-negation principle. |
| pp.248–249, parametric ancestry and ranks | Complete ordered selected families and fixed singleton contributions. | `selectedC/E_transport`, lengths n/n/m/m, concrete prefix/tail separation, complete singleton/composite fibers and full rank sums. |
| p.251, W3 | Retained inner occurrence is selected by the outer contraction. | Now proved in the W3 section below; excluded from these terminal W1 instances by distinct retained indices and positional separation, including C=E. |

For es=H::hs, F=(repeated C gs++U)++repeated E es++V and
K=(gaps gs++C::U)++gaps es++E::V, both actual old/new pairs have exact
types G P K Δ or G P Γ K. The generic ContractionFrame stores raw contraction
descriptions and endpoint identifications, not desired squares or rank laws.
The concrete terminal Data proves every required law. Its all-position
copy_splice_tail identity and universal components derive product/coproduct
squares; actual contraction denotations and associativity give Reduced
equality without coherence or reflection of occurrence equality.

The retained indices are xC=(gaps gs).length and
xE=(gaps gs).length+1+U.length+(gaps es).length, so xC<xE. This differs
from the preserved interior construction's xE<xC. For independent n,m≥2,
old ranks are LC+n,LE+1 and new ranks are LC+1,LE+m on either side.
S(old)+m=S(new)+n; the actual 2/3 example increases S by one. Other fixed
positions have equal 2+rho ranks at the unique common original. Cut counts,
CutFree/Atomized and complete tagged relations are preserved without a new
atomicity hypothesis. See [the report](GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_REPORT.md)
and both author-side reviews for exact examples and verification.

Shared-selected W3 fusion is now proved below. Disjoint interleaving,
remaining exchange/W1/W2–W6, all-site rank control, Reducibility, Blocked-w,
cut elimination and coherence/maximality remain separate/open.


## Shared-selected contraction fusion (W3)

The same hash-verified September 2007 source was consulted at §11.2,
printed pp.248–253/PDF pp.260–265, with printed p.251 inspected in rendering.
W3 requires the retained inner occurrence to be selected by the outer
contraction. This is the positional hypothesis of the concrete public theorems,
not an inferred property of equal formula labels or a disjoint W1 condition.

| Source location | Exact correspondence | Lean proof |
| --- | --- | --- |
| p.251 W3, same basic sequence with two descriptions | repeated C hs++Λ = gaps gs++C::Θ, with explicit casted shared membership. | SharedContraction.Data.identify/Shared and W3.SharedContraction.fusion_left/right. |
| p.251 W3, suitable single-contraction subscripts | Compute ordered original selected family and actual flat gaps/tail, n+m−1 copies. | ContractionSelection.fuse; upper/lower/count; conversion back to existing ContractionBlock; Data.arity/selected_originals. |
| pp.248–249, complete cluster ancestry | Retained composite fiber is the complete ordered flat selection; every other final fiber is a computed unique original. | Data.square/retained_fiber/other_fiber/original_flat. |
| p.251 W3, old rank k+1+l+m versus flat k+l+1 | Complete grouped fibers are a permutation; all m intermediate nodes contribute. | TraceRoute.fiber_comp_perm/sum_fiber_comp, selected_sumsL/R, outer_rankL/R, retained_rankL/R. |
| p.252 right analogue | Actual right-side constructors and correctly variant coproduct equation. | Separately typed fusion_right, denoteR and all right rank/preservation laws. |

The actual endpoint types are G P K Δ and G P Γ K, K=gaps hs++C::Λ,
under arbitrary P,C and existing premises, independent n,m≥2, hI and shared
membership. No atomicity, CutFree, Atomized, DecidableEq, nonempty P or
coherence premise is required. The auxiliary selection stores positional
choices, not an assumed fusion law or new Gentzen primitive. Universal
component extensionality gives product/coproduct identities before Reduced
equality; occurrence equality is derived afterward.

Old retained/outer rank equals the flat counterpart plus m. Every other final
same-side position has ranks 2+rho(f,a) and 1+rho(f,a) at its proved common
original. Counts, CutFree/Atomized and complete tagged relations are preserved.
Inhabited equal-label, 2/3 and 3/2 arities, three shared offsets, Empty-variable
constants, compounds and actual signed cuts compile. See
[the W3 report](GENTZEN_W3_SHARED_SELECTED_CONTRACTION_REPORT.md) and reviews.

Terminal selected-thinning W2 and its right dual are now proved below.
Remaining disjoint interleaving/exchange/W1/W2/W4–W6, arbitrary-context
replacement, Reducibility, Blocked-w, cut elimination, coherence and
unconditional maximality stay open.


## Terminal selected thinning (W2)

The same hash-verified September 2007 source was consulted at §11.2,
printed pp.248–253/PDF pp.260–265. Printed p.251 W2/W4 was inspected in
rendering; p.252 states the right analogue. No new source discrepancy is
asserted. Source-access evidence is retained under
`provenance/wsl-gentzen-w2-selected-thinning/source-access/`.

| Source location | Exact correspondence | Lean proof |
| --- | --- | --- |
| p.251 W2 | A terminal thinning appends C and is selected with the n original gs copies. Replace by direct contraction and exchange past Θ. | SelectedThinning.Data and W2.SelectedThinning.terminal_left. |
| p.252 right analogue | Actual succedent thinning/contraction/exchange, without arrow negation. | terminal_right and separately typed denoteR, ranks and preservation. |
| pp.248–249 complete ancestry | All original positions embed; the new selected leaf has no original predecessor. | Bounded copyIndex_old, separate copyIndex_last, square, selected_transport and complete retained/fixed fibers. |
| p.251 W2 and cluster ranks | Each of n old selected paths gains a node, and the new leaf has rank one. | selected_sumL/R, contraction_lossL/R, endpoint_lossL/R and fixed_equalL/R. |
| p.251 W1 versus W2 | The inserted thinning is selected here, rather than fixed-parametric. | inserted_selected and the appended singleton in outer.selected. |

For arbitrary P,C,gs,Θ, n≥2 and existing premises, F=repeated C gs++Θ,
I=gaps gs++C::Θ, U=F++[C], K=(gaps gs++Θ)++[C]. Both actual outputs
have exact G P K Δ or G P Γ K. Data contains no assumed square or rank
conclusion. The actual all-position square and universal components derive
Reduced equality, without Semilattice Coherence or occurrence/inclusion
reflection. The full outer retained fiber has n+1 positions; either composite
from original F has n. Each other final position has a computed unique common
original, including when all labels equal C.

Old outer rank is LC+n+1, new inner rank LC, and new final retained rank
LC+1. Exact losses n+1/n are strict; every other final same-side rank is
2+rho(f,a) on both proofs. An empty exchange still adds a node. Counts,
CutFree and full tagged relations are preserved. Old Atomized iff
AtomicFormula C and f.Atomized; new iff f.Atomized. Concrete compound
counterexamples rule out an unconditional reverse predicate implication.
Actual Empty P constants, equal-tag calculations and signed cuts compile.
See [the W2 report](GENTZEN_W2_SELECTED_THINNING_REPORT.md) and both reviews.

Terminal selected-logical W4 and its right dual are now proved below,
including the n=2 endpoint tie and fixed-position increases. Remaining local
cases, arbitrary-context rank control, Reducibility, Blocked-w, cut elimination,
coherence and unconditional maximality remain separate/open.


## Terminal selected logical introduction (W4)

The same hash-verified September 2007 source was consulted at §11.2,
printed pp.248–253/PDF pp.260–265, with p.251 inspected in rendering.
No new discrepancy is asserted. Source-access material:
`provenance/wsl-gentzen-w4-selected-logical/source-access/`.

| Source location | Exact correspondence | Actual Lean proof |
| --- | --- | --- |
| p.251 W4 | Selected terminal logical principal; inner n-copy contraction, introduction, final two-copy contraction. | SelectedLogical.Data and W4.SelectedLogical.terminal_left. |
| p.250 (w ∧ 1), p.251 W4 | Final contraction selects retained and principal C at gaps [gaps gs,Θ]. | Actual last block/constructors and last_selected=[k,q]; local shape only, no general Blocked-w input. |
| pp.248–249 ancestry | Both A/B slots consumed, every original selected C survives. | partial_square, selected_survives/transport, both principal empty fibers, full retained/fixed fibers. |
| p.251 source rank comparison | New inner rank is below old outer by n+1. | selected_sumL/R, contraction_lossL/R and strictness. |
| p.252 right analogue | Actual disjR/contractR, without arrow negation. | Separately typed terminal_right, coproduct_square, ranks and preservation. |

For C=conj A B on the left or disj A B on the right, set
R=repeated C gs++Θ, S=gaps gs++C::Θ, F=R++[A,B], I=S++[A,B],
U=R++[C], J=S++[C], K=(gaps gs++Θ)++[C]. Original A,B,gs,Θ,
n≥2 and existing f give actual outputs G P K Δ / G P Γ K. No atomicity,
freshness, nonempty P, DecidableEq or coherence premise. The positional W2
facts are reused without replacing logical introduction by thinning.

Complete ordered selections have lengths n/n+1/two at the three contractions.
Both original partial retained fibers have n entries; every other final
position has a computed common original and complete singleton fibers.
The partial whole-formula square is supplemented by both consumed categorical
components before universal extensionality. Product paths are ante K→ante F;
coproduct paths succ F→succ K, in the original Reduced category.

Old outer rank=LC+n+1, new inner=LC, new final retained=LC+3.
Final rank ties for n=2 and decreases for n≥3. Every other fixed same-side
rank increases from 2+rho to 3+rho. Counts, CutFree/Atomized and complete
tagged relations are preserved. Compound principals need no atomicity condition.
Inhabited Empty/compound/equal-tag/tie/increase/signed-cut examples compile.
See [the W4 report](GENTZEN_W4_SELECTED_LOGICAL_REPORT.md) and reviews.

The G.mix f g single-premise W5 placement and right dual are now proved
below. Other local cases, arbitrary-context rank control, Reducibility,
Blocked-w, cut elimination, coherence and unconditional maximality remain open.


## W5 single-premise mix, selected g in G.mix f g

The same hash-verified September 2007 source §11.2 was consulted at printed
pp.248–253/PDF pp.260–265, including rendered p.251 and p.252 continuation.
No new source discrepancy. Source material:
`provenance/wsl-gentzen-w5-single-premise-mix/source-access/`.

| Source location | Exact correspondence | Actual Lean proof |
| --- | --- | --- |
| p.251 first W5 equation | Contract only g in mix(f,g), with f a fixed suffix. | W5.SinglePremiseMix.single_premise_left and actual oldL/newL. |
| p.252 (m nat) | Actual append comparison and mix naturality in Reduced. | ContractionBlock.extend_join/split/product/coproduct/mixL/R. |
| pp.248–249 complete clusters | All selected paths belong to g; every actual mix and opposite contraction node is counted. | Complete branch predecessors/fibers, ordered transport, selected sums and full rank table. |
| p.252 right analogue | Actual right-side contraction and coproduct comparison. | single_premise_right, right component/rank/preservation laws; no arrow negation. |
| p.252 other placements/both-premise case | Separate from the first W5 equation. | G.mix g f is now proved below; mixed-premise/binary logical cases remain open. |

For F=repeated C gs++Θ, K=gaps gs++C::Θ and n≥2, original existing
f/g give exact G P (K++Φ) (Δ++Ψ) / G P (Δ++Φ) (K++Ψ).
No atomicity, freshness, DecidableEq, nonempty-P or coherence hypothesis.
Actual extension with unchanged gs, universal components and inherited mix
naturality give denotation equality; occurrence equality follows afterward.
The complete selected list comes only from g, even for equal labels.
Both branch traces, retained/fixed/suffix fibers and common originals compile.

Old outer=LC+n; new retained=LC+1. Losses n/n−1 are strict.
Every fixed/opposite g rank is 2+rho on both; f ranks old 2+rho/new
1+rho on either side. The historical task predicted opposite old=1+rho,
omitting the outer contraction node. Existing opposite-contraction laws and
actual cut examples refute that prediction; definitions/source/manuscript are
unchanged. Current records use the proved correction.
Counts, CutFree/Atomized conjunctions and full tagged relations are preserved.
Empty/compound/equal-label/two-three-copy/signed-cut examples compile.
See [the W5 report](GENTZEN_W5_SINGLE_PREMISE_MIX_REPORT.md) and reviews.

The G.mix g f placement is now proved below.
Mixed-premise/binary W5/W6, remaining W1/W2, arbitrary-context rank control,
Reducibility, Blocked-w, cut elimination, coherence and unconditional
maximality remain separate/open.

## W5 other single-premise mix, selected g in G.mix g f

Pinned September 2007 §11.2 p.252 explicitly gives the analogous mix(g,f)
placement; the right analogue follows later on the same page. Printed
pp.248–253 are PDF pp.260–265 one-based. Rendered p.252/PDF p.264 and the
cached full PDF/text were consulted; hashes/access evidence are retained under
provenance/wsl-gentzen-w5-other-premise-mix/. No new source discrepancy.

| Source anchor | Typed correspondence | Actual proof |
| --- | --- | --- |
| p.252 mix(g,f) analogue | g contains every selected copy; f's contexts precede g's. | W5.OtherPremiseMix.other_premise_left; output G P (Φ++K) (Ψ++Δ), prefix gaps (Φ++H)::hs derived from original gs. |
| p.252 right analogue | Actual contractR on g's suffix, with f's target prefix. | other_premise_right; output G P (Φ++Δ) (Ψ++K), prefix gaps (Ψ++H)::hs. |
| p.252 (m nat) | Concrete prefix product/coproduct comparisons before inherited naturality. | prepend_join/split, prepend_product/coproduct, otherMixL/R; no coherence/reflection. |
| pp.248–249 clusters | Whole ordered g selection and all fixed/opposite branch positions. | OtherMix branch squares/fibers and W5.OtherPremiseMix selected/fixed/opposite rank laws. |
| p.250 Reducibility subterm replacement | One selected proof occurrence must be rebuilt inside a surrounding proof. | Typed addresses and reconstruction are now proved below; local equality alone still does not prove Reducibility. |

For n≥2, derive gs≠[] and reuse ContractionSelection.prependFixed. Exact
selected list is d.selected.map (At.shift Ξ); retained index is
Ξ.length+(gaps gs).length. g-suffix fibers are full original contraction
fibers, f-prefix fibers are singleton, with other branch empty. Equal-label
f positions are excluded. Full old outer fibers are separately proved.
Old outer=LC+n, new retained=LC+1; contraction loss n, endpoint loss n−1.
Fixed/opposite g ranks are 2+rho on both, f 2+rho→1+rho on both sides.
Counts, CutFree/Atomized and complete tagged relations are preserved.
Inhabited Empty/compound/equal-label/n=2/3/signed-cut examples compile.

See [the report and track/drift audit](GENTZEN_W5_OTHER_PREMISE_MIX_REPORT.md)
and the completed replacement checkpoint below.
Mixed-premise/binary W5–W6, crossing/absorption and other W1/W2 cases,
source classification, tied-site rank/multiset control, Reducibility,
Blocked-w, cut elimination, restricted coherence, PositiveCoherence,
Reduced.Faithful, Boolean Coherence and unconditional maximality remain open.

## Proof-occurrence replacement and integration into surrounding Gentzen proofs

Pinned September 2007 §11.2 p.250's Reducibility Lemma replaces one selected
subterm in a topmost cut. Printed pp.248–253 are PDF pp.260–265 one-based;
rendered p.250/PDF p.262 and cached text were consulted. Access evidence is
retained under provenance/wsl-gentzen-proof-replacement/; no new discrepancy.

| Source anchor | Actual typed construction | Boundary |
| --- | --- | --- |
| pp.248–249 subterm occurrences | Existing Premise/ProofAddress reused; inserted proof has a new address with the same branch path, even with identical siblings. | No new tracing/rank definition; cluster transport is not asserted. |
| p.250 replacing the chosen subterm | Premise.rebuild and ProofAddress.replace preserve exact outer endpoints, all rule parameters and unchanged siblings; recovery/composition laws compile. | Any replacement needs the same local sequent; no global normalization assumption. |
| p.250 equality after replacement | replace_denote derives outer equality from local Reduced equality using actual G.denote and rule congruences; tagged relation follows. | No occurrence reflection or coherence. |
| pp.251–252 W5 | Existing OtherPremiseMix left/right equations now lift at any valid address, preserving counts and existing CutFree/Atomized. Concrete nested signed-cut and Empty examples compile. | No global rank decrease is inferred. |
| p.250 blocked/reducible definitions; W1–W6 | Next source-faithful classification will select the required local transformation. | Still open, with missing cases and tied-site rank control separate. |

Both cutCount and proofSize obey exact additive one-occurrence balances;
proofSize is not an asserted elimination measure. Address append has unit,
associativity and path laws; replacement at a composed address agrees with
nested reconstruction. Root/replacement predicates supply CutFree/Atomized
preservation; arbitrary inputs need no atomicity or CutFree to construct replace.

See [the integration report](GENTZEN_PROOF_REPLACEMENT_REPORT.md) and
[the classification continuation](CODEX_GENTZEN_BLOCKED_CLASSIFICATION.txt).
Source Blocked/Reducible definitions, complete dispatch, remaining local cases,
tied-site rank/multiset control, Reducibility/Blocked-w/clean cuts, cut
elimination, restricted coherence, PositiveCoherence, faithfulness/Boolean
Coherence and unconditional maximality remain open.

## Source blocked patterns, reducible occurrences and selection dispatch

Pinned September 2007 §11.2 pp.248–253, especially p.250's seven patterns,
reducibility condition and pp.251–253 W1–W6/right analogue, were consulted.
The [classification report](GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md) maps each
pattern to actual typed constructors/gaps and records the full finite case ledger.

BlockedL/R use actual two/three-copy contractions. disjLLast explicitly moves
the source terminal inputs/principal through the head-form primitive; sourceRight2/3
use the existing first-retaining right exchange macro around the canonical
last-retaining contraction. No macro rank-invariance or strictification is claimed.
ProperContains uses a nonempty typed suffix address. ReducibleL/R retain the
actual cut-side cluster membership and contraction position and require only
proper containing tied contractions blocked. Root, sibling and nested signed
examples distinguish the occurrence from its proof value.

PortOrigin gives each complete selected position empty/singleton/branching
predecessor evidence with actual premise tags. Ordered profiles have a unique
shared/introduced/parametric and first/second/both regime. Actual arity≥2 and
CutFree exclude basis/cut heads by proof. selected_fresh_rule,
selected_second_binary and selected_shared_rule restrict the possible head/
regime pairs. This is exhaustive logical classification, not certified rewrite
dispatch. Administrative exchanges remain actual heads. All fourteen blocked
patterns and all seven profile regimes have inhabited tests, including Empty
constants, compounds, equal labels, both signs and nested tied contractions.

Next close [mixed-premise W5](CODEX_GENTZEN_MIXED_W5_DISPATCH.txt), with singleton
branch boundaries, explicit blocked outer contraction, profile extraction and
nested replacement. Other missing local cases, complete dispatch, all affected
tied-site ranks, Reducibility/Blocked-w/cut elimination and coherence remain open.
