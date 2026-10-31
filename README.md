# Došen–Petrić maximality in Lean

## Palomar registration and arXiv preparation (30 October 2026)

Registered as [**PALOMAR-2026-10-30-000014, version 1**](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000014&version=1). The permanent entry,
archived mechanical evidence and source-preservation tag bind the exact proof
commit below. The [registration report](docs/PALOMAR_REGISTRATION_REPORT.md)
records the public readback; a separate [HTML delivery diagnostic](docs/PALOMAR_RENDER_DELIVERY_DIAGNOSTIC.md)
records the analytics injection in two served render pages.

The arXiv package is ready in [submission/arxiv-v10](submission/arxiv-v10/README.md).
V10 retains the ChatGPT and Codex disclosure and MSC 2020 Primary 03G30;
Secondary 03F07, 18A32, and cites the registered proof. No arXiv submission has
been made. V10 carries the terminology revision; definitions, statements, proofs and all previous versions are preserved.

The verified package was merged into main through `23ec1bc`. It selects five statements
in `DosenPetric.Palomar`: both
actual-source maximality proofs, their congruence dichotomy, a nonzero variable
identity and the empty top-to-bottom hom-set. The independent
[Challenge](Challenge.lean) contains the concrete presentation and five theorem
proof holes; [Solution](Solution.lean) imports the proved production declarations.
[The correspondence account](docs/PALOMAR_STATEMENT_CORRESPONDENCE.md) gives the
raw/quotient relation and derived-negation proofs. The complete-paper scope below
is preserved separately from this five-statement selection.

Use the pinned Lean 4.35.0 toolchain. `lake build Solution` checks the production
proof package. `lake build Challenge` compiles the independent statement; its five
intentional proof warnings are confined to that library. Production checking
retains `warningAsError = true`. `bash scripts/verify.sh` runs the strict build
and transitive axiom audit. The public configuration is [comparator.json](comparator.json).
Protected local comparison and independent-kernel outcomes are recorded in
[the registration report](docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md), with exact
commands, inputs and diagnostics under `provenance/wsl-palomar-registration-20261030/`.

The author approved Apache-2.0 publication, including the original manuscript
and retained history, on 30 October 2026. The repository is public. Its immutable
submission SHA remains `2e771844077fd8cebfbe365230f13d4dd13a75b1`. Lean stays at 4.35.0.
[Official full preflight](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41129351329) passed with the pinned standard profile;
the [stage report](docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md) distinguishes its
result from local verification and final registration. [Service verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41137470993)
also passed; [the service report](docs/PALOMAR_SERVICE_VERIFICATION_REPORT.md) records its evidence. The
publication order is Palomar Registry registration first, then arXiv submission.

## Current complete full-paper formalization (29 October 2026)

Current manuscript: [v10 PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v10.pdf) and [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v10.tex), dated October 31, 2026. The original v9 release and all earlier versions remain preserved.
The [v10 report](docs/MANUSCRIPT_V10_REPORT.md) records the terminology revision,
successful TeX builds and version preservation. Every manuscript revision must
increment the version number; the rule is recorded in AGENTS.md.

All mathematical content of v7 is now proved for the actual equation-generated
Došen–Petrić presentation, with the status/citation refresh preserved in v8.
This includes both maximality routes, the full-source model corollary, all
unnumbered claims, the complete substitution action and actual occurrence/block/
profile/ordinal/renaming/skeleton constructions, all examples and all three
appendices' equations and diagrams. All published inputs used by the actual
proofs are proved or supplied by compatible verified core Lean constructions;
no uninstantiated handler/coherence/conclusion field remains at those endpoints.

The active exhaustive ledger is [MANUSCRIPT_COMPLETE_CLAIM_MAP.md](docs/MANUSCRIPT_COMPLETE_CLAIM_MAP.md).
See [completion report](docs/FULL_PAPER_COMPLETION_REPORT.md),
[hostile review](docs/reviews/FULL_PAPER_COMPLETION_HOSTILE.md) and
[writing review](docs/reviews/FULL_PAPER_COMPLETION_WRITING.md), plus the separate
FULL_SOURCE_MODELS_REPORT.md and all preserved earlier reports. The three old
milestones are explicitly separate rows in the current map. Full-paper closure
includes every additional appendix/model/operation obligation; it is not inferred
from actual maximality alone. Exact mathematical-source commit: 630c4b6e47da16a1434476a211fd29ce6adc5569.

Local checks cover 883 Lean files, 14,849 declarations, all 35 public files,
full transitive dependency/source closure and 74 expected rejections. Exact exits,
hashes, checked/committed archive and delivery paths are in provenance/wsl-appendix-a/.
Both completion reviews are local author-side. At mathematical completion on
29 October, independent replay, Comparator, official preflight, service verification
and publication had not yet been performed and the repository was private. Their
subsequent results and public registration are recorded above. The original stash and all preceding source/results/receipts persist.

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
See [report](docs/FULL_SOURCE_MODELS_REPORT.md),
[hostile review](docs/reviews/FULL_SOURCE_MODELS_HOSTILE.md) and
[writing review](docs/reviews/FULL_SOURCE_MODELS_WRITING.md). Both reviews are local
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
with committed bytes. See [report](docs/FULL_PAPER_CORRESPONDENCES_REPORT.md),
[hostile review](docs/reviews/FULL_PAPER_CORRESPONDENCES_HOSTILE.md),
[writing review](docs/reviews/FULL_PAPER_CORRESPONDENCES_WRITING.md). Reviews are local
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
is read back and compared with committed bytes. See [report](docs/SHORT_QE_REPORT.md),
[hostile review](docs/reviews/SHORT_QE_HOSTILE.md),
[writing review](docs/reviews/SHORT_QE_WRITING.md). Reviews are local author-side;
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
See [report](docs/SOURCE_MAXIMALITY_REPORT.md),
[hostile review](docs/reviews/SOURCE_MAXIMALITY_HOSTILE.md),
[writing review](docs/reviews/SOURCE_MAXIMALITY_WRITING.md). Reviews are local author-
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

See [report](docs/GENTZEN_COHERENCE_REPORT.md),
[hostile review](docs/reviews/GENTZEN_COHERENCE_HOSTILE.md),
[writing review](docs/reviews/GENTZEN_COHERENCE_WRITING.md).
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


## Retained unrestricted Gentzen cut elimination checkpoint (29 October 2026)

`cut_elimination : CutElimination P` and
`atomized_cut_elimination : AtomizedCutElimination P` are proved for arbitrary P.
Every G proof has a CutFree representative at its exact original sequent with
Reduced equality; the second result also supplies Atomized. No handler, Clean,
degree or rank hypothesis is supplied by the caller. Coherence and full-paper
maximality remain separate continuing obligations; the three milestones are unchanged.

| Construction | Actual declaration | Scope |
| --- | --- | --- |
| All seven blocked cases on each side | CutCommutation.blocked_right_rank_step / blocked_left_rank_step | Original lower tag, full Clean and strict original-rank recursion; node-free gammaDisj association. |
| Every parametric G constructor on each side | CutCommutation.parametric_right_rank_step / parametric_left_rank_step | Actual original child with unchanged opposite premise before reconstruction. |
| Complete leaf/parametric/lower dispatch | PositionalCut.clean_rank_step | Clean gives root blockedness; two leaves invoke exhaustive rank-two degree step. |
| Fixed-degree all-ranks clean theorem | PositionalCut.clean_elimination | Strong original selected-rank induction under strict DegreeBelow. |
| Arbitrary cut-free premises at that degree | PositionalCut.cutFree_degree_step | Simultaneous cleaning follows completed all-ranks theorem; no cleaned-rank bound. |
| Strong formula-degree induction | head_cut_elimination | No supplied degree hypothesis; smaller degrees allow arbitrary ranks. |
| Arbitrary tagged cut-free premises | PositionalCut.cutFree_elimination | Exact erased output and Reduced equality. |
| Arbitrary proof trees, including nested cuts | G.cut_free_normalization; cut_elimination | Exact original sequent and Reduced equality. |
| Simultaneous final atomization | atomized_cut_elimination | Actual unrestricted CutFree/Atomized representative. |

All twelve binary branches and fourteen blocked reductions are reused unchanged.
Constants have degree one, literals zero; conjunction cuts A-then-B and disjunction
B-then-A. No returned-rank bound, output blockedness or general G duality is assumed.
Both concrete Appendix C source/rank correspondences remain proved. All nine
manuscript blobs, prior results, stash and delivery receipts are preserved.

See [report](docs/GENTZEN_CUT_ELIMINATION_REPORT.md),
[hostile review](docs/reviews/GENTZEN_CUT_ELIMINATION_HOSTILE.md),
[writing review](docs/reviews/GENTZEN_CUT_ELIMINATION_WRITING.md) and
[constructor/tag map](docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Evidence: provenance/wsl-gentzen-global-induction/. Strict pinned verification,
all public checks, actual global witnesses and 44 expected rejections are recorded
with actual counts/exits/hashes in FINAL_VERIFICATION.json. Checked source bytes
are archived and compared with committed bytes. Reviews are local author-side;
independent replay, Comparator, official/service verification and publication
remain separate unperformed statuses. DELIVERY_REGISTER.json records exact
committed-byte repository/Downloads paths and verified conflict-preserving copies.

Next prove restricted mix/positive/reduced/Boolean coherence, instantiate the
intended-presentation and uniform-substitution/congruence bridges, and complete
both maximality routes, the model corollary and all remaining mathematical claims
in all three v7 appendices. The historical checkpoints below retain their dated
scope; their open normalization statuses are superseded by this current table.
Continue under the full-paper authorization without another routine checkpoint.

## Retained v7 manuscript checkpoint: authorized errata appendix

V7, dated 28 October 2026, preserves all v6 mathematical content and adds the
exact author-requested Appendix C plus its introduction roadmap sentence.
Appendix C records the source p.260 inequality r' < r and p.262 right-rank-one
qualification. The entire Appendix C is on PDF p.12, followed by the unchanged
disclosure; references are on p.13. The final local TeX build resolves all
references/citations and has no overfull/underfull boxes or warnings. All ten
TikZ diagrams, Appendices A–B, the disclosure and bibliography are unchanged
in source. The v4/v5/v6 source/PDF pairs remain byte-identical.

Source at this checkpoint: `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.tex`,
SHA-256 `70b4f82c03e165e6a6da36d869968531a509341b93f90eedde964506568c8e96`. Checkpoint PDF: the same basename with .pdf,
SHA-256 `957048538137ef085c0a581b399272db753377b76c6a83c1adc307ad8b2e256a`. Evidence: `provenance/wsl-manuscript-v7/`;
report: [MANUSCRIPT_V7_ERRATA_REPORT.md](docs/MANUSCRIPT_V7_ERRATA_REPORT.md); reviews:
[hostile review](docs/reviews/MANUSCRIPT_V7_ERRATA_HOSTILE.md),
[writing review](docs/reviews/MANUSCRIPT_V7_ERRATA_WRITING.md).

The manuscript addition is complete. Appendix C p.260 has its actual source
equation and both strict original-child rank inequalities. Its p.262 concrete
sequential source/rank correspondence is proved by BlockedDisjFirst.source_equation,
fresh_clean_and_rank, the three fresh-principal/total-rank declarations and
blockedL_disjunctionFirst_rank_step. Both erratum rows are closed. Global cut elimination is now proved by the
current unrestricted interfaces; coherence and the other full-paper obligations
retain their separate statuses. The underlying v6 target is supplemented, not reduced.


## Retained opposite logical checkpoint (28 October 2026)

Historical scope through 67de18a; the current continuation above supersedes its
open same-side unary and opposite structural-wrapper tasks.

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
[report](docs/GENTZEN_POSITIONAL_CUTS_REPORT.md); reviews:
[hostile review](docs/reviews/GENTZEN_POSITIONAL_CUTS_HOSTILE.md),
[writing review](docs/reviews/GENTZEN_POSITIONAL_CUTS_WRITING.md).

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

## Full-paper formalization target

The authorized target is the complete mathematical content of manuscript v7:
the short q_A/e_A proof, maximality for the actual equation-generated category
with all inputs proved, the model corollary, unnumbered claims and all three
appendices. Full local Reducibility is one prerequisite. Keep the three
milestones below separate and preserve the existing symmetric-fold alternative.
See the [full-paper contract](docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md),
[statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[correction record](docs/MANUSCRIPT_CORRECTIONS.md). Tagged substitution and its
ordinal-coordinate correspondence remain required content. No manuscript
revision or new publication claim is implied by this checkpoint.

## WSL2 setup

The intended directory is `/home/flengyel/src/Dosen-Petric-Maximality`, on the
WSL2 Linux filesystem. With GitHub SSH authentication configured and Elan installed:

```bash
mkdir -p /home/flengyel/src
git clone git@github.com:flengyel/Dosen-Petric-Maximality.git /home/flengyel/src/Dosen-Petric-Maximality
cd /home/flengyel/src/Dosen-Petric-Maximality
bash scripts/setup-wsl.sh
```

If that directory already exists, inspect its Git status and origin before
updating it. See [WSL2 instructions](docs/WSL2_SETUP.md) for prerequisites.
The setup installs only the pinned project toolchain and runs verification;
it does not change Elan's global default. Local build and audit outcomes are recorded in validation.

Initial modules use Lean core only. The matching Mathlib release is recorded
at full commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; it is not an active
dependency. The committed Lake manifest therefore has no dependency packages.

## Proof scope and continuation

1. Contextual collapse relative to explicit structural and faithful-interpretation data.
2. Maximality relative to explicit coherence, normalization, presentation, and substitution inputs.
3. Maximality for the actual Došen–Petrić presentation after those inputs are established.

The conditional theorems do not complete the intended-presentation milestone
gates. Many syntactic bridges above are constructed, while coherence and
remaining congruence/substitution interfaces are still required. Coherence
applies in the original category; zero arrows require a witness that the
hom-set is inhabited.
The [statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[coverage map](docs/MANUSCRIPT_COVERAGE.md) record the precise boundary.
Use [the next-session prompt](docs/CODEX_NEXT_SESSION.txt) to continue in WSL2.

The manuscript at this historical checkpoint is v7: [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.pdf).
It gives a shorter contextual-collapse proof from the published structural
isomorphisms, distinguishes the result from Joyal's theorem, and describes the
conditional Lean formalization. No earlier explicit statement of the same
maximality theorem was found; derivability from older results does not establish
prior publication. V7 adds the author-requested Appendix C source errata to the preserved v6
baseline. Its TeX build and rendered review pass; the corresponding concrete
Lean rank reductions and the coherence obligations remain open.
See the [corrected novelty review](docs/DOSEN_PETRIC_MAXIMALITY_NOVELTY_REVIEW_2026-10-25.md),
[v6 hostile review](docs/reviews/V6_HOSTILE_REVIEW.md),
[writing review](docs/reviews/V6_WRITING_REVIEW.md),
[Lean scope check](docs/reviews/V6_LEAN_SCOPE.md), and
[validation](docs/V6_VALIDATION.md).
MSC2020: primary 03G30; secondary 03F07 and 18A32.
The v4 [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.pdf)
remain preserved, as do the v5
[TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex) and
[PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.pdf).
[SHA-256 checksums](manuscript/SHA256SUMS) cover all three versions.
The [v5 literature review](docs/LITERATURE_REVIEW_V5_2026-10-23.md),
[manuscript hostile review](docs/reviews/V5_HOSTILE_REVIEW.md),
[writing review](docs/reviews/V5_WRITING_REVIEW.md), and
[manuscript validation](docs/V5_VALIDATION.md) accompany v5.
The [earlier literature comparison](docs/LITERATURE_REVIEW.md) remains available.
The literature searches are bounded and make no exhaustive priority claim.
The current [author-side hostile review](docs/reviews/GENTZEN_FULL_REDUCIBILITY_HOSTILE.md)
and [mathematical-writing review](docs/reviews/GENTZEN_FULL_REDUCIBILITY_WRITING.md)
cover both full local Reducibility statements and outside transport; they are
not independent certification. See the [current report](docs/GENTZEN_FULL_REDUCIBILITY_REPORT.md),
[governing full-target instructions](docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
[current continuation](docs/CODEX_NEXT_SESSION.txt),
[historical classification report and case ledger](docs/GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md),
[superseded mixed-W5-only continuation](docs/CODEX_GENTZEN_MIXED_W5_DISPATCH.txt),
[preceding integration report](docs/GENTZEN_PROOF_REPLACEMENT_REPORT.md),
[preceding W5 report and track/drift audit](docs/GENTZEN_W5_OTHER_PREMISE_MIX_REPORT.md),
[preceding W5 report](docs/GENTZEN_W5_SINGLE_PREMISE_MIX_REPORT.md),
[preceding W4 report](docs/GENTZEN_W4_SELECTED_LOGICAL_REPORT.md),
[preceding W2 report](docs/GENTZEN_W2_SELECTED_THINNING_REPORT.md),
[preceding W3 report](docs/GENTZEN_W3_SHARED_SELECTED_CONTRACTION_REPORT.md),
[preceding terminal-tail report](docs/GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_REPORT.md),
[preceding disjoint-contraction report](docs/GENTZEN_W1_DISJOINT_CONTRACTION_REPORT.md),
[preceding same-side logical report](docs/GENTZEN_W1_SAME_SIDE_LOGICAL_REPORT.md),
[preceding same-side exchange report](docs/GENTZEN_W1_SAME_SIDE_EXCHANGE_REPORT.md),
[preceding same-side thinning report](docs/GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md),
[preceding logical report](docs/GENTZEN_W1_LOGICAL_REPORT.md),
[preceding contraction report](docs/GENTZEN_W1_CONTRACTION_REPORT.md),
[contraction review](docs/reviews/GENTZEN_W1_CONTRACTION_HOSTILE.md),
[preceding exchange report](docs/GENTZEN_W1_EXCHANGE_REPORT.md),
[exchange review](docs/reviews/GENTZEN_W1_EXCHANGE_HOSTILE.md),
[preceding thinning review](docs/reviews/GENTZEN_W1_THINNING_HOSTILE.md),
[historical contextual-collapse review](docs/reviews/CONTEXTUAL_COLLAPSE_HOSTILE.md)
and [initial review](docs/REVIEW.md) remain available.

## Verification and Palomar

Run `bash scripts/verify.sh`. CI uses the hash-checked official Lean release,
a strict build, source screening, and transitive axiom collection. Evidence
and its limitations are in [validation](docs/VALIDATION.md).

The author requested Palomar registration on 30 October 2026. The
[registration stage record](docs/PALOMAR_REGISTRATION_STATUS.md) and
[local Codex instructions](docs/CODEX_PALOMAR_REGISTRATION.txt) cover the
independent Challenge/Solution package, exact definition correspondence,
independent kernels and the current full official preflight. The completed
mathematical source and full-paper claim map are preserved.

The [current requirements](docs/PALOMAR_REQUIREMENTS.md) pin the verifier to
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; upstream hashes and policy JSON
are retained in `provenance/palomar-registration-2026-10-30/`.
`bash scripts/fetch-palomar.sh` fetches that source into its own revision-specific
directory and preserves the older checkout.

The verified package is merged into main and publicly released under the
author-approved Apache-2.0 license, including the original manuscript and retained
history. Original proposals remain under `docs/palomar/` as historical materials.
The verified source remains `2e771844077fd8cebfbe365230f13d4dd13a75b1`. Official full preflight passed;
service verification also passed. The private review and author’s registration decision remain separate. ArXiv submission
follows successful Palomar registration.
