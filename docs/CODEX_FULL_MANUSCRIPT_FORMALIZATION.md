# Complete Lean formalization of manuscript v7

## Current actual source maximality and derived negation (29 October 2026)

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

See [report](GENTZEN_CUT_ELIMINATION_REPORT.md),
[hostile review](reviews/GENTZEN_CUT_ELIMINATION_HOSTILE.md),
[writing review](reviews/GENTZEN_CUT_ELIMINATION_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
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

## Retained opposite logical checkpoint (28 October 2026)

Historical scope through 67de18a; the current construction above supersedes its
open same-side unary logical and opposite structural-wrapper status. Binary
descent is now checked, while binary equations/reconstructions remain open.

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

## Governing source and instruction order

The active manuscript is v7, dated 28 October 2026. Its source is
`manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.tex`, SHA-256
`70b4f82c03e165e6a6da36d869968531a509341b93f90eedde964506568c8e96`; its PDF has SHA-256
`957048538137ef085c0a581b399272db753377b76c6a83c1adc307ad8b2e256a`. The exact addition and checks are
recorded in MANUSCRIPT_V7_ERRATA_REPORT.md and provenance/wsl-manuscript-v7.
All v6 obligations remain; Appendix C adds the source-rank explanations to
formalize. The source commit is identified by the v7 addition in Git history;
these hashes fix its bytes independently of a self-referential commit identifier.

The preserved reviewed v6 baseline is
`manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex` at commit
`810dcdbccc76a4307028773c561f36b910b5170c`, SHA-256
`2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0`.
The preserved v6 PDF has the same basename. Read the complete CURRENT v7
source and all three appendices, `AGENTS.md`, the statement and coverage maps,
and the presentation correspondence. V6's two appendices remain its historical
baseline; they do not restrict the v7 target.
Follow later explicitly authorized manuscript changes and update the source
anchor and claim ledger together; do not silently change the formal target.

This document governs the overall endpoint. `CODEX_NEXT_SESSION.txt` identifies
the immediate continuation. `CODEX_AFTER_05C6BC8_REDUCIBILITY.txt` and
`CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt` retain their exact mathematical targets
as subordinate instructions for the coherence work. Their older references to
the governing task do not restrict the project to Reducibility. Preserve their
source-shaped statements, rank conditions, and existing verified results.

The three existing milestones remain distinct: the structural collapse
interface, conditional relative maximality, and maximality for the actual
presentation. Full-paper completion is an additional requirement beyond those
milestones. Historical checkpoints are evidence of progress, not current proof
instructions when superseded by the current continuation and maps.

## Required endpoint

For every nonempty variable type P, construct the actual September 2007
equation-generated zero-identity Boolean category B(P), and prove that every
proof congruence closed under uniform endosubstitution which identifies distinct
parallel arrows identifies every parallel pair. Also prove the equivalence
with the statement that the only substitution congruences are equality and
the total congruence.

The final theorem must quantify over the actual source quotient and its actual
proof congruences. Instantiate or prove every interface used by
`relative_maximality`, including the restriction/correspondence for congruences
and substitution closure. Do not replace B(P) by `GeneratedModel`, a relation
category, a structural fragment, or a newly strengthened presentation.

Published mathematical inputs needed by the proof, especially Boolean
Coherence and the particular structural isomorphisms, must have Lean proofs
for this presentation or be supplied by compatible, pinned, verified library
theorems with proved correspondence. A citation, record field, local axiom, or
uninstantiated hypothesis does not discharge an input. Conditional lemmas remain
useful intermediate results and must remain labelled as such.

Complete mathematical content means the definitions, results, constructions,
equations, examples, and diagram identities developed in the paper, including
unnumbered assertions, together with the dependencies needed to prove them.
Bibliographic, historical, novelty, and disclosure prose does not require a
Lean encoding; nor does the task require formalizing every theorem mentioned
only to describe related literature. The paper's concrete non-cartesian-closure
argument does belong to the mathematical target.

## Claim ledger and correspondence

Maintain a complete claim ledger in `MANUSCRIPT_STATEMENTS.md`, with one entry
per numbered result or displayed identity and sufficient entries for the
unnumbered claims. For each entry record the manuscript label or precise prose
anchor, exact Lean declaration and file, hypotheses and universes, correspondence
proof, and status. Distinguish an existing declaration, a conditional theorem,
an instantiated source-presentation theorem, and an open obligation. A source
label cannot be marked complete merely because a weaker contextual consequence
or an analogous result in another model has been proved.

### Procedure for any necessary corrections

If a necessary correction is established during this work, its repair is
included in the task. This applies to manuscript claims, Lean statements and
proofs, source correspondences, citations and exposition. Maintain
`MANUSCRIPT_CORRECTIONS.md` outside the paper. For each confirmed defect record
the exact source anchor, evidence, repair, affected declarations or diagrams,
verification and resolution. Distinguish a confirmed error from an open proof
obligation, a suspected issue and an optional editorial preference. The current
record contains no outstanding confirmed manuscript error; this procedure does
not assert that one has been found.

Apply each justified correction consistently to the mathematical source and
formalization. Rebuild and inspect the PDF whenever its source changes, and run
the relevant Lean checks whenever proof sources change. Update the source
anchor, correction record, claim ledger and continuation together. Do not
silently weaken a statement, omit an appendix, change a definition, or remove
a mathematical qualification to make completion easier. If a substantive repair
cannot be proved, keep the affected claim open and state the exact obstruction.

Carry each accepted correction through the entire affected scope in the same
work pass: definitions, statements, proofs, repeated prose, diagrams, captions,
source comments, formalization, claim maps and reports as applicable. Search for
parallel instances and re-read the connected passages after editing. Preserve
the decision and verified resolution in the external record and continuation;
do not rely on the author's repeating it in later prompts. Record an accepted
editorial preference as such, rather than misclassifying it as a mathematical
error. A later steering message supplements the active task unless it explicitly
replaces it.

### Occurrence-substitution presentation

The tagged-block presentation is a required expository contribution of the
paper. Preserve its separation of outer occurrences, positions within inserted
formulas, and placeholder labels, together with the typed maps, commutative
diagrams and worked example. Its expository contribution is the explicit
organization of these data and their relation to substitution.

Prove exact correspondence with the finite-ordinal formula in
Došen–Petrić, *Proof-Theoretical Coherence*, September 2007, §2.5, pp.45–46.
In particular, verify gamma, both coordinate bijections, the transported delta,
the block locator, empty blocks, repeated labels and noninjective renaming.
An implementation of the ordinal formula alone does not complete this
correspondence obligation. Keep the mathematical account self-contained and
describe the maps and their properties directly; attribute the source formula
and the occurrence-coordinate presentation precisely.

The following list is mandatory coverage, not permission to omit a mathematical
claim found during the complete manuscript read.

| Manuscript component | Required formal content |
|---|---|
| §2 presentation and operations | Typed formula and arrow syntax, generated equality and quotient category; the specified products, coproducts, units and distributor; source correspondence for the primitive and derived operations and equations. |
| §2 negation | Derived contravariant arrow negation, its functor laws, and the specified natural double-negation and De Morgan isomorphisms, including constants. Object-level negation and a double-negation retract alone do not discharge this claim. |
| §2 equations (1)–(3) and zeros | The first-injection equation, equality of the displayed five-arrow zero composite with the source zero identity, the zero law, witness independence, commutation and absorption for inhabited hom-sets. |
| §2 congruences and Theorem 2.1 (`thm:main`) | Closure under every specified arrow operation, including derived negation, pairing and copairing; action of uniform substitution on arrows and endpoint types; actual-presentation maximality in both stated formulations. |
| §3 occurrences and Theorem 3.1 (`thm:coherence`) | Tagged occurrence sets, label maps, coordinate encoding, all stated relation operations, and the actual functor G; soundness and faithfulness for the source quotient, so both directions of the coherence equivalence are proved. |
| §3 unnumbered consequences | Distinct projections and id_p ≠ zero_p; each Hom(top,E) subsingleton; the resulting obstruction to a cartesian closed structure with the specified products; normal-form isomorphisms and their occurrence graphs; preservation of complete signed literal labels. |
| §3 substitution, (4)–(5) | The occurrence-block bijection and inverse, label compatibility and block square; the whole-arrow substitution functor and compatibility with generated equality and operations. Record identity/composition and endpoint transports needed by the appendix and model interpretation arguments. |
| Lemma 4.1 (`lem:isolation`) | Actual typed selector/coselector witnesses for the original endpoint formulas, their exact composite and zero equations after any required interchange of f and g, and the normalized relation calculation. A normalized contextual consequence alone is not the printed witness theorem. |
| Proposition 4.2 (`prop:all-contexts`) | From a new substitution-closed equation to K_A for every A, with both literal signs, whole-arrow substitution, the double-negation square and zero transport. |
| Lemma 5.1 (`lem:structural-isos`) | The particular q_A and e_A maps defined below are isomorphisms in the actual source quotient for every A; both inverse equations and the required substitution transport. |
| Lemma 5.2 (`lem:collapse`) | The short q/e quotient argument below, with only proof-congruence closure once all K_A are given. |
| Corollary 5.3 (`cor:models`) | The statement for every interpretation in every model of the specified presentation, with the interpretation/quotient bridge and substitution stability proved; conclude thinness of arbitrary model hom-sets. |
| §6 formalization mathematics | Retain the existing symmetric-fold proof as a separate route. Identify its displayed composite with mix followed by codiagonal, and prove the parameter independence and symmetry used there. Keep the prose scope aligned with the verified source. |
| Appendix A.1 | Profiles and dependent block sets D and C; injections a_r, b_i; existence and uniqueness of gamma; block projections; the fibre and profile squares; the actual-substitution bijection chi and label square. |
| Appendix A.2 | Prefix sums, both ordinal encodings and their inverses, existence and uniqueness of delta, the ordinal square and coordinate equation, the unique block locator including empty blocks, and correspondence with the book's generalized composition. Prove skeleton-plus-profile reconstruction and its compatibility with substituted patterns; verify the displayed eight-position example and delta(2)=3. |
| Appendix A.3 | Renaming and substitution square for arbitrary, possibly noninjective rho; preservation of separate occurrence positions under repeated names; specialization to the positive and negative substitutions in Proposition 4.2 with the stated endpoint types. |
| Appendix B | Explicitly typed path equalities for the first-injection triangle, five-arrow zero diagram and zero-law square, identified with the actual source operations. Reuse existing equations where they already prove these exact paths; duplicate proofs are unnecessary. |
| Appendix C | Selected side-rank positivity and total-rank correspondence; the actual (w gamma 3) recursive-cut strict inequalities r' < r; the (w disjunction 1) fresh right-principal rank 1 and unchanged-left-rank comparison, with explicit source/native adapters. Generic rank facts alone do not complete the concrete reduction correspondence. |

For Appendix A, cover empty profiles and blocks whenever the displayed maps
exist. Do not impose positivity, injectivity of label maps, distinct actual
variables, or nonempty occurrence sets for convenience. Give an explicit
translation between any zero-based Lean `Fin` coordinates and the manuscript's
one-based finite ordinals.

## Formalize the shorter proof as well as its conclusion

The old symmetric-fold proof remains valuable and must be preserved. Its
existence does not complete the new proof-correspondence obligation for v6 §5.
Introduce the actual maps, with j_A the first injection A → A ∨ top:

    q_A = [j_A ∘ π₁^(A,bot), ι₂^(A,top)]
        : (A ∧ bot) ∨ top → A ∨ top
    e_A = 1_A ∧ j_A
        : A ∧ A → A ∧ (A ∨ top).

Prove both are isomorphisms. The manuscript identifies them with published
isomorphisms first at a variable p, using occurrence graphs and, for e_p, a
possible product swap, then applies substitution. Formalize those identifications
with proved source inputs, or give direct inverse equations in the same source
quotient and record the correspondence. A bijective occurrence graph alone does
not imply invertibility under a merely faithful functor.

For a proof congruence satisfying every K_A, formalize this sequence:

1. Set E = A ∨ top, S = (A ∧ bot) ∨ top, and s = ι₂ : top → E.
   Prove the relevant zero arrow equals s ∘ ! in the original category.
2. Obtain q_A ≡ s ∘ !_S. Transport its original inverse equations through the
   congruence, deduce 1_E ≡ s ∘ !_E, and prove that E is terminal in the quotient.
3. Prove that r = π₁ : A ∧ E → A is invertible in that quotient and that
   r ∘ e_A = π₁ : A ∧ A → A.
4. Use the diagonal as the inverse of this projection to obtain π₁ ≡ π₂;
   use pairing to equate arbitrary parallel arrows.

Prove the required quotient preservation of products, coproducts, units and
inverse equations, or implement an equivalent proof directly modulo the
congruence. Use coherence only in the original category. Do not assume quotient
faithfulness, cancel j_A, or supply zero arrows for empty hom-sets. Connect this
proof to Proposition 4.2 and the actual-presentation main theorem, rather than
leaving it as a disconnected conditional demonstration.

## Model corollary

Define interpretations for the full source signature and prove the induced
functor out of the equation-generated quotient. Prove that agreement under
every interpretation forms a proof congruence closed under endosubstitution;
this requires composition of an interpretation with substitution to be another
interpretation. Do not assume that the kernel of one interpretation is
substitution closed.

Use nonempty P to choose p, interpret p as an arbitrary object X of the target
category, and transfer equality of the projections at p to the projections at
X. Pair arbitrary target arrows to conclude thinness. No surjectivity of an
interpretation on objects or arrows may be an added assumption. Keep the target
model universe general enough to express the printed corollary.

## Immediate continuation and dependency order

811eceeb and all successor reviews are incorporated. All cut elimination,
Positive/Reduced/Boolean coherence, intended occurrence interpretation, actual
quotient reduction/inclusion and recovery, derived negation/naturality, full
raw/quotient proof-congruence correspondence and actual maximality are proved.
The actual main theorem and its equality/total dichotomy now instantiate every
relative input. Reuse them. Continue the separate short q_A/e_A proof, remaining
negation/substitution compatibility and operation/coordinate laws, universal-
model corollary and all remaining v7 claims. The three milestones do not certify
the complete paper. Preserve the discharged recursion contract below.

At unchanged degree use the original inherited clean child and strict selected
rank; do not infer a bound after re-cleaning or head routing. Final cut-free
structural reconstruction may be atomized after recursion, as already proved.
For a subsequent blocked cut, prove the fresh native principal's one-sided
rank 1 and its clean status, with actual source/native adapters. At smaller
degree allow arbitrary returned ranks. Preserve both accepted principal cut
orders and the proved reflected-diagram interpretation.

The exact v7 Appendix C addition is complete. Its p.260 concrete source/rank
correspondence is proved by the left gammaDisj equation and both original-child
strict descents. Its p.262 actual sequential source/rank correspondence is proved
by BlockedDisjFirst.source_equation, fresh_clean_and_rank, fresh_principal_rank,
fresh_total_rank, fresh_total_rank_ge_two and blockedL_disjunctionFirst_rank_step. Preserve all older manuscript versions and
settled writing/correction requirements; no further manuscript defect was
established by this review.

Then prove restricted mix/positive/reduced/Boolean coherence, actual source
instances and substitution/congruence bridges, both maximality proofs, the model
corollary and every appendix claim under this unchanged contract. Historical
instructions and checkpoints do not reset scope or require another approval.

Keep the source G syntax/equations, rho and blocked/reducible predicates and
quantifiers unchanged. Record established corrections and verify their full
scope; never assume coherence, equality reflection or a supplied normalization
witness. Preserve the accepted source/native, singleton and empty-exchange
decisions, left-first composition, empty hom-sets and witnessed zeros.

## Completion and verification

Full-paper completion requires all of the following:

- Every confirmed correction affecting a claimed result or correspondence is
  implemented and verified before that claim is marked complete. The correction
  record identifies any unresolved issue; an unproved Lean obligation is not
  labelled a manuscript error without separate mathematical evidence.
- Every mathematical claim in the ledger has an exact checked counterpart or
  a proved derivation from named checked counterparts. Every conditional input
  needed by a final paper theorem has an actual source-presentation instance.
- Both the short §5 argument and the retained symmetric-fold route have their
  stated scope verified. The main theorem and model corollary have no open
  coherence or presentation premise. All three appendices are accounted for,
  including examples, uniqueness statements, coordinate correspondences and
  Appendix C's concrete corrected rank arguments.
- No custom mathematical axioms, proof holes, `native_decide`, conclusion-shaped
  assumptions, unwitnessed zeros, or circular uses of the coherence being proved
  occur in production proof dependencies. Apply the existing foundation-axiom
  policy and inspect the transitive dependency closure of the final endpoints.
- Run `bash scripts/verify.sh` and the applicable source-boundary checks and
  negative controls on the final immutable source, using the pinned toolchain.
  Use one heavy build or kernel replay at a time. Verification of unchanged
  source from an earlier commit is not verification of newly added endpoints.
- Apply the hostile and mathematical-writing reviews to the actual theorem
  statements, proof correspondence, claim ledger and final manuscript scope.
  Update `MANUSCRIPT_STATEMENTS.md`, `MANUSCRIPT_COVERAGE.md`, README and the
  continuation so they agree with what has been proved.
- Preserve the existing manuscript and previous proof routes. Any necessary
  manuscript correction must be explicit, with its source and PDF rebuilt and
  verified; do not delete a claim merely to declare formalization complete.
- Commit and push verified changes to main without force under the existing
  authorization, preserving intervening work. Retain reports and perform the
  required byte-verified Downloads delivery when that destination is available;
  report an inaccessible destination explicitly. Keep publication and Palomar
  submission separate from local formalization and verification.

If an obligation remains open, record its exact statement, current hypotheses,
obstruction and concrete next proof task. Do not report the entire paper as
formalized because a conditional theorem compiles, a local reduction family is
complete, or the main theorem alone has been proved.
