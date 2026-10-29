# Manuscript v7: statements and formal scope

## Current Positive, Reduced and Boolean coherence (29 October 2026)

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

The manuscript addition is complete. Appendix C p.260 has its actual source
equation and both strict original-child rank inequalities. Its p.262 concrete
sequential source/rank correspondence is proved by BlockedDisjFirst.source_equation,
fresh_clean_and_rank, the three fresh-principal/total-rank declarations and
blockedL_disjunctionFirst_rank_step. Both erratum rows are closed. Global cut elimination is now proved by the
current unrestricted interfaces; coherence and the other full-paper obligations
retain their separate statuses. The underlying v6 target is supplemented, not reduced.

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

The [reviewed successor instruction](CODEX_AFTER_5B8A199_BLOCKED_W.txt)
expands these remaining targets. Its source/evidence and writing reviews are
`reviews/GENTZEN_5B8A199_REVIEW.md` and `reviews/GENTZEN_5B8A199_WRITING.md`;
they add no checked Lean declaration or manuscript correction.

| Claim / source | Exact compiled declaration | Hypotheses / status |
| --- | --- | --- |
| §11.2 p.250 Reducibility and p.252 right analogue | `DosenPetric.Reduced.Gentzen.reducibility_left/right` in GentzenReducibility.lean | Arbitrary P and all contexts; exact ReducesL/R. Completed prerequisite to G2, not G2/cut elimination. |
| p.252 source one-premise W6 | `W6.TerminalOne.reducesFirst/Second` | Nonempty selection, arbitrary actual contexts and containing address; source macro ranks proved. |
| p.251 arbitrary cL/cR placement | `UnrestrictedExchange.left/right` | Actual arbitrary ContractionBlock with at least two selected copies, no outside-interval restriction. |
| Outside replacement | `ProofAddress.outside_of_incomparable`, `outside_cluster` | Paths mutually non-prefix; constructs actual surviving address internally. |

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

## Full-paper claim coverage

[The full-paper instructions](CODEX_FULL_MANUSCRIPT_FORMALIZATION.md) require
exact checked counterparts for the entire mathematical content of current v7,
including the short proof, model corollary, unnumbered assertions and all three
appendices. All v6 obligations remain, with Appendix C's additional correspondences.
Expand this map into a complete claim ledger as implementation proceeds, using
the contract's section-by-section inventory. Record hypotheses and actual
source-presentation instances; do not count a conditional or weaker theorem as
the printed claim. A scope clarification does not close an open proof obligation.

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

## Historical follow-up at 1e967bc (superseded above)

The [concrete W6 instruction](CODEX_W6_CONSTRUCTION.md) now specifies six
left/right selected-principal constructions, their rank targets and complete
addressed conclusions. This is a construction analysis for local Codex;
implementation and verification remain open. See its
[hostile audit](reviews/W6_CONSTRUCTION_HOSTILE.md) and
[writing review](reviews/W6_CONSTRUCTION_WRITING.md). No proof status below
is advanced by this instruction update.

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
The immediate proof task is [the supplied continuation](CODEX_AFTER_05C6BC8_REDUCIBILITY.txt),
with the unchanged full targets in CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt.
This is verified progress, not completion of that task. Final sources:
**249 Lean files / 8,919 audited declarations**. Earlier checkpoint
sections below retain their historical scope and are superseded where necessary.

Source: Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*,
v6, 25 October 2026, in `manuscript/`. The maximality theorem and model corollary are unchanged.
The contextual-collapse proof now uses two structural isomorphisms from
Došen–Petrić, §12.5, p.294; the proof of Lemma 7 in their 2012 isomorphism
paper supplies another source. Section 3 distinguishes the category from the
cartesian closed hypotheses of Joyal's theorem. Section 6 describes the
conditional Lean formalization, which retains the earlier symmetric-fold proof.
The new isomorphism-based proof has not been implemented in Lean. Appendices A
and B are unchanged. Review and verification records remain outside the paper.
Labels below refer to the manuscript rather than independently assigned numbering.

Let P be a nonempty set of variables. The target category B(P) is the free
zero-identity Boolean category of Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007 revision, §§14.2–14.3. A proof congruence is an equivalence on
each hom-set preserved by every specified arrow operation. A substitution
congruence additionally preserves every uniform formula substitution on arrow
terms and their endpoint types.

The target statement is: for every such congruence θ, if there exist objects
A,C and distinct f,g : A → C with f θ g, then for every X,Y and every
a,b : X → Y, a θ b. The existential pair and universal conclusion range over
the actual presentation. The final semantic corollary quantifies over every
interpretation of variables, not one fixed valuation.

`Category.comp f g` means first f, then g. Thus manuscript g ∘ f is
`Category.comp f g`, or `f ≫ g` after a Mathlib bridge.

| Manuscript definition or result | Formal counterpart | Exact scope or remaining input |
| --- | --- | --- |
| §2 category operations | `DosenPetric.Category`, `Presentation.Term`, `Equation`, `Derives`, `category` | The source quotient is built from the September 2007 primitive grammar and published equations; see `PRESENTATION_CORRESPONDENCE.md`. Composition and both tensors descend by generated congruence. |
| `eq:zero-identity` | `Presentation.zeroConstruction_structural`, `zeroConstruction_eq`, `zeroIdentity` | The source unit-isomorphism composite equals the manuscript pairing/copairing formula and primitive zero; the constructed zero satisfies the required law. |
| `eq:zero-law` | `DosenPetric.ZeroIdentity.law` | For all parallel f,g : A → B, `comp (zero A) f = comp g (zero B)`. |
| §2 zero arrow | `ZeroIdentity.zeroOf` | Requires f : Hom A B. No arrow is supplied to an empty hom-set. |
| §2 witness independence and absorption | `zeroOf_independent`, `commute`, `postcompose`, `precompose`, `zero_idempotent` | All categories with the explicit zero-identity law. `Presentation.zeroConstruction_eq` now proves that formula equals primitive zero in the source quotient; `Presentation.zeroIdentity` uses the construction. |
| §3 formulas and positions | `Formula`, `Formula.Occ`, `Formula.label`, `Formula.subst` | Arbitrary variable types; negation preserves positions; each connective uses Sum tags; constants have Empty positions. |
| `eq:occ-substitution` | `Formula.expand`, `contract`, `contract_expand`, `expand_contract` | For every substitution σ : P → Formula Q and formula A, mutually inverse maps between Occ(A[σ]) and Σ x : Occ(A), Occ(σ(label A x)). No nonemptiness assumption is needed. |
| §3 repeated variables | `Formula.repeated_positions_distinct` | The two positions in p ∧ p are distinct even though their labels coincide. |
| §3 relation operations | `Relations.comp`, `graph`, `sumMap`, `fstRel`, `sndRel`, `copair`, `reassoc` | Binary relations on types. These operations apply in particular to finite occurrence types. `Presentation.occurrenceMap` now descends from the source equation quotient and preserves identity, composition, and the specified operations; faithfulness remains open. |
| `eq:first-injection` | `Relations.first_injection`, `OccurrenceInterpretation.first_injection` | The relation equation is unconditional; its original-category counterpart is derived under the typed faithful-interpretation input. |
| §6 symmetric fold (v5 `lem:symmetric`) | `Relations.hRel_eq_fold`, `hRel_independent`, `hRel_swap`; `OccurrenceInterpretation.fold_independent`, `fold_swap` | The relation fold is calculated from operations; categorical independence and swap invariance follow by original-category faithfulness. The manuscript identifies this map as mix followed by the codiagonal. |
| §6 formal collapse argument (v5 `eq:second-block`) | `Relations.second_block`, `OccurrenceInterpretation.second_block` | The relation equation discards the first source block; the categorical equation follows by original-category faithfulness. This calculation belongs to the retained formal proof, not the replacement §5 proof. |
| `lem:structural-isos` | Not implemented as this lemma | The manuscript derives the specified q_A and e_A isomorphisms from the published structural isomorphisms using original-category coherence and uniform substitution. |
| §3 distinct projections | `Relations.projections_distinct`, `GeneratedModel.nonthin`, `Presentation.nonthin` | Every v5 §5 interface field is instantiated in a generated structural-fragment model, with distinct categorical projections and `GeneratedModel.empty_hom`. This does not identify the fragment model with B(P). Separately, `Presentation.nonthin p` proves distinct projections in the equation-generated source quotient; `Presentation.empty_hom` proves its Hom(top,bot) empty. |
| `thm:coherence` | Presentation.coherence; Reduced.faithful/boolean_coherence; Presentation.interpretation | Boolean coherence is proved for the actual equation-generated presentation through actual PositiveCoherence, common atomic factorization and existing normalization transfers. Full intended faithful interface and signed-label invariant are instantiated. |
| §14.2 source signed-literal reduction used toward §3 coherence | `Reduced.Term/Equation/Derives/Hom/category`, `inclusion`, `red_sound`, `representation` | Genuine restricted syntactic quotient on NormalForm P; 21 term/61 inherited equation schemas, atomic eta/epsilon only. Every full raw term has a reduced representative equal after inclusion to normalization transport; every full normal-form arrow is in the inclusion image. Equality reflection and quotient descent of red are not proved. |
| §14.2 contextual factorizations toward §3 coherence | `Reduced.Context`, `gConj/gDisj`, `gEta/gEpsilon`, `gEta_comp/gEpsilon_comp`; tagged context and composed occurrence laws | Unconditional equalities in Reduced.Hom for arbitrary P, all one-hole contexts and existing top-domain/bottom-codomain arrows (atomic η/ε specializations give (gη)/(gε)/(gηf)/(gεf)). Needed positive identities are directly derived from the unchanged equations. Common atomic factorization is now proved; §12.5 positive-fragment coherence remains open. |
| §14.2 common atomic factorization toward §3 coherence | commonAtomicFactor; faithful_of_positive_coherence; Reduced.faithful | Complete shared supported factorization is instantiated with Gentzen.positive_coherence, giving full Reduced faithfulness without additional mathematical inputs. |
| §12.5 algebra toward positive coherence | `Reduced.tensor_zero/tensor_zeroOf`, derived `Term.union/Derives.union/union`, union algebra and occurrence formulas | Unconditional for arbitrary P and existing reduced arrows; positive raw closure is explicit. Union-unit follows the direct p.291 structural proof. No new equation, empty-hom-set zero, coherence or fullness is assumed. Positive Gentzenization, unrestricted cut elimination and actual restricted/unrestricted positive coherence are now proved; see the current table. |
| Positive Gentzenization toward §12.5 coherence | `Reduced.Gentzen.G/denote/denote_positive`, `gentzenization`, `gentzenization_decode`, `gentzenization_occurrences` | G0/G1 compile for arbitrary P and every positive raw term, with atomic/constant leaves only, visible contextual cuts, actual singleton units and tagged occurrence coordinates. All 19 Positive schemas are covered. positive_cutFree_represented now strengthens this to actual cut-free atomized witnesses, used in the completed coherence argument. |
| Atomic-k toward G2 cut elimination | `Reduced.Gentzen.G.atomization`, `atomization_cutFree`, `atomization_occurrences`; positional `atomThinL/R` and actual mixed-map consequences | Unconditional for arbitrary P and every G proof at unchanged contexts: atomized representative, equal Reduced denotation, preservation of existing CutFree and complete tagged relation equality. All sixteen schemas and four compound-thinning cases compile. The cluster/rank prerequisite is now proved below; blocked-contraction transformations and the rest of G2 remain open. |
| Gentzen clusters/rank prerequisite within G2 | `G.predecessors_correct/sourceArity_correct/position_classification`, `cluster_correct/cluster_address`, `rho_node_list/rho_child_lt`, `contractionRankL_eq/R_eq`, `cutRank_two_iff_leaves` | Unconditional typed finite tracing/rank for arbitrary P and every G proof, including cuts; all sixteen rules, full separated contraction copies and source leaves covered. Reindex and topmost/cut-free specializations compile. Tied sites are characterized; blocked transformations, Reducibility and cut elimination remain open. |
| Two opposite-side W1 thinning instances | `W1.denoteL/R`, `contraction_lossL/R`, `endpoint_rankL/R`, `endpoint_lossL/R`, both strict decreases; CutFree/Atomized equivalences, exact cutCount and relation equality | Unconditional for arbitrary P,C,D and premise f with hn ≥ 2. Contraction rank loses n = gs.length; whole selected endpoint loses n−1. The dual is separately checked. Other W1 cases, all-site rank control, Reducibility and cut elimination remain open. |
| Two opposite-side W1 exchange instances | `W1.Exchange.denoteL/R`, singleton predecessors and rho equations, complete contraction sums and both exact rank losses; CutFree/Atomized/count/relation preservation | For arbitrary P and premises, including cuts, n=gs.length ≥ 2 gives contraction loss n and whole selected-endpoint loss n−1, including empty blocks. No new atomicity condition or coherence premise. General W1, arbitrary-context rank control and Reducibility remain open. |
| Opposite-side W1 contraction commutation | `W1.Contraction.denote/reverse`, opposite-side singleton predecessor/rho laws, four endpoint equations, directed balances/decreases/increases, endpointSum balance, predicate/count/relation preservation | One pair at arbitrary independent n,m≥2: outerL has ranks L+n,R+1; outerR has L+1,R+m. Each directed move lowers its targeted side and raises the other. Sum preserved for n=m; no general decreasing measure, arbitrary-context result or full Reducibility. |
| Opposite-side W1 unary logical commutations | `W1.Logical.denoteL/R`, exact opposite-side predecessors/rho and full selected-copy sums; principal Leaf/empty predecessors, old/new ranks 2/1; predicate/count/relation preservation | Arbitrary P,A,B,C and premises, including cuts: contraction loses n, whole selected endpoint n−1 for n≥2. Compound principal formulas are allowed in Atomized. Opposite-side unary W1 families complete at their local scopes; other same-side exchange/contraction/logical and binary cases, all-site decrease and broader Reducibility remain open. |
| Fixed-position same-side W1 thinning (four cases) | `W1.SameSideThinning.interior_left/right`, `terminal_left/right`; proved copies/thinning square, ordered selected transport, retained/inserted coordinates, exact rank and preservation laws | Arbitrary P,C,E, lists and cut-containing premises with n≥2. Exact Reduced equality uses universal component extensionality, not faithfulness. Every selected copy stays parametric even E=C. Contraction loss n, whole selected endpoint loss n−1, inserted fixed rank 2→1; both Atomized predicates equal AtomicFormula E ∧ f.Atomized. Other W1/W2, all-site decrease and Reducibility remain open. |
| Four fixed-parametric same-side W1 exchange commutations | `W1.SameSideExchange.interior_left/right`, `terminal_left/right`; all-position copies/exchange square, complete ordered selected transport, retained/fixed fibers, exact ranks and preservation | Arbitrary P, formulas/lists/premise, n≥2; exchange entirely inside one fixed gap or terminal tail. Contraction loss n, retained endpoint loss n−1; other same-side fixed positions have unchanged 2+rho ranks. Both Atomized predicates equal f.Atomized. Crossing selected positions, multi-gap and absorption configurations remain open, as do general W1 and Reducibility. |
| Four fixed-parametric same-side W1 unary logical cases | `W1.SameSideLogical.interior_left/right`, `terminal_left/right`; partial ancestry with both consumed slots none, complete selected transport/survival, separate component equations, Reduced squares/equality and exact ranks | Arbitrary P,A,B,C, lists/premise, n≥2; logical rule wholly inside one fixed gap or terminal tail. Retained n/n−1 losses, principal 2→1, all other final fixed ranks unchanged 2+rho. Both Atomized predicates equal f.Atomized. No coherence premise, label disequality or total A/B→D whole-formula map. Other W1/W2–W6 and general Reducibility remain open. |
| Fixed-gap disjoint same-side W1 contractions | `W1.DisjointContraction.fixedGap_left/right`, all eight context equalities, copies/copies squares, both complete ordered selected transports, retained/fixed fibers, four-rank tables and preservation | Arbitrary P,C,E, lists and existing premises; independent n,m≥2, including C=E and cuts. Exact final context K=(gaps pre++U)++gaps es++E::(V++(gaps post++C::Θ)). Old=(LC+n,LE+1), new=(LC+1,LE+m); S(old)+m=S(new)+n. Other fixed ranks unchanged; no global measure or W3/coherence claim. |
| Terminal-tail disjoint same-side W1 contractions | `W1.DisjointContraction.terminalTail_left/right`, concrete eight context identities, copies/copies square, ordered selected transports and complete fixed fibers; both exact rank tables and preservation | Arbitrary P,C,E,gs,hs,H,U,V and existing premises; independent n,m≥2, including C=E and cuts. Final K=(gaps gs++C::U)++gaps es++E::V. Retained xC<xE; old=(LC+n,LE+1), new=(LC+1,LE+m), S(old)+m=S(new)+n. Disjoint interleaving, all-site rank control and general Reducibility remain open; W3 is supplied below. |
| W3 shared-selected contraction fusion | `W3.SharedContraction.fusion_left/right`; computed flat gaps/tail, complete ordered selected originals/fibers, structural squares and exact rank laws | Arbitrary P,C,gs/hs,Θ/Λ with typed hI and genuine shared-position membership, independent n,m≥2 and existing cut-containing premises. Actual single contraction of arity n+m−1 at G P K Δ or G P Γ K; old retained/outer rank = flat rank+m, other final same-side ranks 2+rho versus 1+rho. No coherence or all-site Reducibility conclusion. |
| Terminal selected-thinning W2 | `W2.SelectedThinning.terminal_left/right`; actual thinning/outer contraction versus direct contraction/exchange, complete ordered selected transport/fibers, structural squares and exact ranks | Arbitrary P,C,gs,Θ, n≥2 and existing cut-containing premises at exact G P K Δ / G P Γ K. Full outer selection has n+1 positions; composite fibers from F have n. Contraction/endpoint losses n+1/n; other fixed ranks unchanged. Counts/CutFree/tagged relations preserved. Old Atomized iff AtomicFormula C and f.Atomized; new iff f.Atomized. Atomicity is not required for equality/ranks. No all-site Reducibility/coherence conclusion. |
| Terminal selected-logical W4 | `W4.SelectedLogical.terminal_left/right`; actual logical introduction/outer contraction versus inner contraction/introduction/two-copy contraction; complete partial ancestry/fibers and component equalities | Arbitrary P,A,B,gs,Θ, n≥2 and existing cut-containing f, C=conj A B / disj A B. Exact G P K Δ / G P Γ K outputs. Both A/B slots consumed, selected n/n+1/two-copy families and all fixed originals/fibers constructed. Old outer rank LC+n+1 versus inner LC; new endpoint LC+3. Final n=2 tie, n≥3 strict decrease, other fixed rank increase one. Counts/CutFree/Atomized/full tagged relations preserved, no atomicity/coherence input. General Reducibility/Blocked-w/coherence open. |
| W5 single-premise mix, selected g in G.mix f g | `W5.SinglePremiseMix.single_premise_left/right`; actual contraction/mix constructors, component extension/naturality, complete branch fibers and exact ranks | Arbitrary P,C,gs,Θ,n≥2 and existing f/g, including cuts. Exact outputs G P (K++Φ) (Δ++Ψ) / G P (Δ++Φ) (K++Ψ). Complete ordered selection from g, same-label f exclusion, retained/fixed/suffix fibers and unique originals. Old outer LC+n, new retained LC+1; exact n/n−1 losses. Fixed/opposite g ranks both 2+rho; f old 2+rho/new 1+rho on both sides, correcting the historical missing-node target. Counts/CutFree/Atomized/full relations preserved. The other placement is now proved below; mixed-premise W5 and general Reducibility/coherence open. |
| W5 other single-premise mix, selected g in G.mix g f | `W5.OtherPremiseMix.other_premise_left/right`; derived prefix data/components, complete branch fibers and ranks | Arbitrary original P,C,gs,Θ,n≥2 and existing f/g including cuts. Exact outputs G P (Φ++K) (Ψ++Δ) / G P (Φ++Δ) (Ψ++K); raw gaps (Ξ++H)::hs derived from gs=H::hs. Complete shifted g selection; equal-label f exclusion, retained/fixed/prefix fibers and unique originals. Old outer LC+n, new retained LC+1; n/n−1 losses. Fixed/opposite g both 2+rho; f old 2+rho/new 1+rho on both sides. Counts/predicates/full relations preserved. Proof-occurrence replacement is now proved below; mixed-premise/binary W5–W6 and global elimination/coherence remain open. |
| Proof-occurrence replacement and W5 integration toward G2 | `Premise.rebuild/inserted`, `ProofAddress.replace/inserted/append`, recovery/composition/congruence/preservation; `OtherPremiseMix.replace_denote/count/cutFree/atomizedL/R` | Arbitrary existing root, proof occurrence/address and replacement at the exact same sequent. Outer endpoints/siblings preserved; inserted address keeps its path; complete Reduced congruence and tagged relation consequence. Exact additive cutCount/proofSize balances; root/replacement CutFree or Atomized imply rebuilt predicate. Existing W5 duals lift at any address, with nested signed-cut/Empty examples. Blocked/Reducible encodings and finite profiles are now proved below; certified rewrite dispatch, tied-site ranks and global G2/G3 remain open. |
| Blocked/reducible occurrences and finite selection classification | `BlockedL/R`, `ReducibleL/R`, `ProofAddress.ProperContains`, `PortOrigin`, `ContractionBlock.classificationL/R` and source-order macros | Seven actual source left patterns and separately typed canonical right encodings with explicit first-retention comparisons. Reducibility retains topmost-cut, cluster/address/position, unblocked and proper blocked-ancestor conditions. Every arity≥2 cut-free input has a unique seven-regime selected profile with complete per-position origin evidence; basis/cut excluded by proof. This is classification, not a reducer. Constructed mixed-premise mix W5 now has both addressed descendant theorems. Full profile dispatch, logical W5/W6, remaining local cases, outside-site ranks and global G2 remain open; see the follow-up report. |
| Normalization, §3 | `Presentation.normalization`; `NegationNormalization.forward_backward/backward_forward`, `forward_graph/backward_graph`, `transport_apply` | Actual source-quotient instance for every P, with signed-leaf normal forms, both inverse arrows, inverse tagged coordinates, literal/label/polarity correspondence, Empty cases, and relation transport. Recovery/injectivity reuse the existing theorems. No coherence or naturality premise. |
| Global signed-label preservation, §3 | Presentation.occurrence_literal; interpretation_signedLabel | The direct signed-label theorem now instantiates the invariant of the actual Presentation.interpretation P, for arbitrary P and every source arrow. |
| `lem:isolation` | `Isolation.selector_edge`, `coselector_edge`, `isolate_edge`, `normalized_literal_context` | Normal-form witness equations and the normalized contextual consequence under faithful interpretation, normalization, and signed-label inputs. The full original-category witness formulation is not a separate declaration; no actual presentation is inferred. |
| `prop:all-contexts` | `ContextualCollapse.context_retract`, `all_contexts` | Typed substitution on arrows and endpoints, separate congruence closure, positive substitution, and negative substitution followed by double-negation transport. |
| `lem:collapse` | `ContextualCollapse.total` | Same conclusion by different proofs: v6 §5 uses q_A and e_A; Lean retains the symmetric-fold argument described in §6. Both concern existing arrows and use no quotient faithfulness or cancellation of j_A. |
| `thm:main` | `relative_maximality` is the conditional counterpart | The actual-presentation theorem remains open. The conditional theorem quantifies over every compatible congruence with explicit substitution closure. |
| `cor:models` | Not implemented | All interpretations; use nonempty P to choose a variable and interpret it as an arbitrary object. |
| Appendix A | Partial; full coverage required | Tagged block bijection is implemented. Complete profiles, gamma/chi maps and all squares, ordinal bijections and block locator, delta and the book-operation bridge, skeleton/profile reconstruction, the worked example, and renaming with shared variables; connect the specializations to Proposition 4.2. |
| Appendix B | Exact diagram correspondence required | Reuse the proved first-injection, constructed-zero and zero-law equations to certify the three displayed typed path equalities in the actual presentation. Record exact declaration links; the existence of the diagrams alone is not a Lean proof. |

The structural record fields are hypotheses of the conditional theorems.
They are not substitute definitions of the free Boolean category. Adding fields
such as “every contextual equation implies thinness” would assume the central
obligation rather than formalize its proof.

`Structure` gives the bicartesian universal equations, truth-constant arrows,
and distributor with all endpoints. `OccurrenceInterpretation` gives the
operation-level relation laws. `fold_independent`, `fold_swap`,
`first_injection`, and `second_block` derive the corresponding categorical
equations by faithfulness in the original category. The `GeneratedModel`
checks the entire v5 §5 interface, but includes no full Boolean presentation.
`Congruence` records the compatibility needed by this argument; a bridge must
restrict each actual proof congruence to it.

`Substitution.map σ f` has type `Hom (A.subst σ) (B.subst σ)` for
`f : Hom A B`. Its per-substitution functor/operation laws are inputs;
composition and identity laws for substitution schemas themselves have not
been formalized. No closure under substitution is inferred from one
interpretation kernel. The model corollary still requires every interpretation.

## Source-presentation instances

The [source correspondence](PRESENTATION_CORRESPONDENCE.md) gives printed pages,
equation labels, constructors, and derived arrows for the exact September 2007
revision. `Presentation.operations` constructs `Structure` for the syntactic
quotient. `Presentation.zeroIdentity` uses the displayed `(0ηε)` composite;
`zeroConstruction_eq` proves equality with primitive zero. Empty hom-sets are
preserved, with `Presentation.empty_hom` for every variable type P.

`Term.subst`, `Equation.subst`, and `Derives.subst` establish whole-arrow and
endpoint substitution and its preservation of the source-generated equality.
`Presentation.substitution` instantiates the existing per-substitution
`Substitution` interface, including the constructed zero.
`Presentation.doubleNegation` instantiates `DoubleNegation` from the two n-arrows
and their inverse equations. These instances use no coherence hypothesis.
Schema identity/composition with endpoint identifications and occurrence-block
transport remain separate obligations. No arbitrary extra congruence is thereby
proved substitution closed.

`Presentation.Equation.relation`, `Derives.relation`, and `occurrenceMap` prove
well-definedness of the occurrence interpretation and the operation images.
Presentation.coherence now proves faithfulness, and Presentation.interpretation
instantiates the complete intended OccurrenceInterpretation. The final full-source
congruence bridge and actual relative_maximality instantiation remain continuing duties. `Presentation.normalization`
now constructs the existing normalization record with occurrence graphs and
signed coordinate correspondence. `Presentation.occurrence_signedLabel` now
proves global signed-label preservation directly, with normal-form literal
and transport consequences. Derived contravariant arrow negation/naturality,
congruence restriction, and the remaining Appendix A/model correspondences are
still open. The reduced signed-literal syntax and existential representation
bridge and actual Reduced.faithful are now constructed, with occurrence
compatibility and the instantiated original-category coherence transfer. See the
[reduction report](SIGNED_LITERAL_REDUCTION_REPORT.md),
[signed-label report](SIGNED_LABEL_REPORT.md),
[normalization report](NORMALIZATION_REPORT.md), and the historical
[presentation report](PRESENTATION_BRIDGE_REPORT.md) for exact hypotheses,
source references, commands, evidence, and review boundaries.

The [contextual factorization report](CONTEXTUAL_FACTORIZATION_REPORT.md) records
the next completed source step. The context functor descends through Derives;
its occurrence action fixes surrounding tags and acts on the distinguished hole.
The two “same pairs” comparisons use explicit Sum.inl endpoint embeddings.
Neither these identities nor the earlier representation theorem proves reduced
faithfulness. The source's common atomic factorization and complete support are now proved.
The §12.5 positive-fragment coherence input remains an obligation.

The [common atomic report](COMMON_ATOMIC_FACTORIZATION_REPORT.md) records the
shared factorization and full auxiliary-edge exclusion. Positive describes the
arrow grammar, including zero, rather than literal polarity. Its precise
PositiveCoherence premise is not an axiom or supplied instance. Neither the
factorization nor relation support alone is Boolean Coherence.

The [positive zero/union report](POSITIVE_ZERO_UNION_REPORT.md) records the proved
algebra and separate interpretation formulas. Its dependency table specifies the
then-pending Gentzenization theorem and later coherence inputs; the current G0/G1 status is recorded below.

The [Gentzenization report](POSITIVE_GENTZENIZATION_REPORT.md) records completed
G0/G1 and its historical Atomic-k continuation target. The
[Atomic-k report](POSITIVE_THINNING_ATOMIZATION_REPORT.md) now proves that exact
target, with CutFree preservation and tagged occurrence equality. The
cluster/rank prerequisite is now proved below; the remaining G2 transformations
come next.
The representation is existential and supplies no quotient translation.

The [cluster/rank report](GENTZEN_CLUSTER_RANK_REPORT.md) records the completed
prerequisite. The [W1 thinning report](GENTZEN_W1_THINNING_REPORT.md) now
proves the two opposite-side thinning instances, with distinct contraction
and endpoint rank losses. Other W1 cases and all-site reducibility remain open.
No rank invariance under equal denotations or quotient descent is asserted.

The [W1 exchange report](GENTZEN_W1_EXCHANGE_REPORT.md) proves the two
opposite-side exchange instances after thinning. The contraction pair is now proved in
[the contraction report](GENTZEN_W1_CONTRACTION_REPORT.md), with its two
directed rank comparisons. The [logical report](GENTZEN_W1_LOGICAL_REPORT.md) now proves the two unary
logical instances and principal 2→1 ranks. The [same-side thinning report](GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md)
now proves interior-gap and terminal-tail insertion and both duals, with every
selected copy parametric even E=C. The [same-side exchange report](GENTZEN_W1_SAME_SIDE_EXCHANGE_REPORT.md)
now proves four fixed-gap/tail exchange cases. The [same-side logical report](GENTZEN_W1_SAME_SIDE_LOGICAL_REPORT.md) now
proves all four fixed-gap/tail unary logical cases. The [disjoint-contraction report](GENTZEN_W1_DISJOINT_CONTRACTION_REPORT.md) proves both fixed-gap same-side cases. The [terminal-tail report](GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_REPORT.md) now proves both terminal-tail cases with explicit xC<xE ordering and the independently directed rank table. The [W3 report](GENTZEN_W3_SHARED_SELECTED_CONTRACTION_REPORT.md) now proves shared-selected fusion and its right dual, including exact retained rank drop m. The [W2 report](GENTZEN_W2_SELECTED_THINNING_REPORT.md) now proves terminal selected thinning and its right dual, including distinct n+1/n losses and the asymmetric Atomized boundary. The [W4 report](GENTZEN_W4_SELECTED_LOGICAL_REPORT.md) now proves terminal selected logical introduction and its right dual, with n+1 source contraction loss, n=2 endpoint tie and other fixed-rank increases. The [single-premise W5 report](GENTZEN_W5_SINGLE_PREMISE_MIX_REPORT.md) now proves the G.mix f g placement and right dual, including n/n−1 losses and corrected opposite-side ranks. The [other-placement W5 report](GENTZEN_W5_OTHER_PREMISE_MIX_REPORT.md)
proves G.mix g f and its right dual with actual prefixed gaps and the same
complete rank table. The [proof-replacement report](GENTZEN_PROOF_REPLACEMENT_REPORT.md) now
constructs typed replacement and integrates both W5 duals at arbitrary addresses,
with exact count/predicate laws and actual nested examples. The [classification report](GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md) now
encodes those patterns and proves finite selected-ancestry coverage. Its ledger
identifies mixed-premise W5 as the next unproved regime.
Disjoint interleaving, mixed-premise/binary W5–W6, remaining exchange/W1/W2,
complete rewrite dispatch, macro/tied-site ranks and broader elimination/coherence stay open.

## Appendix C correspondence ledger (v7 addition)

| Claim anchor | Exact mathematical statement | Lean correspondence | Status |
| --- | --- | --- | --- |
| app:cut-errata, opening | Both one-sided ranks are positive; total rank is their sum. | G.rho_pos, PositionalCut.rank, rank_ge_two and rank_head; native G.cutRank retained. | Compiled for all exact selected positions, including heads. |
| Appendix C, p.260 paragraph | The two recursive subcuts in source (w gamma 3) have unchanged formula degree and rank r' < r. | BlockedLeftDisj.gammaParent_source, gamma_equation, gamma_first_descent, gamma_second_descent and CutCommutation.blockedL_gammaDisj_rank_step. | Compiled actual source reduction, full inherited Clean and both strict original-rank inequalities; C and its degree are unchanged. |
| Appendix C, p.262 paragraph | The native disjL right cut premise has rho.left=1 at its selected antecedent; total rank is unchanged opposite h.rho.right+1≥2. | BlockedDisjFirst.fresh_principal_rank, fresh_total_rank, fresh_total_rank_ge_two; source_equation, original_descent, fresh_clean_and_rank; CutCommutation.blockedL_disjunctionFirst_rank_step. | Actual sequential source/native correspondence, full Clean and both strict original-rank calls proved. disjLLast wrapper exchanges are explicit and not assigned native rank one. |

## Native principal conjunction correspondence

| Source / target | Exact checked declaration | Scope |
| --- | --- | --- |
| §11.2 p.254 principal conjunction degree step | PrincipalConjunction.rule_equation and selected_equation | Actual Reduced equality for the same principal cut; native A-then-B reduction is an alternative to the displayed B-then-A source order. No global elimination is inferred. |
| Component recursive calls | selectedReduction_count, selectedReduction_atomized, component_degrees | Two component cuts, same atomization condition and both smaller degrees; their actual elimination awaits the discharged global induction. |
| Internal logical principal routing | LogicalHeadRouting.square, G.conjL_toHead, G.disjR_toHead | Both consumed tags and all fixed tags, including empty contexts and repeated labels; no false exchange-wrapper rank. |

## Principal disjunction and exhaustive rank-two degree correspondence

| Source / target | Exact checked declaration | Scope |
| --- | --- | --- |
| §11.2 pp.254–255, disjunction principal case by analogy | PrincipalDisjunction.rule_equation, selected_equation | Actual native B-then-A reduction at every selected gap and original output. No assumed quotient duality or unwritten source display. |
| Both strictly smaller-degree principal branches | PrincipalConjunction.degree_step, PrincipalDisjunction.degree_step | Actual cut-free atomized witnesses under DegreeBelow; inner witness replaced before outer call, arbitrary returned ranks. |
| Exhaustive selected rank-two degree step | PositionalCut.rank_two_degree_step | Atomic cases and both principal cases, under the explicit strict outer degree hypothesis. Global discharge remains open. |
| Exact selected exchange and reverse context association | HeadRouting.front_arrow/front_split/front_singleton, split_assoc_inverse | All fixed/selected tags, actual units and both context sides. |

## Selected structural cut correspondence

| Source / target | Exact checked declaration | Scope |
| --- | --- | --- |
| §11.2 pp.255 onward, same-side parametric structural cases | CutCommutation.same_right/same_left; exchange_singleFiber/thin_singleFiber/contract_singleFiber | Actual Reduced equations at original selected sequents; every exchange/old thinning/unselected contraction position. The selected lower contraction remains in the blocked families. |
| Actual strict recursive subcut | clean_same_right/left, rank_same_right/left, same_right_rank_step/same_left_rank_step | Actual inherited original clean child and strictly smaller selected rank, before residual reconstruction and final atomization. |
| Opposite structural programs at arbitrary gaps | selected_opposite_left/right and selected_opposite_left/right_descent | Exact Reduced equations, addressed cleanliness and strict rank for every nonempty program. |
| Typed deletion and complete residual correspondence | At.remove/retain_remove/remove_retain/formula_eq, Route.residual_get/residual_square | Every surviving tag, including equal formula labels and empty lists. |

## Opposite logical selected-cut correspondence

| Source / target | Exact checked declaration | Scope |
| --- | --- | --- |
| §11.2 p.255 onward, opposite unary logical parametric cases | CutCommutation.opposite_conjL/opposite_disjR | Actual Reduced commuting equations for native G rules at every selected gap and original sequent. |
| Cut-free logical reconstruction | opposite_conjL_eliminated/opposite_disjR_eliminated | Actual cut-free atomized witnesses with exact equality from the child witness. |
| Same-degree recursive call | opposite_conjL_descent/opposite_disjR_descent and both rank_step lemmas | Complete inherited original-child cleanliness and strict selected-rank descent, before rebuilding. |
| Prefix/suffix logical comparison | prefixSide_logical, prefixSide_join/split, suffixLogicalSide_join/split | Actual association and unit comparisons; product-coordinate pentagon is proved and instantiated. |
