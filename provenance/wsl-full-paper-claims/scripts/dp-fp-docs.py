for src,dst in [('report','FULL_PAPER_CORRESPONDENCES_REPORT.md'),('hostile','reviews/FULL_PAPER_CORRESPONDENCES_HOSTILE.md'),('writing','reviews/FULL_PAPER_CORRESPONDENCES_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-fp-'+src+'.md').read_bytes())
active='''## Current original isolation and complete substitution square (29 October 2026)

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

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md','docs/PRESENTATION_CORRESPONDENCE.md']:
 p=root/rel;s=p.read_text();a=s.index('\n')+1
 block=active if rel!='README.md' else active.replace('](FULL_','](docs/FULL_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+'\n'+block+s[a:];s=s.replace('## Current short q_A/e_A proof','## Retained short q_A/e_A proof checkpoint');p.write_text(s)
p=root/'docs/MANUSCRIPT_STATEMENTS.md';s=p.read_text();lines=s.splitlines()
for i,t in enumerate(lines):
 if t.startswith('| `lem:isolation` |'):lines[i]='| `lem:isolation` | Isolation.original_witnesses; Presentation.occurrence_isolation, OriginalIsolation.lean | Complete exact original-endpoint statement for arbitrary P : Type u, distinct existing f/g, signed literal, actual i/r, both equalities and permitted interchange. All source normalization/faithfulness/labels instantiated. |'
 if t.startswith('| Appendix B |'):lines[i]='| Appendix B | ManuscriptDiagrams.first_triangle/zero_diagram/zero_primitive/zero_square, ManuscriptStructuralDiagrams.lean | Complete exact source paths: typed triangle; five named arrows and their zero identity; arbitrary parallel f/g square. Uses existing source equations, no duplicated proof assumptions. |'
 if t.startswith('| §6 symmetric fold (v5 `lem:symmetric`) |'):lines[i]='| §6 symmetric fold (v5 `lem:symmetric`) | Presentation.fold_source_mix/fold_manuscript, mix_parameter_independent/fold_parameter_independent/fold_symmetric, PresentationSymmetricFold.lean | Exact categorical identification with displayed mix followed by copair(id,id), parameter independence and pair-of-projections symmetry in the original source. Existing relation and generic interface equations preserved. |'
 if t.startswith('| `eq:occ-substitution` |'):lines[i]='| `eq:occ-substitution` | Formula.expand/contract and inverse laws; contract_label/expand_label; Term.substitution_coordinates and occurrence_substitute_coordinates/expanded | Actual tagged block bijection, label square and complete raw/quotient whole-arrow block square are proved for arbitrary substitutions and both variable universes. Appendix A profiles/ordinals/book correspondence remain separate. |'
 if t.startswith('| Appendix A |'):lines[i]='| Appendix A | Actual block bijection, label and whole-arrow squares complete; profiles/ordinals remain open | Formula.expand/contract, contract_label/expand_label and all source substitution squares are instantiated. Complete profiles, gamma/chi and all their squares, ordinal bijections/locator, delta/book bridge, skeleton/profile reconstruction, worked example and noninjective renaming/specializations. |'
p.write_text('\n'.join(lines)+'\n')
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text();a=s.index('811eceeb and all successor reviews',s.index('## Immediate continuation'));b=s.index('At unchanged degree',a)
s=s[:a]+'''811eceeb and all successor reviews are incorporated. All cut elimination,
coherence, actual source interfaces, full congruence/closure bridges, both
maximality routes, exact original isolation, cartesian-closure obstruction,
Appendix B and the displayed symmetric-fold correspondence are proved.
The complete 31-constructor/quotient occurrence-block substitution square,
actual label square and derived-negation/whole-arrow-substitution compatibility
are also proved, with full operation and witnessed-zero laws. Preserve them.
Continue full-source model interpretations, composition with substitution and
the universal-agreement congruence/model corollary; remaining arrow-action
composition and all Appendix A profile/ordinal/renaming/example constructions.
The dated §6 development-status paragraph requires a coordinated final scope
refresh before full-paper certification; preserve all versions and diagrams.
The endpoint and discharged recursion contract below remain unchanged.

'''+s[b:];p.write_text(s)
p=root/'AGENTS.md';s=p.read_text();a=s.index('Actual full proof-congruence correspondence');b=s.index(' Reuse all completed binary',a)
s=s[:a]+'''Actual full proof-congruence correspondence, substitution closure, both actual
maximality routes, original isolation, complete whole-arrow block/label squares,
negation/substitution compatibility, Appendix B, categorical consequences and
exact symmetric-fold correspondence are now proved. Continue full-source model
interpretations and the model corollary, remaining substitution-action and
Appendix A profile/ordinal/renaming/example claims, and final manuscript scope
refresh. Preserve both proof routes and every completed result.'''+s[b:];p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Further exact correspondences and retained scope update (29 October 2026)

Original isolation, source nonzero identities/global points, the cartesian-
closure obstruction, Appendix B paths, the exact fold/mix identity and complete
raw/quotient substitution block square are now proved. Derived negation commutes
with whole-arrow substitution. All affected active maps and continuation are
reconciled. An early proof attempt incorrectly used a reverse-arrow helper across
product/coproduct endpoints; Lean rejected it. All affected cases now use typed
occurrence functions and the actual two endpoint label maps. Parallel usages
were checked, and the complete 31-constructor theorem compiles. This was an
implementation typing correction, not a manuscript mathematical defect.

Pending scope refresh FP-SCOPE-20261029: v7 §6, the paragraph beginning “For the
equation-generated”, states faithfulness remains unproved and the full source
inputs are not instantiated. This dated development-status paragraph is now
historical after the completed source proofs. It requires one coordinated final
scope update across manuscript and linked records before full-paper certification;
that prose repair is not reported as completed. Preserve prior versions and all
ten diagrams, rebuild/inspect any changed TeX, and record exact source/PDF hashes.
No false mathematical theorem was established. Current nine manuscript blobs,
accepted corrections, all completed proofs and the original stash remain intact.
'''+s[a:];p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();s+='''
## Further full-paper correspondences (29 October 2026)

The source original-isolation witnesses, non-cartesian-closure consequence,
Appendix B and exact fold/mix correspondence are now proved. All 31 source
constructors have actual whole-arrow substitution block squares and negation
commutes with substitution. See FULL_PAPER_CORRESPONDENCES_REPORT.md. Constructor/
cut/rank/coherence results and both actual main routes remain preserved. Model,
remaining Appendix A/action laws and the final scope refresh continue.
''';p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_D8DC710.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER BOTH MAXIMALITY ROUTES: MODEL AND REMAINING PAPER CLAIMS','CONTINUE V7 AFTER COMPLETE BLOCK SQUARE: MODEL AND APPENDIX A')
s=s.replace('Read SHORT_QE_REPORT.md', 'Read FULL_PAPER_CORRESPONDENCES_REPORT.md and its hostile/writing reviews, reusing\nSHORT_QE_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_D68DA50.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_D8DC710.txt, archived verbatim.\nThe D68DA50 continuation remains preserved.')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Further full-paper claims are now proved: Presentation.occurrence_isolation
has actual original-endpoint witnesses, both equations and the permitted swap.
top_hom_subsingleton, literal_identity_ne_zero and no_projection_exponential/
not_cartesian_closed close the stated global-point/nonzero/closure consequences.
Appendix B's three exact typed source paths and the displayed fold/mix/copair
identification, parameter independence and symmetry are proved.

Term.substitution_coordinates exhausts all 31 primitive constructors;
occurrence_substitute_coordinates/expanded give the actual quotient block square.
Formula.contract_label/expand_label give the actual label square. Fiber relation
identity/comp/converse/graph laws retain both old and inner tags, including empty
blocks. Typed occurrence functions preserve the distinct source formulas.
substitute_negate and negate_subst_derives prove actual/raw negation compatibility;
substitutionFunctor and both tensors/pair/copair/zero laws preserve the full arrow
operations. Formula identity/composition/extensionality are proved; general
arrow-action composition transports and full Appendix A remain separate duties.

Current local evidence: fourteen production modules, all 33 public files and 61
expected rejections; strict full dependency/source audit and checked/committed
archive in provenance/wsl-full-paper-claims/. Exact counts/exits/hashes and
delivery paths are retained there. Short-proof proof/receipt 3d30b77 / d8dc710,
actual-main 640cc9e / d68da50, coherence 8c9e0f3 / a80a353 and all prior results,
stash and receipts persist. Reviews are local author-side; independent replay,
Comparator and official/service checks were not performed.

Pending FP-SCOPE-20261029: v7 §6's dated paragraph still describes faithfulness
and source inputs as unproved. Preserve the versions/diagrams and perform one
coordinated final scope refresh before whole-paper certification, with TeX build/
inspection and correction/map records. It is not a false mathematical theorem;
the prose refresh remains explicitly unfinished.
'''+s[b:]
s=s.replace('1. Complete remaining negation/substitution compatibility and general operation/\ncoordinate laws needed for the model corollary. Finish original isolation witnesses,\nnon-cartesian-closure and every mathematical claim in all three v7 appendices.\nReuse actual maximality and both proof routes without reopening them.', '1. Construct full-source model interpretations and composition with substitution;\nprove the universal-agreement congruence and model corollary. Complete general\narrow-substitution action transports and all Appendix A profiles/gamma/chi/ordinal/\nrenaming/example/book correspondences, including empty profiles and both literal\nsigns. Finish the recorded manuscript scope refresh. Reuse all completed claims\nand both main routes without reopening them.')
s=s.replace('55 controls.','61 controls.')
s=s.replace('640cc9e / d68da50. Deliver', '640cc9e / d68da50 and short-proof proof/receipt 3d30b77 / d8dc710. Deliver')
p.write_text(s)
print('Reconciled original isolation, complete block square, negation compatibility, diagrams and consequences; model/Appendix A/scope refresh continue')
