for src,dst in [('report','SOURCE_MAXIMALITY_REPORT.md'),('hostile','reviews/SOURCE_MAXIMALITY_HOSTILE.md'),('writing','reviews/SOURCE_MAXIMALITY_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-sp-'+src+'.md').read_bytes())
active='''## Current actual source maximality and derived negation (29 October 2026)

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

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md','docs/PRESENTATION_CORRESPONDENCE.md']:
 p=root/rel;s=p.read_text();a=s.index('\n')+1
 block=active if rel!='README.md' else active.replace('](SOURCE_','](docs/SOURCE_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+'\n'+block+s[a:]
 s=s.replace('## Current Positive, Reduced and Boolean coherence','## Retained Positive, Reduced and Boolean coherence checkpoint')
 p.write_text(s)
p=root/'docs/MANUSCRIPT_COVERAGE.md';s=p.read_text();lines=s.splitlines()
for i,t in enumerate(lines):
 if t.startswith('| II | '):lines[i]='| II | Maximality conditional on explicit coherence, normalization, presentation, and substitution inputs | Complete: relative_maximality remains proved and preserved; its complete actual-source instance is now Presentation.maximality. |'
 if t.startswith('| III | '):lines[i]='| III | Maximality for the actual Došen–Petrić presentation with all bridges proved | Complete for the actual maximality theorem: Presentation.maximality/congruence_dichotomy/raw_maximality, full raw/quotient proof-congruence correspondence, closure transfer and every relative input instantiated. The distinct full-paper endpoint remains open: short q/e route, model corollary and further operation/substitution/appendix claims. |'
 if t.startswith('| Boolean Coherence / faithful interpretation |'):lines[i]=t.replace('Full quotient red-functor/equivalence laws remain separate appendix duties.', 'The actual quotient reduction/inclusion functors, normalization natural isomorphism and explicit reverse recovery are now proved.')
p.write_text('\n'.join(lines)+'\n')
p=root/'docs/MANUSCRIPT_STATEMENTS.md';s=p.read_text();lines=s.splitlines()
for i,t in enumerate(lines):
 if t.startswith('| `thm:main` |'):lines[i]='| `thm:main` | Presentation.maximality; congruence_dichotomy; raw_maximality, PresentationMaximality.lean | Actual equation-generated source, arbitrary P : Type u, full proof congruences with explicit endosubstitution closure; complete inputs and exact raw/quotient correspondence. The symmetric-fold route is instantiated; the distinct short q/e proof remains open. |'
 if t.startswith('| §14.2 source signed-literal reduction used toward §3 coherence |'):lines[i]='| §14.2 source signed-literal reduction used toward §3 coherence | Reduced.reduceHom/reductionFunctor/inclusionFunctor, normalizationNaturalIso, reduction_inclusion, recover_reduceHom/reduce_recoverHom | Actual quotient descent, functor laws, equality reflection, source natural isomorphism and reverse endpoint-cast recovery are proved for arbitrary P. Earlier raw red/representation proofs remain preserved. |'
 if t.startswith('| §3 relation operations |'):lines[i]=t.replace('faithfulness remains open.', 'Presentation.coherence proves faithfulness in that same original quotient.')
p.write_text('\n'.join(lines)+'\n')
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text();a=s.index('811eceeb and all successor reviews',s.index('## Immediate continuation'));b=s.index('At unchanged degree',a)
s=s[:a]+'''811eceeb and all successor reviews are incorporated. All cut elimination,
Positive/Reduced/Boolean coherence, intended occurrence interpretation, actual
quotient reduction/inclusion and recovery, derived negation/naturality, full
raw/quotient proof-congruence correspondence and actual maximality are proved.
The actual main theorem and its equality/total dichotomy now instantiate every
relative input. Reuse them. Continue the separate short q_A/e_A proof, remaining
negation/substitution compatibility and operation/coordinate laws, universal-
model corollary and all remaining v7 claims. The three milestones do not certify
the complete paper. Preserve the discharged recursion contract below.

'''+s[b:];p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('Continue full source congruence/uniform-substitution correspondence,\nactual maximality, both proof routes, model corollary and full-paper obligations.', 'Actual full proof-congruence correspondence, substitution-closure transfer,\nderived arrow negation/naturality and actual maximality are now proved. Continue\nthe separate short q_A/e_A route, remaining operation/substitution compatibility,\nmodel corollary and every full-paper obligation. Preserve the symmetric-fold route.');p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Actual source maximality continuation (29 October 2026)

Actual quotient reduction/inclusion, both recovery laws, derived negation with
natural DN/DM comparisons, explicit raw negation and its original-tag converse
relation are proved. Full raw/quotient proof-congruence correspondence and uniform
closure transfer now instantiate actual maximality and its equality/total
dichotomy. All relevant live maps and milestone rows are reconciled together.
No new manuscript defect was established. All nine manuscript blobs, three
appendices, ten diagrams, accepted corrections, prior proofs and the stash
remain unchanged. Full-paper completion is separate: the short q/e proof,
model and remaining substitution/operation/ordinal/appendix claims continue.
'''+s[a:];p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();s+='''
## Actual source maximality continuation (29 October 2026)

All constructor/tag/rank and coherence results persist. Actual quotient reduction,
derived negation/naturality, full proof-congruence/closure correspondence and
Presentation.maximality/congruence_dichotomy/raw_maximality are now proved; see
SOURCE_MAXIMALITY_REPORT.md. The separate short proof, model and remaining full-
paper claims continue. Constructor coverage remains a discharged prerequisite.
''';p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_A80A353.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER BOOLEAN COHERENCE: COMPLETE SOURCE MAXIMALITY BRIDGES','CONTINUE V7 AFTER ACTUAL MAXIMALITY: SHORT PROOF AND FULL-PAPER CLAIMS')
s=s.replace('Read GENTZEN_COHERENCE_REPORT.md', 'Read SOURCE_MAXIMALITY_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_COHERENCE_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_75B8E48.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_A80A353.txt, archived verbatim.\nThe 75B8E48 continuation remains preserved.')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Actual source maximality is now proved by Presentation.maximality,
congruence_dichotomy and raw_maximality. Full ProofCongruence/RawProofCongruence
relations correspond pointwise in both directions; uniform closure transfers;
fragment and fragment_closed instantiate the exact relative interface. All other
inputs are actual source data. Reduced quotient reduction/inclusion, normalization
natural isomorphism and both recovery equations are proved. Derived source
negation has a full raw representative, exact original-tag converse graph,
contravariant functor laws and natural DN/DM comparison equations. Preserve them.
Milestone III's actual theorem is now instantiated; full-paper completion remains
separate. Derived-negation/substitution compatibility is still an explicit
operation-law duty, alongside the short proof/model/remaining appendix claims.

Current local evidence: eighteen production modules; all 31 public files,
actual source functor/negation/congruence/main signatures and 52 expected
rejections; strict full dependency/source audit and checked/committed source
archive in provenance/wsl-full-source-bridges/. Actual counts/exits/hashes and
committed-byte delivery paths are retained there. Earlier coherence proof/receipt
8c9e0f3 / a80a353 and all preceding results, reports and receipts persist.
Reviews are local author-side; independent replay, Comparator and official/service
verification were not performed.
'''+s[b:]
s=s.replace('1. Complete full source proof-congruence and uniform-substitution correspondence,\ninstantiate actual-presentation maximality, and formalize the short q_A/e_A proof,', '1. Formalize the distinct short q_A/e_A proof and its actual inverse equations,\ncomplete remaining negation/substitution compatibility and operation/coordinate laws,')
s=s.replace('48 controls.', '52 controls.')
s=s.replace('852502b / 75b8e48. Deliver', '852502b / 75b8e48 and actual-coherence proof/receipt 8c9e0f3 / a80a353. Deliver')
p.write_text(s)
print('Reconciled actual source main theorem and full congruence correspondence; full-paper tasks continue')
