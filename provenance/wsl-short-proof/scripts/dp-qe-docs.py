for src,dst in [('report','SHORT_QE_REPORT.md'),('hostile','reviews/SHORT_QE_HOSTILE.md'),('writing','reviews/SHORT_QE_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-qe-'+src+'.md').read_bytes())
active='''## Current short q_A/e_A proof (29 October 2026)

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

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md','docs/PRESENTATION_CORRESPONDENCE.md']:
 p=root/rel;s=p.read_text();a=s.index('\n')+1
 block=active if rel!='README.md' else active.replace('](SHORT_','](docs/SHORT_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+'\n'+block+s[a:];s=s.replace('## Current actual source maximality and derived negation','## Retained actual source maximality and derived negation checkpoint');p.write_text(s)
p=root/'docs/MANUSCRIPT_STATEMENTS.md';s=p.read_text();lines=s.splitlines()
for i,t in enumerate(lines):
 if t.startswith('| `lem:structural-isos` |'):lines[i]='| `lem:structural-isos` | ShortProof.q_definition/e_definition, q_qInverse/qInverse_q, e_eInverse/eInverse_e; PresentationShortQ.lean, PresentationShortE.lean | Complete direct correspondence: particular manuscript maps, explicit original raw inverses and both inverse laws for every formula A and P : Type u. Ten raw/quotient substitution equations give exact cross-universe transport. |'
 if t.startswith('| `lem:collapse` |'):lines[i]='| `lem:collapse` | ShortProof.total, terminal_id/terminal_pair, r_i, projection_id, diagonal_u, projections; PresentationShortTerminal.lean, PresentationShortProjection.lean | Complete distinct short q/e proof directly modulo arbitrary Congruence (Presentation.operations P), assuming every K_A. Original inverse equations and original coherence only; no quotient faithfulness or cancellation of j_A. Existing ContextualCollapse.total symmetric-fold route preserved. |'
 if t.startswith('| `thm:main` |'):lines[i]='| `thm:main` | Presentation.short_maximality and Presentation.maximality; congruence_dichotomy; raw_maximality | Both actual source proof routes are instantiated. P : Type u arbitrary, full proof congruences and explicit uniform endosubstitution closure; all inputs and raw/quotient correspondence proved. |'
p.write_text('\n'.join(lines)+'\n')
p=root/'docs/MANUSCRIPT_COVERAGE.md';s=p.read_text().replace('The distinct full-paper endpoint remains open: short q/e route, model corollary and further operation/substitution/appendix claims.', 'The distinct short q/e route is now proved by Presentation.short_maximality. The full-paper endpoint remains open: model corollary and further operation/substitution/isolation/appendix claims.');p.write_text(s)
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text();a=s.index('811eceeb and all successor reviews',s.index('## Immediate continuation'));b=s.index('At unchanged degree',a)
s=s[:a]+'''811eceeb and all successor reviews are incorporated. All cut elimination,
coherence, intended occurrence data, actual quotient functors/recovery, derived
negation/naturality, full proof-congruence/closure correspondence and actual
maximality are proved. The distinct short q_A/e_A proof now has concrete raw
inverses, all four original inverse equations, exact substitution transport,
direct modulo-congruence collapse and Presentation.short_maximality. Preserve
both routes. Continue remaining negation/substitution and general operation/
coordinate laws, original isolation witnesses, universal-model corollary,
non-cartesian-closure and every remaining v7 claim. The full-paper endpoint is
unchanged. Preserve the discharged recursion contract below.

'''+s[b:];p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('the separate short q_A/e_A route, remaining operation/substitution compatibility,\nmodel corollary and every full-paper obligation. Preserve the symmetric-fold route.', 'remaining operation/substitution compatibility, original isolation witnesses,\nmodel corollary and every full-paper obligation. The distinct short q_A/e_A route\nis now proved with explicit inverses and actual short_maximality. Preserve both routes.');p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Exact short q_A/e_A proof continuation (29 October 2026)

The particular q_A and e_A have concrete raw inverses, both original inverse
equations and exact whole-arrow substitution transport. The manuscript's short
collapse proof is now implemented directly modulo congruence and connected to
actual main theorem by Presentation.short_maximality. The retained symmetric-
fold route is unchanged. This uses the full contract's permitted direct inverse
proofs, not a bijective-graph inference. The e inverse uses a distributive
section and an explicit witnessed-zero branch; no distributive isomorphism is
introduced. All affected active maps and continuation are reconciled. No new
manuscript defect was established; nine manuscript blobs and all accepted
corrections remain preserved. Model and remaining full-paper claims continue.
'''+s[a:];p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();s+='''
## Distinct short-proof continuation (29 October 2026)

All completed constructor/rank/coherence/source-main results persist. The exact
q_A/e_A inverses, direct short congruence collapse and actual short_maximality
are now proved; see SHORT_QE_REPORT.md. Both maximality routes are retained.
Remaining model, substitution/operation/isolation and appendix duties continue.
''';p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_D68DA50.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER ACTUAL MAXIMALITY: SHORT PROOF AND FULL-PAPER CLAIMS','CONTINUE V7 AFTER BOTH MAXIMALITY ROUTES: MODEL AND REMAINING PAPER CLAIMS')
s=s.replace('Read SOURCE_MAXIMALITY_REPORT.md', 'Read SHORT_QE_REPORT.md and its hostile/writing reviews, reusing\nSOURCE_MAXIMALITY_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_A80A353.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_D68DA50.txt, archived verbatim.\nThe A80A353 continuation remains preserved.')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''The exact short q_A/e_A proof is now complete: ShortProof.qTerm/qInverseTerm,
eTerm/eInverseTerm, q_definition/e_definition, all four original inverse equations,
and ten raw/quotient substitution laws. sourceConjTerm/sectionTerm supply only
the needed actual section; e's inverse kills the unused summand with explicit
zero witness fst;diag. terminal_id/terminal_pair use q's original inverse;
r_i, projection_id, diagonal_u and projections complete direct congruence collapse.
ShortProof.total is independent of the symmetric-fold collapse. Actual
Presentation.short_maximality connects isolation/all-contexts and the new route.
Both actual main proofs are now preserved; the full paper still has remaining
model, negation/substitution/operation, isolation, non-cartesian-closure and
appendix claims. Do not reopen the completed short construction.

Current local evidence: six production modules, all 32 public files and 55
expected rejections, full strict dependency/source audit and checked/committed
archive in provenance/wsl-short-proof/. Actual counts/exits/hashes and delivery
paths are retained there. Actual-main proof/receipt 640cc9e / d68da50 and
coherence proof/receipt 8c9e0f3 / a80a353, all prior proofs, stash and receipts
persist. Reviews are local author-side; independent replay, Comparator and
official/service checks were not performed.
'''+s[b:]
s=s.replace('1. Formalize the distinct short q_A/e_A proof and its actual inverse equations.\nComplete remaining negation/substitution compatibility and operation/coordinate\nlaws, the model corollary and every mathematical claim in all three v7 appendices.\nReuse actual-presentation maximality and preserve its symmetric-fold route.', '1. Complete remaining negation/substitution compatibility and general operation/\ncoordinate laws needed for the model corollary. Finish original isolation witnesses,\nnon-cartesian-closure and every mathematical claim in all three v7 appendices.\nReuse actual maximality and both proof routes without reopening them.')
s=s.replace('52 controls.','55 controls.')
s=s.replace('8c9e0f3 / a80a353. Deliver', '8c9e0f3 / a80a353 and actual-main proof/receipt 640cc9e / d68da50. Deliver')
p.write_text(s)
print('Reconciled exact q/e isomorphisms, short collapse and actual short main; remaining full-paper obligations persist')
