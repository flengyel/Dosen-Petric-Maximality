for src,dst in [('report','GENTZEN_BLOCKED_DISJUNCTION_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_DISJUNCTION_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_DISJUNCTION_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-sd-'+src+'.md').read_bytes())
active='''## Current eight blocked reductions (29 October 2026)

All twelve binary branches, all six gamma blocked families,
BlockedL.conjunction and BlockedR.disjunction have actual source equations and
instantiated original-rank steps. Six First/Second/Both logical blocked families
and global induction remain open. Successor 811eceeb and all preceding results,
corrections and deliveries are preserved.

BlockedDisjunction.parent_source identifies the exact right2/native disjR source.
source_equation proves its selected cut equal to a concrete prefixRouted
two-cut construction. original_descent supplies the original child full Clean
and strict original rank before routing, with unchanged opposite h/z. A new
native disjR principal has component exchanges below it and only node-free
residual-list equality transport above it. fresh_rho, fresh_blocked, fresh_clean
and fresh_rank_lt prove one-sided rank one, full Clean and 1+h.rho below the
original contracted rank for every returned k, with no returned-rank bound.
Both ih calls precede duplicate context repair and final structural atomization.
The resulting CutFree/Atomized proof has the original exact output and equation.

Appendix C p.260 remains closed. Its p.262 concrete BlockedL.disjunctionFirst
fresh-right-premise correspondence remains open: BlockedR.disjunction instead
proves a fresh disjR in the left premise. All nine manuscript blobs and the
stash persist; unchanged TeX is not rebuilt.

See [report](GENTZEN_BLOCKED_DISJUNCTION_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_DISJUNCTION_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_DISJUNCTION_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Current evidence: provenance/wsl-gentzen-sequential-disjunction/. Twelve new
modules contain 53 source declarations; 726 Lean files are screened. Twenty-two
public files and 29 expected rejections are checked. Exact audit totals/exits,
checked/committed bytes and Downloads paths are in FINAL_VERIFICATION.json and
DELIVERY_REGISTER.json. Four actual initial-output smoke witnesses are explicitly
distinguished from the general equation/rank proof. Reviews are local author-side
reviews; independent replay, Comparator, official/service verification and
publication remain separate unperformed statuses.

Next complete BlockedL.disjunctionFirst/Second/Both and
BlockedR.conjunctionFirst/Second/Both. Preserve two/three-copy arities, original
Clean/rank before adapters, components below fresh native principals and final
structural atomization. Discharge constructor/tag dispatch, fixed-degree all-ranks
Clean under strict DegreeBelow, arbitrary-premise cleaning, strong degree induction
and arbitrary-G normalization. Export unrestricted CutElimination and
AtomizedCutElimination inhabitants, then continue coherence, intended-presentation
and uniform-substitution/congruence bridges, both maximality routes, model
corollary and every claim in all three v7 appendices. The three milestones and
full-paper endpoint remain distinct. Deliver changed reports/records from committed
bytes with verified conflict-preserving copies. Continue under existing
authorization without a routine approval checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current seven blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 if rel=='docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md':
  s=s.replace('the seven remaining sequential logical blocked reductions. All six gamma\nfamilies and BlockedL.conjunction have actual source equations and rank steps.', 'the six remaining First/Second/Both logical blocked reductions. All six gamma\nfamilies, BlockedL.conjunction and BlockedR.disjunction have actual source equations\nand rank steps.').replace('remaining three BlockedL and four BlockedR','remaining three BlockedL and three BlockedR')
 p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('BlockedL.conjunction also has its actual sequential source equation and original-rank\nstep. Complete the seven remaining sequential logical blocked reductions', 'BlockedL.conjunction and BlockedR.disjunction also have their actual sequential\nsource equations and original-rank steps. Complete the six remaining First/Second/Both\nlogical blocked reductions');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches, all six
gamma blocked families, BlockedL.conjunction and BlockedR.disjunction are complete.
Each has an actual source equation and instantiated original-rank step. Six
First/Second/Both logical blocked families and global induction remain open.
Current report: GENTZEN_BLOCKED_DISJUNCTION_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Appendix C p.260 is proved; its p.262 BlockedL.disjunctionFirst correspondence
remains open. Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('all three gamma families complete; four sequential BlockedR reductions pending','all three gamma families and disjunction complete; three sequential BlockedR reductions pending').replace('The seven completed blocked families','The eight completed blocked families').replace('| conjunction / disjunction | Actual source_equation, reconstruction and blockedL_conjunction_rank_step | Pending sequential actual cut reduction |','| conjunction / disjunction | Actual source_equation, reconstruction and blockedL_conjunction_rank_step | Actual source_equation, reconstruction and blockedR_disjunction_rank_step |').replace('adapters are proved for all six gamma entries and BlockedL.conjunction; the\nseven other logical entries remain open.', 'adapters are proved for all six gamma entries and both unary logical entries;\nthe six First/Second/Both entries remain open.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Sequential disjunction completed (29 October 2026)

BlockedR.disjunction now has its actual right2/disjR source, arbitrary-tag
Reduced equation, concrete exact-output prefix repair and instantiated original-rank
step. Its fresh native disjR has component exchanges below it; only node-free
residual-list equality transport follows it. rho=1, blockedness, full Clean and
strict comparison with the original contracted rank are proved without a returned
rank bound. Eight blocked families are complete; six First/Second/Both families
remain. Appendix C p.260 remains proved and p.262 remains open: the latter is the
BlockedL.disjunctionFirst fresh right-premise case. No new manuscript defect was
established. All nine manuscript blobs, preceding corrections, stash and receipts
persist. See GENTZEN_BLOCKED_DISJUNCTION_REPORT.md and its two local reviews.
'''+s[a:];s=s.replace('## Sequential conjunction completed', '## Historical sequential-conjunction checkpoint');p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_668FB50.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER SEQUENTIAL CONJUNCTION: SEVEN BLOCKED CASES REMAIN','CONTINUE V7 AFTER BOTH UNARY LOGICAL REDUCTIONS: SIX BLOCKED CASES REMAIN')
s=s.replace('Read GENTZEN_BLOCKED_CONJUNCTION_REPORT.md', 'Read GENTZEN_BLOCKED_DISJUNCTION_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_CONJUNCTION_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_787EE6C.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_668FB50.txt, archived verbatim.\nThe 787EE6C continuation remains preserved.')
s=s.replace('Seven logical blocked cases\nremain, beginning with BlockedR.disjunction.', '''BlockedR.disjunction is also complete: BlockedDisjunction.parent_source,
source_equation, original_descent and CutCommutation.blockedR_disjunction_rank_step.
The first ih is on original f before component routing, with unchanged h/z.
SequentialDisjunction.fresh_rho/fresh_blocked/fresh_clean/fresh_rank_lt prove the
native disjR principal's rank one and full Clean through its node-free equality
transport; the second ih has total 1+h.rho below original rank. Both prefix
duplicate repairs and output residue preserve exact sequent/equality; final
structural atomization is retained. Six First/Second/Both cases remain.
Appendix C p.262 still requires BlockedL.disjunctionFirst, since this completed
BlockedR branch introduces its fresh principal in the other cut premise.''')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 726 screened Lean files, twenty-two public files and
29 expected rejections; twelve new production modules and 53 source declarations.
Exact audited declaration totals/exits and committed-byte source evidence:
provenance/wsl-gentzen-sequential-disjunction/. Actual initial-output witnesses
are smoke checks, distinguished from the general source/rank proof. Earlier
evidence persists. Reviews are local author-side reviews; independent replay,
Comparator and official/service verification were not performed.
'''+s[b:]
s=s.replace('remaining seven sequential logical blocked reductions:', 'remaining six First/Second/Both logical blocked reductions:').replace(' BlockedR: disjunction, conjunctionFirst,',' BlockedR: conjunctionFirst,').replace('All three gamma families on both sides and BlockedL.conjunction are complete; reuse them.', 'All three gamma families on both sides, BlockedL.conjunction and BlockedR.disjunction\nare complete; reuse them.').replace('26 controls.', '29 controls.')
s=s.replace('787ee6c. Deliver', '787ee6c, plus the sequential-conjunction proof/receipt 4e5c3b1 / 668fb50. Deliver')
p.write_text(s)
print('Reconciled eight completed blocked families, six open, exact p.262 status, and preserved all prior continuations')
