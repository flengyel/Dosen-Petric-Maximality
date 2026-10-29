for src,dst in [('report','GENTZEN_BLOCKED_DISJ_SECOND_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_DISJ_SECOND_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_DISJ_SECOND_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-ls-'+src+'.md').read_bytes())
active='''## Current ten blocked reductions (29 October 2026)

All twelve binary branches, all six gamma families, both unary logical blocked
families and BlockedL.disjunctionFirst/Second have actual source equations and
instantiated original-rank steps. Four blocked families and global induction
remain open. Both Appendix C concrete source/rank correspondences are proved.
All earlier results, corrections, source bytes and delivery receipts persist.

BlockedDisjSecond.parent_source/source_equation identify the actual left2/
disjLLast source and complete selected Reduced equality. original_descent supplies
original g full Clean and strict original rank before routing, with unchanged
h/z. The untouched first child is CutFree/Atomized. Fixed association adapters
are moved after the fresh native G.disjL f₀ k cut. fresh_clean_and_rank and
blockedL_disjunctionSecond_rank_step instantiate both calls, without a returned-
rank bound. Concrete residue/duplicate repair and final atomization preserve
original output, CutFree, Atomized and equation. X's fixed equal-labelled Cs
remain distinct from the selected second-child/fresh pair.

Appendix C p.260 retains the actual gammaDisj equation and both strict descents.
p.262 retains BlockedDisjFirst.source_equation, fresh_clean_and_rank, final rank
step and fresh_principal_rank/fresh_total_rank/fresh_total_rank_ge_two. Right
premise rank one means rho.left=1 at its selected antecedent; total is unchanged
opposite h.rho.right+1≥2. No source wrapper is assigned native rank one. No new
manuscript defect was found. All nine manuscript blobs and the stash are unchanged.

See [report](GENTZEN_BLOCKED_DISJ_SECOND_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_DISJ_SECOND_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_DISJ_SECOND_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Evidence: provenance/wsl-gentzen-blocked-left-disj-second/. Six modules contain
40 new source declarations; 746 Lean files are screened. Twenty-four public files
and 32 expected rejections are checked. Exact audit totals/exits, checked/committed
bytes and Downloads paths are in FINAL_VERIFICATION.json and DELIVERY_REGISTER.json.
Four actual terminal-output smoke witnesses use witnessed bottom-tail first
children and are distinguished from the general source/rank proof. Reviews are
local author-side. Independent replay, Comparator, official/service verification
and publication remain separate unperformed statuses.

Next complete BlockedL.disjunctionBoth and BlockedR.conjunctionFirst/Second/Both.
Preserve both three-copy cases, original Clean/ranks before adapters, native fresh
principals and final structural atomization. Assemble exhaustive dispatch,
fixed-degree all-ranks Clean under strict DegreeBelow, arbitrary-premise cleaning,
strong degree induction and arbitrary-G normalization. Export actual unrestricted
elimination, then continue coherence, intended-presentation and uniform-substitution/
congruence bridges, both maximality routes, model corollary and every claim in all
three v7 appendices. The three milestones and full-paper endpoint stay distinct.
Deliver committed-byte reports/records with verified conflict-preserving copies;
continue under existing authorization without a routine approval checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current nine blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 if rel=='docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md':
  s=s.replace('the five remaining logical blocked reductions. All six gamma families,\nBlockedL.conjunction, BlockedR.disjunction and BlockedL.disjunctionFirst have\nactual source equations and rank steps.', 'the four remaining logical blocked reductions. All six gamma families, both\nunary logical families and BlockedL.disjunctionFirst/Second have actual source\nequations and rank steps.').replace('remaining two BlockedL and three BlockedR','remaining one BlockedL and three BlockedR')
 p.write_text(s)
p=root/'AGENTS.md';s=p.read_text();s=s.replace('with fresh right-premise rho.left=1 and total h.rho.right+1≥2. Complete the five\nremaining logical blocked reductions', 'with fresh right-premise rho.left=1 and total h.rho.right+1≥2. BlockedL.disjunctionSecond\nalso has its actual source/rank construction. Complete the four remaining logical\nblocked reductions');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches, all six
gamma families, both unary logical families and BlockedL.disjunctionFirst/Second
are complete through actual source equations and instantiated original-rank steps.
Four blocked families and global induction remain open. Current report:
GENTZEN_BLOCKED_DISJ_SECOND_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Both Appendix C concrete source/rank correspondences remain proved. Measure
original selected rank before adapters.

'''+s[b:]
s=s.replace('all three gamma families, conjunction and disjunctionFirst complete; two BlockedL reductions pending', 'all three gamma families, conjunction and disjunctionFirst/Second complete; one BlockedL reduction pending').replace('The nine completed blocked families','The ten completed blocked families').replace('| disjunctionSecond / conjunctionSecond | Pending sequential actual cut reduction | Pending sequential actual cut reduction |','| disjunctionSecond / conjunctionSecond | Actual source_equation, fresh full Clean/rank and blockedL_disjunctionSecond_rank_step | Pending sequential actual cut reduction |').replace('BlockedL.disjunctionFirst. Five entries remain open.', 'BlockedL.disjunctionFirst/Second. Four entries remain open.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Second-disjunction continuation (29 October 2026)

BlockedL.disjunctionSecond now has its actual left2/disjLLast source equation,
original second-child full Clean/strict descent, fresh native G.disjL full Clean
and instantiated two-call rank step. The first context stays fixed even when its
formulas equal C; exact positive/negative tag checks preserve this distinction.
Ten blocked families are complete and four remain. Both Appendix C concrete rows
remain proved by their existing declarations. No new manuscript defect was found;
all nine manuscript blobs, stash and receipts persist. See
GENTZEN_BLOCKED_DISJ_SECOND_REPORT.md and its two local reviews.
'''+s[a:]
s=s.replace('## Both Appendix C correspondences proved (29 October 2026)', '## Historical ninth-family checkpoint: both Appendix C correspondences proved (29 October 2026)')
p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_D59CB83.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER DISJUNCTION FIRST: FIVE BLOCKED CASES REMAIN; BOTH ERRATA ROWS PROVED', 'CONTINUE V7 AFTER DISJUNCTION SECOND: FOUR BLOCKED CASES REMAIN; BOTH ERRATA ROWS PROVED')
s=s.replace('Read GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md', 'Read GENTZEN_BLOCKED_DISJ_SECOND_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_DISJ_FIRST_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_0CEF4A4.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_D59CB83.txt, archived verbatim.\nThe 0CEF4A4 continuation remains preserved.')
s=s.replace('Both p.260 and p.262 actual source/rank correspondences are proved. Five cases remain.', '''Both p.260 and p.262 actual source/rank correspondences are proved.
BlockedL.disjunctionSecond is also complete: BlockedDisjSecond.parent_source,
source_equation, original_descent, fresh_clean_and_rank and
CutCommutation.blockedL_disjunctionSecond_rank_step. The first call is on original
g with inherited full Clean and strict original rank, before routing; the untouched
f contributes CutFree/Atomized. The second call is on literal native G.disjL f₀ k,
with unchanged h/z and no returned-rank assumption. Association/residue/duplicate
repairs and final atomization preserve the exact original output/equation. Four
blocked cases remain.''')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 746 screened Lean files, twenty-four public files and
32 expected rejections; six new modules and 40 source declarations. Exact audited
declaration totals/exits and committed-byte source evidence:
provenance/wsl-gentzen-blocked-left-disj-second/. Actual terminal-output smoke
witnesses use witnessed bottom-tail first children and are distinguished from
the general source/rank proof. All earlier evidence persists. Reviews are local
author-side; independent replay, Comparator and official/service checks were not performed.
'''+s[b:]
s=s.replace('remaining five logical blocked reductions:', 'remaining four logical blocked reductions:').replace(' BlockedL: disjunctionSecond, disjunctionBoth.', ' BlockedL: disjunctionBoth.')
s=s.replace('BlockedL.disjunctionFirst are complete; reuse them.', 'BlockedL.disjunctionFirst/Second are complete; reuse them.').replace('31 controls.', '32 controls.')
s=s.replace('0cef4a4. Deliver', '0cef4a4, plus the first-disjunction proof/receipt cecdc79 / d59cb83. Deliver')
p.write_text(s)
print('Reconciled ten completed blocked families, four open, preserved both Appendix C rows and prior continuation bytes')
