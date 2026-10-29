for src,dst in [('report','GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_DISJ_FIRST_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_DISJ_FIRST_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-lf-'+src+'.md').read_bytes())
active='''## Current nine blocked reductions and both Appendix C correspondences (29 October 2026)

All twelve binary branches, all six gamma blocked families, BlockedL.conjunction,
BlockedR.disjunction and BlockedL.disjunctionFirst have actual source equations
and instantiated original-rank steps. Five blocked families and global induction
remain open. Successor 811eceeb, all earlier results/corrections and receipts persist.

BlockedDisjFirst.parent_source and source_equation prove the exact left2/disjLLast
source and complete selected Reduced equality. original_descent supplies the
original first child full Clean and strict original rank before routing, with
unchanged h/z. Structural adapter equations put component routes below literal
G.disjL k g₀ and defer both binary reconstruction adapters until after its cut.
fresh_clean_and_rank and blockedL_disjunctionFirst_rank_step discharge both ih
calls without a returned-rank bound. Exact duplicate/context repair and final
atomization yield the original-output CutFree/Atomized proof and equation.

Both Appendix C erratum correspondences are now proved. The existing p.260
actual gammaDisj equation and both strict descents persist. For p.262,
BlockedDisjFirst.fresh_principal_rank proves rho.left=1 at the right cut premise's
selected antecedent; fresh_total_rank and fresh_total_rank_ge_two prove total
h.rho.right+1≥2. The actual source/rank step and full Clean close this concrete
sequential instance. Right rank names its cut-premise role, not SequentSide.right.
The exchanged disjLLast wrapper is not assigned native rank one. No new manuscript
defect was found; all nine manuscript blobs and the stash are unchanged.

See [report](GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_DISJ_FIRST_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_DISJ_FIRST_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Evidence: provenance/wsl-gentzen-blocked-left-disj-first/. Twelve modules contain
60 new source declarations; 739 Lean files are screened. Twenty-three public
files and 31 expected rejections are checked. Exact audit totals/exits, checked/
committed source bytes and Downloads paths are in FINAL_VERIFICATION.json and
DELIVERY_REGISTER.json. Four actual terminal-output smoke witnesses use witnessed
bottom-tail children; they are distinguished from the general source/rank proof.
Reviews are local author-side reviews. Independent replay, Comparator, official/
service checks and publication remain separate unperformed statuses.

Next complete BlockedL.disjunctionSecond/Both and BlockedR.conjunctionFirst/Second/
Both. Preserve two/three-copy arities, original Clean/ranks before adapters,
fresh native principals and final structural atomization. Discharge exhaustive
dispatch, fixed-degree all-ranks Clean under strict DegreeBelow, arbitrary-premise
cleaning, strong degree induction and arbitrary-G normalization. Export actual
unrestricted CutElimination/AtomizedCutElimination, then continue coherence,
intended-presentation and uniform-substitution/congruence bridges, both maximality
routes, model corollary and all claims in all three v7 appendices. The three
milestones and full-paper endpoint remain distinct. Deliver committed-byte reports/
records with verified conflict-preserving copies; continue without a routine checkpoint.

'''
p262old='| Appendix C, p.262 paragraph | The new native disjL principal occurrence in the right premise has right rank one; total rank is the unchanged left rank plus one and at least two. | rank_fresh_disjL, rank_ge_two and native principal blockedness compile. Requires the actual sequential blocked disjunction reduction; source disjLLast exchanges stay explicit. | General native rank statements compiled; concrete source reduction correspondence open. |'
p262new='| Appendix C, p.262 paragraph | The native disjL right cut premise has rho.left=1 at its selected antecedent; total rank is unchanged opposite h.rho.right+1≥2. | BlockedDisjFirst.fresh_principal_rank, fresh_total_rank, fresh_total_rank_ge_two; source_equation, original_descent, fresh_clean_and_rank; CutCommutation.blockedL_disjunctionFirst_rank_step. | Actual sequential source/native correspondence, full Clean and both strict original-rank calls proved. disjLLast wrapper exchanges are explicit and not assigned native rank one. |'
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current eight blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 s=s.replace('equation and both strict original-child rank inequalities. Its p.262 sequential\nfresh-right-principal correspondence remains open. Selected-cut positivity and\nnative fresh-principal rank-one laws compile.', 'equation and both strict original-child rank inequalities. Its p.262 concrete\nsequential source/rank correspondence is proved by BlockedDisjFirst.source_equation,\nfresh_clean_and_rank, the three fresh-principal/total-rank declarations and\nblockedL_disjunctionFirst_rank_step. Both erratum rows are closed.')
 s=s.replace(p262old,p262new)
 if rel=='docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md':
  s=s.replace('the six remaining First/Second/Both logical blocked reductions. All six gamma\nfamilies, BlockedL.conjunction and BlockedR.disjunction have actual source equations\nand rank steps.', 'the five remaining logical blocked reductions. All six gamma families,\nBlockedL.conjunction, BlockedR.disjunction and BlockedL.disjunctionFirst have\nactual source equations and rank steps.').replace('remaining three BlockedL and three BlockedR','remaining two BlockedL and three BlockedR')
  s=s.replace('strict descents. Its p.262 sequential fresh-right-principal correspondence remains open.', 'strict descents. Its p.262 actual sequential source/rank correspondence is proved\nby BlockedDisjFirst.source_equation, fresh_clean_and_rank, fresh_principal_rank,\nfresh_total_rank, fresh_total_rank_ge_two and blockedL_disjunctionFirst_rank_step.')
 p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('logical blocked reductions and global induction.', 'logical blocked reductions and global induction.')
s=s.replace('source equations and original-rank steps. Complete the six remaining First/Second/Both\nlogical blocked reductions', 'source equations and original-rank steps. BlockedL.disjunctionFirst also has its\nactual sequential source/rank proof, closing the concrete Appendix C p.262 row\nwith fresh right-premise rho.left=1 and total h.rho.right+1≥2. Complete the five\nremaining logical blocked reductions')
p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches, all six
gamma families, both unary logical blocked families and BlockedL.disjunctionFirst
are complete through actual source equations and instantiated original-rank steps.
Five blocked families and global induction remain open. Current report:
GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Both Appendix C p.260 and p.262 concrete source/rank correspondences are proved.
Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('all three gamma families and conjunction complete; three sequential BlockedL reductions pending','all three gamma families, conjunction and disjunctionFirst complete; two BlockedL reductions pending').replace('The eight completed blocked families','The nine completed blocked families').replace('| disjunctionFirst / conjunctionFirst | Pending sequential actual cut reduction | Pending sequential actual cut reduction |','| disjunctionFirst / conjunctionFirst | Actual source_equation, fresh full Clean/rank and blockedL_disjunctionFirst_rank_step; Appendix C p.262 closed | Pending sequential actual cut reduction |').replace('adapters are proved for all six gamma entries and both unary logical entries;\nthe six First/Second/Both entries remain open.', 'adapters are proved for all six gamma entries, both unary logical entries and\nBlockedL.disjunctionFirst. Five entries remain open.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Both Appendix C correspondences proved (29 October 2026)

BlockedL.disjunctionFirst now has its actual left2/disjLLast source equation,
original first-child full Clean/strict descent, fresh native G.disjL full Clean,
and instantiated two-call original-rank step. This closes the p.262 concrete
correspondence: fresh_principal_rank proves rho.left=1 in the right cut premise;
fresh_total_rank and fresh_total_rank_ge_two prove unchanged opposite rho.right+1≥2.
The source disjLLast wrapper itself is not assigned native rank one. Both adapters
are moved after the fresh recursive cut. The p.260 actual gammaDisj correspondence
is preserved. Nine blocked families are complete and five remain open.
All live parallel passages and both errata rows are reconciled in this pass.
No new manuscript defect was established; all nine manuscript blobs and the
stash persist. Report/reviews: GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md and its two reviews.
Earlier dated progress entries retain their checkpoint statements; the current
status is this paragraph and the updated formal-correspondence errata table.
'''+s[a:]
s=s.replace('## Sequential disjunction completed','## Historical eight-family checkpoint')
s=s.replace('the p.262 sequential fresh-right-principal correspondence remains open, as\nrecorded in the v7 statement ledger.', 'the p.262 actual sequential source/rank correspondence is now also proved by\nBlockedDisjFirst.source_equation, fresh_clean_and_rank, the three concrete\nfresh/total-rank declarations and blockedL_disjunctionFirst_rank_step, as recorded\nin the v7 statement ledger.')
s=s.replace('Existing cutRank_ge_two covers head cuts. The concrete fresh-principal calculation and positional correspondence remain to be proved.', 'BlockedDisjFirst.source_equation and blockedL_disjunctionFirst_rank_step prove the actual sequential instance. fresh_principal_rank gives rho.left=1 in the right cut premise; fresh_total_rank and fresh_total_rank_ge_two give unchanged opposite rho.right+1≥2. original_descent and fresh_clean_and_rank discharge original Clean/strict rank before adapters. Concrete correspondence proved.')
s=s.replace('## Selected-cut rank and base-case progress (28 October 2026)', '## Historical selected-cut rank and base-case checkpoint (28 October 2026)')
p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_0CEF4A4.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER BOTH UNARY LOGICAL REDUCTIONS: SIX BLOCKED CASES REMAIN','CONTINUE V7 AFTER DISJUNCTION FIRST: FIVE BLOCKED CASES REMAIN; BOTH ERRATA ROWS PROVED')
s=s.replace('Read GENTZEN_BLOCKED_DISJUNCTION_REPORT.md','Read GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_DISJUNCTION_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_668FB50.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_0CEF4A4.txt, archived verbatim.\nThe 668FB50 continuation remains preserved.')
s=s.replace('p.262 remains open.', 'p.262 is now proved by the concrete first-disjunction case below.')
s=s.replace('Six First/Second/Both cases remain.\nAppendix C p.262 still requires BlockedL.disjunctionFirst, since this completed\nBlockedR branch introduces its fresh principal in the other cut premise.', '''BlockedL.disjunctionFirst is also complete: BlockedDisjFirst.parent_source,
source_equation, original_descent, fresh_clean_and_rank and
CutCommutation.blockedL_disjunctionFirst_rank_step. Both calls use strict original
rank and full Clean, with unchanged h/z. Both binary reconstruction adapters
are moved after the fresh native G.disjL recursive cut. The three concrete
Appendix C declarations fresh_principal_rank, fresh_total_rank and
fresh_total_rank_ge_two close p.262: right cut premise rho.left=1, total unchanged
opposite h.rho.right+1≥2. The exchanged disjLLast wrapper is not assigned rank one.
Both p.260 and p.262 actual source/rank correspondences are proved. Five cases remain.''')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 739 screened Lean files, twenty-three public files and
31 expected rejections; twelve new modules and 60 source declarations. Exact
audited declaration totals/exits and committed-byte source evidence:
provenance/wsl-gentzen-blocked-left-disj-first/. Actual terminal-output smoke
witnesses use witnessed bottom-tail children and are distinguished from the
general source/rank proof. Earlier evidence persists. Reviews are local author-side;
independent replay, Comparator and official/service checks were not performed.
'''+s[b:]
s=s.replace('remaining six First/Second/Both logical blocked reductions:', 'remaining five logical blocked reductions:').replace(' BlockedL: disjunctionFirst, disjunctionSecond, disjunctionBoth.', ' BlockedL: disjunctionSecond, disjunctionBoth.')
s=s.replace('All three gamma families on both sides, BlockedL.conjunction and BlockedR.disjunction\nare complete; reuse them.', 'All three gamma families on both sides, both unary logical cases and\nBlockedL.disjunctionFirst are complete; reuse them.')
s=s.replace("Preserve Appendix C's completed p.260 source/rank correspondence. Close its\np.262 Lean row only after the actual sequential blocked instance.", "Preserve both completed Appendix C source/rank correspondences, including the\nactual p.262 first-disjunction instance and its full native fresh Clean proof.")
s=s.replace('29 controls.', '31 controls.')
s=s.replace('668fb50. Deliver', '668fb50, and the sequential-disjunction proof/receipt 5e42101 / 0cef4a4. Deliver')
p.write_text(s)
print('Reconciled all live Appendix C rows/passages; nine blocked families proved, five remain; historical continuations retained')
