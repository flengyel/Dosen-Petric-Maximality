for src,dst in [('report','GENTZEN_BLOCKED_CONJ_FIRST_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_CONJ_FIRST_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_CONJ_FIRST_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-rf-'+src+'.md').read_bytes())
active='''## Current twelve blocked reductions (29 October 2026)

All twelve binary branches and twelve blocked families have actual source equations
and instantiated original-rank steps. Every BlockedL family and BlockedR gammaMix,
gammaConj, gammaDisj, disjunction and conjunctionFirst are complete. Only
BlockedR.conjunctionSecond/Both and global induction remain open. Both Appendix C
concrete source/rank correspondences remain proved. All earlier results,
corrections, source bytes and delivery receipts persist.

BlockedConjFirst.parent_source/source_equation identify the actual right2/conjR
source and its complete arbitrary-tag Reduced equality. Selected/fixed maps and
residues preserve every ordinal coordinate, including equal-labelled fixed U tags.
SequentialConjFirst.native_equation uses the completed binary and right contraction
equations. SequentialAdapters.right_equation moves all fixed programs after the
fresh native G.conjR recursive cut. original_descent supplies original f full Clean
and strict original rank with unchanged h/z before routing; untouched g supplies
CutFree/Atomized. fresh_clean_and_rank proves native selected succedent rho.right=1,
full Clean and total 1+h.rho.left below the original rank for every returned k.
Both recursive calls are instantiated. Concrete association/residue/duplicate
repair and final atomization preserve exact output, CutFree, Atomized and equality.
No returned-rank bound, output blockedness or general G duality is introduced.

Both Appendix C concrete rows retain their actual source/rank declarations:
p.260's gammaDisj equation and both strict descents, and p.262's first-disjunction
source/rank step and fresh_principal_rank/fresh_total_rank/fresh_total_rank_ge_two.
No exchanged wrapper is assigned native rank one. No new manuscript defect was
established; all nine manuscript blobs and the stash remain unchanged.

See [report](GENTZEN_BLOCKED_CONJ_FIRST_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_CONJ_FIRST_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_CONJ_FIRST_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Evidence: provenance/wsl-gentzen-blocked-right-conj-first/. Eight modules contain
45 source declarations; 764 Lean files are screened. Twenty-six public files
and 37 expected rejections are checked. Actual audit totals/exits, checked/committed
bytes and Downloads paths are in FINAL_VERIFICATION.json and DELIVERY_REGISTER.json.
Four actual initial-output smoke witnesses use witnessed bottom-source proofs and
initiality, covering signed/negative literals, Empty/constants and populated
repeated X/Y/U. They are distinguished from the general source/rank proof.
Reviews are local author-side. Independent replay, Comparator, official/service
verification and publication remain separate unperformed statuses.

Next complete BlockedR.conjunctionSecond/Both, retaining the last three-copy case.
Assemble exhaustive dispatch, fixed-degree all-ranks Clean under strict DegreeBelow,
arbitrary-premise cleaning, strong degree induction and arbitrary-G normalization.
Export actual unrestricted elimination, then continue coherence, intended-presentation
and uniform-substitution/congruence bridges, both maximality routes, model corollary
and every claim in all three v7 appendices. The three milestones and full-paper
endpoint stay distinct. Deliver committed-byte reports/records with verified
conflict-preserving copies; continue under existing authorization without a
routine approval checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current eleven blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 if rel=='docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md':
  s=s.replace('the three remaining BlockedR conjunction reductions. Every BlockedL family\nand BlockedR gammaMix/gammaConj/gammaDisj/disjunction have actual source', 'the two remaining BlockedR conjunctionSecond/Both reductions. Every BlockedL\nfamily and BlockedR gammaMix/gammaConj/gammaDisj/disjunction/conjunctionFirst have actual source').replace('remaining three BlockedR','remaining two BlockedR')
 p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('Every BlockedL family is complete. Complete the three remaining\nBlockedR conjunction reductions and global induction.', 'Every BlockedL family is complete. BlockedR.conjunctionFirst now has its actual\nsource equation and both instantiated original-rank calls. Complete the two\nremaining BlockedR conjunctionSecond/Both reductions and global induction.');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches and twelve
blocked families are complete through actual source equations and instantiated
original-rank steps. BlockedR.conjunctionSecond/Both and global induction remain
open. Current report: GENTZEN_BLOCKED_CONJ_FIRST_REPORT.md; continuation:
CODEX_NEXT_SESSION.txt. Both Appendix C concrete source/rank correspondences remain
proved. Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('all three gamma families and disjunction complete; three sequential BlockedR reductions pending', 'all three gamma families, disjunction and conjunctionFirst complete; two BlockedR reductions pending').replace('The eleven completed blocked families','The twelve completed blocked families').replace('| disjunctionFirst / conjunctionFirst | Actual source_equation, fresh full Clean/rank and blockedL_disjunctionFirst_rank_step; Appendix C p.262 closed | Pending sequential actual cut reduction |','| disjunctionFirst / conjunctionFirst | Actual source_equation, fresh full Clean/rank and blockedL_disjunctionFirst_rank_step; Appendix C p.262 closed | Actual source_equation, fresh full Clean/rank and blockedR_conjunctionFirst_rank_step |').replace('all three BlockedL disjunction entries. Three BlockedR conjunction entries remain open.', 'all three BlockedL disjunction entries and BlockedR.conjunctionFirst. Two BlockedR entries remain open.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## First-conjunction continuation (29 October 2026)

BlockedR.conjunctionFirst now has its actual right2/conjR source equation,
full original first-child Clean/strict descent, fresh native G.conjR full Clean
and both instantiated rank calls. The right-adapter transport is proved separately;
no general G duality or returned-rank bound is assumed. Fixed U tags equal to C
remain distinct from the selected pair. Twelve blocked families are complete;
only BlockedR.conjunctionSecond/Both remain. Both Appendix C rows retain their
proved declarations. No new manuscript defect was found; all nine blobs, stash
and receipts persist. See GENTZEN_BLOCKED_CONJ_FIRST_REPORT.md and its two local
reviews. Preceding local checkpoints remain historical.
'''+s[a:];p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_1A89A84.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER ALL BLOCKEDL: THREE BLOCKEDR CONJUNCTION CASES REMAIN','CONTINUE V7 AFTER TWELVE BLOCKED FAMILIES: CONJUNCTIONSECOND/BOTH REMAIN')
s=s.replace('Read GENTZEN_BLOCKED_DISJ_BOTH_REPORT.md', 'Read GENTZEN_BLOCKED_CONJ_FIRST_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_DISJ_BOTH_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_8A7EE15.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_1A89A84.txt, archived verbatim.\nThe 8A7EE15 continuation remains preserved.')
s=s.replace('is now complete; only three BlockedR conjunction families remain.', '''is now complete. BlockedR.conjunctionFirst is also complete:
BlockedConjFirst.parent_source/source_equation, original_descent,
fresh_clean_and_rank and CutCommutation.blockedR_conjunctionFirst_rank_step.
The actual right2 source and arbitrary-tag equations preserve all fixed tags,
including equal-labelled U tags. SequentialAdapters.right_equation moves fixed
programs after the fresh native G.conjR call. First ih uses original f full Clean
and strict original rank with unchanged h/z before routing; untouched g supplies
CutFree/Atomized. The second uses full fresh Clean and total 1+h.rho.left below
original rank for every returned k, before repair. No returned-rank promise or
assumed general G duality. Final atomization preserves exact output/equality.
Only BlockedR.conjunctionSecond/Both remain.''')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 764 screened Lean files, twenty-six public files and
37 expected rejections; eight new modules and 45 source declarations. Exact
actual audit totals/exits and checked/committed-byte source evidence:
provenance/wsl-gentzen-blocked-right-conj-first/. Four actual initial-output smoke
witnesses use witnessed bottom-source proofs and initiality, covering signed/
negative literals, Empty/constants and populated repeated X/Y/U. They are
separate from the general source/rank proof. All earlier evidence persists.
Reviews are local author-side; independent replay, Comparator and official/service
checks were not performed.
'''+s[b:]
s=s.replace('remaining three logical blocked reductions:\n BlockedR: conjunctionFirst, conjunctionSecond, conjunctionBoth.', 'remaining two logical blocked reductions:\n BlockedR: conjunctionSecond, conjunctionBoth.').replace('logical blocked cases are complete; reuse them.', 'logical blocked cases and BlockedR.conjunctionFirst are complete; reuse them.').replace('35 controls.','37 controls.')
s=s.replace('f81846b / 8a7ee15. Deliver', 'f81846b / 8a7ee15, plus the three-copy/all-BlockedL proof/receipt bd56c03 / 1a89a84. Deliver')
p.write_text(s)
print('Reconciled twelve complete families, two open; preserved all earlier results and Appendix C rows')
