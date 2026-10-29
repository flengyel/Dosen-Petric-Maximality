for src,dst in [('report','GENTZEN_BLOCKED_DISJ_BOTH_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_DISJ_BOTH_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_DISJ_BOTH_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-lb-'+src+'.md').read_bytes())
active='''## Current eleven blocked reductions (29 October 2026)

All twelve binary branches and every BlockedL family have actual source equations
and instantiated original-rank steps. Eleven blocked families are complete;
BlockedR.conjunctionFirst/Second/Both and global induction remain open. Both
Appendix C concrete source/rank correspondences remain proved. All earlier
results, corrections, source bytes and delivery receipts persist.

BlockedDisjBoth.parent_source/source_equation identify the actual left3/disjLLast
source, contracting two original parametric copies and the terminal fresh copy.
first_get/second_get/fresh_get compare every selected tag; first_fixed/second_fixed
and the two residues compare all other tags, including equal-labelled formulas.
SequentialDisjBoth.terminal_factor/source_denote and native_equation give the
arbitrary-tag three-cut equation. Its inputProgram has a proved unique fresh
fiber; all fixed adapters move past the fresh native G.disjL cut. Both original
child calls inherit full Clean and strict original rank, with unchanged h/z,
before routing. fresh_clean_and_rank proves full Clean and total h.rho.right+1
below the original contracted rank independently of returned k/l. The third call
is instantiated before concrete three-copy repairs. Final atomization follows
cut-freeness and preserves exact output/equality. No returned-rank bound or
output blockedness promise is introduced.

Appendix C p.260 retains its actual gammaDisj equation and both strict descents.
p.262 retains the actual first-disjunction source/rank step and
fresh_principal_rank/fresh_total_rank/fresh_total_rank_ge_two. The right cut
premise has rho.left=1 at its native fresh leaf; total is unchanged opposite
h.rho.right+1≥2. No exchanged source wrapper is assigned native rank one. No new
manuscript defect was established; all nine blobs and the stash are unchanged.

See [report](GENTZEN_BLOCKED_DISJ_BOTH_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_DISJ_BOTH_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_DISJ_BOTH_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Evidence: provenance/wsl-gentzen-blocked-left-disj-both/. Eight modules contain
49 source declarations; 755 Lean files are screened. Twenty-five public files
and 35 expected rejections are checked. Actual audit totals/exits, checked/committed
bytes and Downloads paths are in FINAL_VERIFICATION.json and DELIVERY_REGISTER.json.
Four actual terminal-output smoke witnesses use witnessed bottom-tail first
children and are distinguished from the general source/rank proof. Reviews are
local author-side. Independent replay, Comparator, official/service verification
and publication remain separate unperformed statuses.

Next complete the three BlockedR conjunction families, preserving its three-copy
case. Assemble exhaustive dispatch, fixed-degree all-ranks Clean under strict
DegreeBelow, arbitrary-premise cleaning, strong degree induction and arbitrary-G
normalization. Export actual unrestricted elimination, then continue coherence,
intended-presentation and uniform-substitution/congruence bridges, both maximality
routes, the model corollary and every mathematical claim in all three v7 appendices.
The three milestones and full-paper endpoint remain distinct. Deliver committed-
byte reports/records with verified conflict-preserving copies, then continue
under existing authorization without a routine approval checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current ten blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 if rel=='docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md':
  s=s.replace('the four remaining logical blocked reductions. All six gamma families, both\nunary logical families and BlockedL.disjunctionFirst/Second have actual source\nequations and rank steps.', 'the three remaining BlockedR conjunction reductions. Every BlockedL family\nand BlockedR gammaMix/gammaConj/gammaDisj/disjunction have actual source\nequations and rank steps.').replace('remaining one BlockedL and three BlockedR','remaining three BlockedR')
 p.write_text(s)
p=root/'AGENTS.md';s=p.read_text();s=s.replace('also has its actual source/rank construction. Complete the four remaining logical\nblocked reductions and global induction.', 'also has its actual source/rank construction. BlockedL.disjunctionBoth now has\nthe actual left3 source equation, both original descents and three instantiated\nrank calls. Every BlockedL family is complete. Complete the three remaining\nBlockedR conjunction reductions and global induction.');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches and every
BlockedL family are complete through actual source equations and instantiated
original-rank steps. Eleven blocked families are proved; three BlockedR conjunction
families and global induction remain open. Current report:
GENTZEN_BLOCKED_DISJ_BOTH_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Both Appendix C concrete source/rank correspondences remain proved. Measure
original selected rank before adapters.

'''+s[b:]
s=s.replace('all three gamma families, conjunction and disjunctionFirst/Second complete; one BlockedL reduction pending', 'all seven BlockedL families complete, including the three-copy disjunctionBoth case').replace('The ten completed blocked families','The eleven completed blocked families').replace('| disjunctionBoth / conjunctionBoth | Pending sequential actual cut reduction | Pending sequential actual cut reduction |','| disjunctionBoth / conjunctionBoth | Actual left3 source_equation, both original descents, fresh full Clean/rank and blockedL_disjunctionBoth_rank_step | Pending sequential actual cut reduction |').replace('BlockedL.disjunctionFirst/Second. Four entries remain open.', 'all three BlockedL disjunction entries. Three BlockedR conjunction entries remain open.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Three-copy disjunction continuation (29 October 2026)

BlockedL.disjunctionBoth now has its actual left3/disjLLast source equation,
three exact selected-tag comparisons, both original full Clean/strict descents,
fresh native G.disjL full Clean and instantiated three-call rank step. Fixed
adapters and all three duplicate copies are repaired after the fresh cut; no
returned-rank promise is added. Eleven blocked families and every BlockedL family
are complete; three BlockedR conjunction families remain. Both Appendix C rows
retain their proved concrete declarations. No new manuscript defect was found;
all nine blobs, stash and receipts persist. See GENTZEN_BLOCKED_DISJ_BOTH_REPORT.md
and its two local reviews. The preceding tenth-family checkpoint is historical.
'''+s[a:];p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_8A7EE15.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER DISJUNCTION SECOND: FOUR BLOCKED CASES REMAIN; BOTH ERRATA ROWS PROVED', 'CONTINUE V7 AFTER ALL BLOCKEDL: THREE BLOCKEDR CONJUNCTION CASES REMAIN')
s=s.replace('Read GENTZEN_BLOCKED_DISJ_SECOND_REPORT.md', 'Read GENTZEN_BLOCKED_DISJ_BOTH_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_DISJ_SECOND_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_D59CB83.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_8A7EE15.txt, archived verbatim.\nThe D59CB83 continuation remains preserved.')
s=s.replace('blocked cases remain.\n\n', '''blocked cases remain at that checkpoint.
BlockedL.disjunctionBoth is also complete: BlockedDisjBoth.parent_source,
source_equation, first_descent, second_descent, fresh_clean_and_rank and
CutCommutation.blockedL_disjunctionBoth_rank_step. The actual left3 source
contracts both parametric copies and the terminal fresh C. Exact selected/fixed
maps and terminal_factor/source_denote prove arbitrary-tag correspondence.
SequentialDisjBoth.native_equation combines the existing gamma and head-contraction
equations. Both original-child ih calls inherit full Clean and strict original
rank with unchanged h/z before routing. The third call is on literal G.disjL,
proved fresh full Clean and total h.rho.right+1 below the original rank for every
returned pair, before all fixed adapters and three-copy repairs. Exact output,
CutFree/Atomized/equality follow through final atomization. Every BlockedL family
is now complete; only three BlockedR conjunction families remain.

''',1)
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 755 screened Lean files, twenty-five public files and
35 expected rejections; eight new modules and 49 source declarations. Exact
actual audit totals/exits and checked/committed-byte source evidence:
provenance/wsl-gentzen-blocked-left-disj-both/. Four actual terminal-output smoke
witnesses use witnessed bottom-tail first children, covering signed/negative
literals, Empty/constants and all four populated repeated context groups. They
are distinguished from the general source/rank proof. All earlier evidence
persists. Reviews are local author-side; independent replay, Comparator and
official/service checks were not performed.
'''+s[b:]
s=s.replace('remaining four logical blocked reductions:\n BlockedL: disjunctionBoth.\n BlockedR:', 'remaining three logical blocked reductions:\n BlockedR:').replace('All three gamma families on both sides, both unary logical cases and\nBlockedL.disjunctionFirst/Second are complete; reuse them.', 'Every BlockedL family, all three gamma families on both sides and both unary\nlogical blocked cases are complete; reuse them.').replace('32 controls.','35 controls.')
s=s.replace('cecdc79 / d59cb83. Deliver', 'cecdc79 / d59cb83, plus the second-disjunction proof/receipt f81846b / 8a7ee15. Deliver')
p.write_text(s)
print('Reconciled all BlockedL, eleven completed families, three open; preserved Appendix C and prior continuation')
