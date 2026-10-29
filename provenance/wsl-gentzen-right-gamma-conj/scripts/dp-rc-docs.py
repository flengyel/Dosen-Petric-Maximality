for src,dst in [('report','GENTZEN_RIGHT_GAMMA_CONJ_REPORT.md'),('hostile','reviews/GENTZEN_RIGHT_GAMMA_CONJ_HOSTILE.md'),('writing','reviews/GENTZEN_RIGHT_GAMMA_CONJ_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-rc-'+src+'.md').read_bytes())
active='''## Current six gamma blocked reductions (29 October 2026)

Successor 811eceeb remains incorporated. All twelve binary branches and all six
gamma blocked families are proved: gammaMix, gammaConj and gammaDisj on both
BlockedL and BlockedR. Each has an actual source equation, exact-output
reconstruction, eliminated witness and instantiated original-rank step. Eight
sequential logical blocked reductions and global induction remain open.

The new final declaration is CutCommutation.blockedR_gammaConj_rank_step.
BlockedRightConj.gammaParent_source identifies the actual right2 source, with
its leading conjunction principal fixed. gamma_equation proves the arbitrary-tag
comparison. Both original child calls inherit full Clean and strict original
rank through the actual contraction and native conjunction child before
adapters, with unchanged opposite h/z. The completed cut-free reconstruction is
atomized. The two-copy right-contraction arrow equation uses the already proved
principal disjunction equation, followed by the two existing conjunction cores;
no induction call on an artificial disjunction is introduced. Both duplicated
fixed contexts and the equal-labelled fixed principal are compared explicitly.

Appendix C p.260 remains proved by BlockedLeftDisj.gamma_equation,
gamma_first_descent and gamma_second_descent: C and its degree are unchanged,
and both original recursive ranks strictly decrease. Its p.262 sequential
fresh-right-principal correspondence remains open. Older current prose that
still called both rows open is corrected; superseded progress text is historical.
All nine manuscript blobs, including v7 and Appendix C, match the base; unchanged
TeX is not rebuilt. Preserve all earlier results, corrections, stash and receipts.

See [the report](GENTZEN_RIGHT_GAMMA_CONJ_REPORT.md),
[hostile review](reviews/GENTZEN_RIGHT_GAMMA_CONJ_HOSTILE.md),
[writing review](reviews/GENTZEN_RIGHT_GAMMA_CONJ_WRITING.md) and
[constructor/tag table](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Current evidence: provenance/wsl-gentzen-right-gamma-conj/. Nineteen new modules
contain 65 source declarations. Strict verification covers 698 Lean files and
12,737 project declarations; twenty public files and twenty-two expected
control rejections pass. Exact exits, checked/committed source hashes and
Downloads paths are retained in FINAL_VERIFICATION.json and DELIVERY_REGISTER.json.
Prior left-gammaDisj proof/metadata/receipt commits: 17b25c6 / fab64c2 / 2f66237.
All earlier evidence and committed-byte deliveries persist.

Next complete BlockedL.conjunction and BlockedR.disjunction, then the First,
Second and Both logical families on each side. Preserve actual two/three-copy
arities, route components below fresh native principals and prove the selected
leaf, one-sided rank one and full Clean before each sequential cut. Compare
with the original contracted rank, without a returned-proof rank assumption.
Then discharge constructor dispatch, fixed-degree all-ranks Clean under strict
DegreeBelow, simultaneous cleaning, strong degree induction and arbitrary-G
normalization. Export unrestricted CutElimination and AtomizedCutElimination
inhabitants; continue coherence, intended-presentation and uniform-substitution/
congruence bridges, both maximality routes, model corollary and every claim in
all three v7 appendices. The three milestones and complete-paper endpoint remain
distinct. Independent replay, Comparator, official/service verification and
publication remain separate unperformed statuses. Deliver committed-byte
reports and changed records with conflict-preserving verified Downloads copies.
Continue the full-paper contract without another routine approval checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current five blocked reductions');b=s.index('## ',a+3);block=active
 if rel=='README.md':block=block.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 s=s.replace('The manuscript addition is complete; its concrete blocked-reduction Lean\ncorrespondence remains open. Selected-cut positivity and native fresh-principal rank-one laws now compile;\nthe concrete blocked reductions remain open.', "The manuscript addition is complete. Appendix C p.260 has its actual source\nequation and both strict original-child rank inequalities. Its p.262 sequential\nfresh-right-principal correspondence remains open. Selected-cut positivity and\nnative fresh-principal rank-one laws compile.")
 p.write_text(s)
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text().replace('the nine remaining source-shaped blocked reductions. BlockedL.gammaMix,\nBlockedR.gammaMix, BlockedL.gammaConj, BlockedR.gammaDisj and BlockedL.gammaDisj\nhave actual source/rank steps.', 'the eight remaining sequential logical blocked reductions. All six gamma\nfamilies on BlockedL and BlockedR have actual source equations and rank steps.').replace('remaining four BlockedL and five BlockedR','remaining four BlockedL and four BlockedR').replace('The exact v7 Appendix C addition is complete. Its two concrete blocked-rank\nLean correspondences remain open.', 'The exact v7 Appendix C addition is complete. Its p.260 concrete source/rank\ncorrespondence is proved by the left gammaDisj equation and both original-child\nstrict descents. Its p.262 sequential fresh-right-principal correspondence remains open.');p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('BlockedL.gammaConj, BlockedR.gammaDisj and BlockedL.gammaDisj are complete through', 'BlockedL.gammaConj, BlockedR.gammaDisj, BlockedL.gammaDisj and BlockedR.gammaConj\nare complete through').replace('Complete the nine remaining blocked reductions', 'Complete the eight remaining sequential logical blocked reductions');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region');s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches and all
six gamma blocked families are complete on both BlockedL and BlockedR. Each has
an actual source equation, exact reconstruction, eliminated witness and
instantiated original-rank step. Eight sequential logical blocked reductions
and global induction remain open. Current report: GENTZEN_RIGHT_GAMMA_CONJ_REPORT.md;
continuation: CODEX_NEXT_SESSION.txt. Appendix C p.260 is proved; p.262 remains
open. Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('gammaMix/gammaDisj complete; five BlockedR reductions pending', 'all three gamma families complete; four sequential BlockedR reductions pending').replace('gammaMix/gammaConj/gammaDisj complete; four BlockedL reductions pending', 'all three gamma families complete; four sequential BlockedL reductions pending').replace('The five completed blocked families','The six completed blocked families').replace('| gammaConj | Actual source equation/reconstruction; blockedL_gammaConj_eliminated/rank_step | Pending actual cut reduction |','| gammaConj | Actual source equation/reconstruction; blockedL_gammaConj_eliminated/rank_step | Actual source equation/reconstruction; blockedR_gammaConj_eliminated/rank_step |').replace('adapters are proved for the five completed entries; the nine other entries','adapters are proved for all six gamma entries; the eight logical entries')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Six gamma reductions and reconciled current prose (29 October 2026)

BlockedR.gammaConj now has its actual right2 source identity, arbitrary-tag
Reduced equation, exact reconstruction, full original Clean/strict descent and
CutCommutation.blockedR_gammaConj_rank_step. All six gamma families are complete;
eight sequential logical blocked cases remain. The leading conjunction principal
stays fixed even when its formula equals C, as checked by exact indices and a
rejected false identification. The existing p.260 source/rank correspondence is
preserved; p.262 remains open. Two older current prose passages still described
both concrete Appendix C rows as open. Those live passages are corrected, and
superseded checkpoint prose is labeled historical. No new manuscript erratum
was established; all nine manuscript blobs, corrections and deliveries persist.
Current report/reviews: GENTZEN_RIGHT_GAMMA_CONJ_REPORT.md and linked records.
'''+s[a:]
s=s.replace('and its two reviews. The two concrete blocked-reduction Lean correspondences\nremain open, as recorded in the v7 statement ledger.', 'and its two reviews. The p.260 concrete source/rank correspondence is proved;\nthe p.262 sequential fresh-right-principal correspondence remains open, as\nrecorded in the v7 statement ledger.')
s=s.replace('## Current correction status', '## Historical correction checkpoints (superseded by current scope above)')
p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_2F66237.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('AFTER FIVE BLOCKED REDUCTIONS: NINE BLOCKED CASES REMAIN', 'AFTER SIX GAMMA REDUCTIONS: EIGHT LOGICAL BLOCKED CASES REMAIN')
s=s.replace('Read GENTZEN_LEFT_GAMMA_DISJ_REPORT.md', 'Read GENTZEN_RIGHT_GAMMA_CONJ_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_LEFT_GAMMA_DISJ_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_ECFE8DA.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_2F66237.txt, archived verbatim.\nThe ECFE8DA continuation remains preserved.')
s=s.replace('The five actual source reductions are complete:', 'All six gamma source reductions are complete:')
s=s.replace(' BlockedL.gammaDisj: BlockedLeftDisj.gamma_equation; blockedL_gammaDisj_rank_step.', ' BlockedL.gammaDisj: BlockedLeftDisj.gamma_equation; blockedL_gammaDisj_rank_step.\n BlockedR.gammaConj: BlockedRightConj.gamma_equation; blockedR_gammaConj_rank_step.')
s=s.replace('five reductions and their exact tag/fold correspondence.', 'six reductions and their exact tag/fold correspondence.')
s=s.replace('p.262 remains open. Next is BlockedR.gammaConj.', 'p.262 remains open. Right gammaConj uses the completed principal disjunction\narrow equation and both existing conjunction cores. Actual output naturality,\nfixed principal, source and child comparisons are proved. Next are the eight\nsequential logical blocked cases, beginning with BlockedL.conjunction.')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 698 screened Lean files, 12,737 audited declarations,
twenty public files and twenty-two expected rejections; nineteen new production
modules and 65 source declarations. Exact totals/exits and committed-byte
source evidence: provenance/wsl-gentzen-right-gamma-conj/. Earlier phase evidence
persists. Reviews are local author-side reviews; independent replay, Comparator
and official/service verification were not performed.
'''+s[b:]
s=s.replace('remaining nine source-shaped blocked reductions:', 'remaining eight sequential logical blocked reductions:').replace(' BlockedR: gammaConj, disjunction,', ' BlockedR: disjunction,').replace('Both gammaMix, both gammaDisj and left gammaConj families are complete; reuse them.', 'All three gamma families on both sides are complete; reuse them.')
s=s.replace('twenty-one controls.', 'twenty-two controls.')
s=s.replace('at 1d09a27 / ecfe8da.', 'at 1d09a27 / ecfe8da and seventeen-entry left-gammaDisj register at\n17b25c6 / fab64c2 / 2f66237.')
p.write_text(s)
print('Updated six-gamma scope and current Appendix C prose; archived prior continuation')
