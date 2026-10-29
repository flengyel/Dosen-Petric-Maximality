for src,dst in [('report','GENTZEN_BLOCKED_DISJ_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_DISJ_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_DISJ_WRITING.md')]:
 b=Path('/tmp/dp-bd-'+src+'.md').read_bytes().replace(b'\n dedfd',b'\ndedfd');(root/'docs'/dst).write_bytes(b)
active='''## Current four blocked reductions (28 October 2026)

Successor 811eceeb remains incorporated and all twelve binary branches remain
proved. BlockedL.gammaMix, BlockedR.gammaMix, BlockedL.gammaConj and now
BlockedR.gammaDisj have actual source equations, exact-output reconstructions,
eliminated witnesses and instantiated original-rank steps. Ten blocked reductions,
global induction and the full-paper endpoint remain open. The existing stash
and all preceding work and committed-byte deliveries are preserved.

The new declaration is CutCommutation.blockedR_gammaDisj_rank_step. It inherits
full Clean and strict original-child rank through the actual contraction, outer
exchange, native disjL and child exchange before any routing adapter. Both calls
use the unchanged opposite premise. The particular reflected diagram expands to
an actual Reduced equation; singleton units, terminal rotations, equal-labelled
fixed tags and both duplicated-context contractions are proved. The finished
cut-free reconstruction is atomized, preserving exact output and equality.

See [the report](GENTZEN_BLOCKED_DISJ_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_DISJ_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_DISJ_WRITING.md) and
[constructor/tag table](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Earlier three blocked reductions: b95abc6 / f04b638 and
provenance/wsl-gentzen-blocked-cuts/. Current evidence:
provenance/wsl-gentzen-blocked-disj/, thirteen modules and 67 source declarations;
eighteen public files and twenty expected control rejections. Strict counts,
command exits and exact source hashes are in FINAL_VERIFICATION.json.

Continue BlockedL.gammaDisj and BlockedR.gammaConj, then eight sequential logical
blocked cases, preserving all two/three-copy multiplicities and source/native
adapters. Fresh logical principals must have component routes BELOW them and
proved leaf/rank-one/full Clean before the next original-rank call. No returned
proof rank bound is assumed. Appendix C's p.260 left gamma-3 and p.262 fresh-right
Lean correspondences remain open.

Then discharge constructor dispatch, fixed-degree all-ranks Clean under strict
DegreeBelow, arbitrary premise cleaning, strong degree induction and arbitrary-G
normalization; export actual unrestricted CutElimination and
AtomizedCutElimination inhabitants. Continue coherence, intended-presentation and
uniform-substitution/congruence bridges, both maximality routes, model corollary
and every mathematical claim in all three v7 appendices. The three milestones
and the complete-paper endpoint remain distinct. Independent replay, Comparator,
official/service verification and publication are separate unperformed statuses.

All nine manuscript blobs match f04b638; v7, the authorized errata appendix,
older versions and diagrams are unchanged. No new manuscript defect was
established; unchanged TeX is not rebuilt. Carry forward every accepted correction
and verification/delivery obligation. The prior continuation is archived verbatim
in history/CODEX_NEXT_SESSION_F04B638.txt. Deliver new reports and changed records
from committed bytes, preserving differing Downloads files and verifying each
copy. Continue the full-paper contract without a routine approval stop.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current three blocked reductions');b=s.index('## ',a+3)
 block=active
 if rel=='README.md':block=block.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 p.write_text(s[:a]+block+s[b:])
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text().replace('the eleven remaining source-shaped blocked reductions. BlockedL.gammaMix,\nBlockedR.gammaMix and BlockedL.gammaConj have actual source/rank steps.','the ten remaining source-shaped blocked reductions. BlockedL.gammaMix,\nBlockedR.gammaMix, BlockedL.gammaConj and BlockedR.gammaDisj have actual source/rank steps.').replace('remaining five BlockedL and six BlockedR','remaining five BlockedL and five BlockedR');p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('BlockedL.gammaConj are complete through actual source equations and rank steps.\nComplete the eleven remaining blocked reductions','BlockedL.gammaConj and BlockedR.gammaDisj are complete through actual source equations and rank steps.\nComplete the ten remaining blocked reductions');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region');s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches and four
blocked families are complete: BlockedL.gammaMix, BlockedR.gammaMix,
BlockedL.gammaConj and BlockedR.gammaDisj. Each has an actual source equation,
exact reconstruction, eliminated witness and instantiated original-rank step.
Ten blocked reductions and global induction remain open. Current report:
GENTZEN_BLOCKED_DISJ_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('gammaMix complete; six BlockedR reductions pending','gammaMix/gammaDisj complete; five BlockedR reductions pending')
s=s.replace('The three completed blocked families','The four completed blocked families').replace('| gammaDisj | Pending actual cut reduction | Pending actual cut reduction |','| gammaDisj | Pending actual cut reduction | Actual source equation/reconstruction; blockedR_gammaDisj_eliminated/rank_step |').replace('adapters are proved for the three completed entries; the eleven other entries','adapters are proved for the four completed entries; the ten other entries')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Fourth blocked reduction, 28 October 2026

BlockedR.gammaDisj is proved through its actual disjLLast/right2 source equation,
exact reconstruction and original-rank step. Preserve the established reversed
parameter order: the first source child uses gammaSecondRoute. Terminal singleton
units, all three exchanges and both fixed-context contractions are explicit.
Clean/rank descents pass through the actual contraction and original macro
children before adapters. The native source macro is not assigned rank one.
The new constant-only public witness explicitly supplies empty context splits.
Ten blocked reductions and global induction remain open; the two Appendix C Lean
rows are unchanged. No new manuscript defect was established. Current report and
local reviews: GENTZEN_BLOCKED_DISJ_REPORT.md and linked records. All earlier
corrections and delivery receipts remain effective.
'''+s[a:];p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();h=root/'docs/history/CODEX_NEXT_SESSION_F04B638.txt';assert not h.exists() or h.read_bytes()==old
if not h.exists():h.write_bytes(old)
s=old.decode().replace('AFTER THREE BLOCKED REDUCTIONS: ELEVEN BLOCKED CASES REMAIN','AFTER FOUR BLOCKED REDUCTIONS: TEN BLOCKED CASES REMAIN')
s=s.replace('Read GENTZEN_BLOCKED_GAMMA_REPORT.md and its hostile/writing reviews, reusing','Read GENTZEN_BLOCKED_DISJ_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_GAMMA_REPORT.md and its reviews, plus')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_26E6D8D.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_F04B638.txt, archived verbatim.\nThe 26E6D8D continuation remains preserved.')
s=s.replace('The three actual source reductions are complete:', 'The four actual source reductions are complete:')
s=s.replace(' BlockedL.gammaConj: BlockedConj.gamma_equation; blockedL_gammaConj_rank_step.', ' BlockedL.gammaConj: BlockedConj.gamma_equation; blockedL_gammaConj_rank_step.\n BlockedR.gammaDisj: BlockedDisj.gamma_equation; blockedR_gammaDisj_rank_step.')
s=s.replace('three reductions and their exact tag/fold correspondence. Next is\nBlockedL.gammaDisj; do not reopen the three completed constructions.', 'four reductions and their exact tag/fold correspondence. The new right gammaDisj\nuses TerminalFold coordinates and the particular MirrorCalculus lifted-pair\ncalculation, then all three original source exchange/constructor predecessors.\nNext are BlockedL.gammaDisj and BlockedR.gammaConj; reuse all four completed cases.')
s=s.replace('Current local evidence: 631 screened Lean files, 12,384 audited declarations,\nseventeen public files and seventeen expected rejections; twenty new production\nmodules and 103 source declarations. Evidence: provenance/wsl-gentzen-blocked-cuts/. Earlier', 'Current local evidence: strict source/dependency audit and eighteen public files,\ntwenty expected rejections; thirteen new production modules and 67 source\ndeclarations. Exact totals: provenance/wsl-gentzen-blocked-disj/FINAL_VERIFICATION.json. Earlier')
s=s.replace('remaining eleven source-shaped blocked reductions:', 'remaining ten source-shaped blocked reductions:').replace(' BlockedR: gammaDisj, gammaConj, disjunction, conjunctionFirst, conjunctionSecond, conjunctionBoth.', ' BlockedR: gammaConj, disjunction, conjunctionFirst, conjunctionSecond, conjunctionBoth.').replace('The two gammaMix and left gammaConj families are complete; reuse them.', 'The two gammaMix, left gammaConj and right gammaDisj families are complete; reuse them.')
s=s.replace('seventeen controls.', 'twenty controls.')
s=s.replace('disjL register at cf3741a / 26e6d8d.', 'disjL register at cf3741a / 26e6d8d and the seventeen-entry three-blocked\nregister at b95abc6 / f04b638.')
p.write_text(s)
print('Updated active four-family scope, three reviews/reports, and preserved prior continuation')
