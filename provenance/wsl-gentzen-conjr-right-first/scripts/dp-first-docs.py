for src,dst in [('report','GENTZEN_CONJR_RIGHT_FIRST_REPORT.md'),('hostile','reviews/GENTZEN_CONJR_RIGHT_FIRST_HOSTILE.md'),('writing','reviews/GENTZEN_CONJR_RIGHT_FIRST_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-first-'+src+'.md').read_bytes())
active='''## Current conjunction-right first-child construction (28 October 2026)

Successor 811eceebf9991640cf9dcd3923925f75235d4199 is incorporated, preserving
all completed results and stash dedfd8fc8cd49930e9a162d5be585215b062a43c.
conjR_right_first now joins the four mix branches and conjR_right_second as a
completed binary branch through actual native/selected equations, exact-output
reconstruction, eliminated witness and instantiated original-rank step.

BinaryLogical.product_left_splice and mixed_first_residual prove both successor
comparison targets. Their combined core and all actual input/output exchange,
fold/unit, headBefore/suffix and erasure comparisons are instantiated in
conjFirstNative_equation and conjRRightFirst_equation. The generic builder is
conjRRightFirst, with count/Atomized/congruence laws. The rank step calls
ih h z f a on the original inherited clean child before reconstruction.
The public check reproduces the exact retained native candidate. No diagram
field, general proof duality or occurrence-graph reflection is assumed.

See [the run report](GENTZEN_CONJR_RIGHT_FIRST_REPORT.md),
[hostile audit](reviews/GENTZEN_CONJR_RIGHT_FIRST_HOSTILE.md),
[writing review](reviews/GENTZEN_CONJR_RIGHT_FIRST_WRITING.md),
[the successor](CODEX_AFTER_77199AC_LOGICAL_BINARY_CUTS.txt) and
[live constructor/tag table](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
The preceding mix/logical reports and all accepted mathematical/writing decisions
retain their original scope. The former native first-child open equation is resolved.

| Local proof phase | Lean files | Audited declarations | Public check files | Rejected controls | Evidence directory |
| --- | ---: | ---: | ---: | ---: | --- |
| a654ed0; four mix branches; receipt 408257b | 538 | 11,886 | 11 | 8 | provenance/wsl-gentzen-binary-cuts/ |
| 9af0a8a; right-second conjunction and symmetry; receipt 77199ac | 546 | 11,911 | 12 | 9 | provenance/wsl-gentzen-logical-binary-cuts/ |
| Right-first conjunction, both comparison targets and exact native/selected branch | 555 | 11,967 | 13 | 10 | provenance/wsl-gentzen-conjr-right-first/ |

Strict build/transitive audit, public signatures and actual nonempty/empty/tag/
literal witnesses, source closure and ten negative rejections pass locally.
Reviews are local author-side reviews. No independent replay, Comparator,
official/service verification or publication is claimed. All manuscript bytes
match 811eceeb; unchanged TeX is not rebuilt.

Work continued into conjR_left_first. Its precise typed parametric-output core
and failed distribution expansion are retained in current evidence under
open/next-conjr-left-first.lean. That equation remains unproved; it is neither a
counterexample nor the now-resolved native right-first equation. Six logical
binary branches, all fourteen blocked reductions, the dispatcher, discharged
rank/degree/structural inductions and both unrestricted elimination inhabitants
remain open. Coherence and later full-paper bridges, both maximality routes,
model corollary and all three appendices remain in scope. Appendix C is written;
its two concrete blocked-rank Lean correspondences remain open. The three
milestones and additional whole-paper endpoint remain distinct.

All prior completed deliveries, including the 19-entry mix and 16-entry logical
registers, remain complete. The three 77199AC successor files are now delivered
from 811eceeb bytes and verified; current SUCCESSOR_DELIVERY.json records them.
This phase's finalized reports/reviews and changed records use its own
committed-byte DELIVERY_REGISTER.json. The prior continuation is archived verbatim
at history/CODEX_NEXT_SESSION_811ECEE.txt; historical sections below do not reset
current proof status or completed deliveries.

'''
for rel in ['MANUSCRIPT_STATEMENTS.md','MANUSCRIPT_COVERAGE.md','VALIDATION.md','CODEX_FULL_MANUSCRIPT_FORMALIZATION.md']:
 p=root/'docs'/rel;s=p.read_text();start=s.index('## Current continuation after 77199ac');end=s.index('## ',start+3);p.write_text(s[:start]+active+s[end:])
p=root/'README.md';s=p.read_text();start=s.index('## Current continuation after 77199ac');end=s.index('## Current manuscript',start);p.write_text(s[:start]+active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/').replace('](CODEX_','](docs/CODEX_')+s[end:])
p=root/'AGENTS.md';s=p.read_text();s=s.replace('governs the immediate continuation after 77199ac.','governs the immediate continuation after 811eceeb integration.')
s=s.replace('read its two 77199AC reviews. Complete conjR_right_first, then the other six\nlogical binary branches, blocked reductions and global induction. Reuse all\nfour mix branches, conjR_right_second, mixedDisj_swap and the completed unary/\ndescent results.', 'read its two 77199AC reviews. conjR_right_first is now proved through its\nretained native/selected equations and instantiated rank step. Complete the six\nremaining logical binary branches, blocked reductions and global induction.\nReuse all four mix branches, both right-side conjR branches, mixedDisj_swap\nand the completed unary/descent results.');p.write_text(s)
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text().replace('Start with the exact retained conjR_right_first equation, using the\nsuccessor\'s two typed comparison targets and existing proved dependencies.','Both comparison targets and the retained conjR_right_first equation,\narbitrary-tag reconstruction and rank step are now proved. Continue from\nconjR_left_first and the exact open parametric-output core in current evidence.')
s=s.replace('mix branches and conjR_right_second have actual equations, reconstructions and\nrank steps; seven logical binary branches remain open.','mix branches and both right-side conjR branches have actual equations,\nreconstructions and rank steps; six logical binary branches remain open.')
s=s.replace('Complete the seven remaining\nlogical binary branches', 'Complete the six remaining\nlogical binary branches');p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_811ECEE.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER 77199AC: SEVEN LOGICAL BINARY BRANCHES','CONTINUE V7 AFTER CONJR RIGHT-FIRST: SIX LOGICAL BINARY BRANCHES')
s=s.replace('The prior continuation is archived verbatim at history/CODEX_NEXT_SESSION_77199AC.txt.','The prior continuation is archived verbatim at history/CODEX_NEXT_SESSION_811ECEE.txt;\nthe 77199AC and older archives remain preserved. Read the current right-first\nrun report and both reviews, then reuse the preceding mix/logical reports.')
s=s.replace('Reviewed main: 77199ac58fcacfeefb80457a5d91f85c0a59fbab, incorporating b767c19.','Reviewed predecessor: 77199ac58fcacfeefb80457a5d91f85c0a59fbab.\nSuccessor 811eceebf9991640cf9dcd3923925f75235d4199 is integrated, preserving it.')
s=s.replace('Current local evidence: 546 screened Lean files, 11,911 audited declarations,\ntwelve public check files and nine expected negative rejections.', 'Current local evidence: 555 screened Lean files, 11,967 audited declarations,\nthirteen public check files and ten expected negative rejections.\nBoth right-side conjR branches are proved through actual native/selected\nequations, exact-output reconstruction, eliminated witnesses and rank steps.\nCurrent evidence: provenance/wsl-gentzen-conjr-right-first/. The preceding\n546/11,911/twelve/nine phase is retained below with its source-review scope.')
start=s.index('1. Complete conjR_right_first.');end=s.index('2. Complete conjR_left_first',start)
s=s[:start]+'''1. Reuse the completed conjR_right_first branch. See GENTZEN_CONJR_RIGHT_FIRST_REPORT.md,
both reviews and current evidence. product_left_splice and mixed_first_residual
prove the successor's two targets. conjFirstNative_equation proves the retained
native candidate, and conjRRightFirst_equation lifts it to arbitrary original
tags. Count/Atomized/congruence and eliminated/rank_step are instantiated.
The exact call is ih h z f a hd.2 hd.1 before any exchanges. The old retained
native equation is resolved; do not repeat it as the remaining blocker.
'''+s[end:]
s=s.replace('The prior seven retained-tag recipes and original-child descents remain binding.','The remaining retained-tag recipes and original-child descents remain binding.\nThe immediate open diagram is current evidence open/next-conjr-left-first.lean:\nf : X -> A∨(C∨D), g : Y -> B∨E, h : C∧T -> Z. Both paths have type\nT∧(X∧Y) -> Z∨((A∧B)∨(D∨E)); the first cuts the selected C in the mixed-rule\noutput, the second cuts the original first child, retains A and reconstructs.\nActual distribution expansion leaves an unproved equation outside production.\nProve it, specialize all native folds/adapters and lift to selected tags,\neliminated and rank_step before marking that branch complete.')
s=s.replace('all nine existing controls','all ten existing controls').replace('all nine controls','all ten controls')
s=s.replace('Only the three new 77199AC instruction/review files remain pending\nuntil local committed-byte delivery and verification.', 'The three new 77199AC instruction/review files are delivered from 811eceeb\ncommitted bytes and verified in current SUCCESSOR_DELIVERY.json. Deliver current\nreports/reviews and changed records from committed bytes using the current\nDELIVERY_REGISTER.json; preserve differing existing files.')
s=s.replace('Deliver the three new 77199AC successor files and every new local report/review\nfrom committed bytes; record paths, lengths and SHA-256 comparisons.', 'The three new 77199AC successor files are delivered from 811eceeb bytes,\nwith exact paths/hashes in current SUCCESSOR_DELIVERY.json. Deliver every new\nlocal report/review from committed bytes; record paths, lengths and hashes.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();s=s.replace('## Current correction status\n\n','''## Current correction status

conjR_right_first is now proved through both supplied comparison targets,
the exact retained native equation, arbitrary-tag reconstruction and original-rank
step. Six logical binary and fourteen blocked reductions remain open. The next
parametric-output equation is retained separately in current evidence. No new
manuscript error was established. The earlier open right-first record below is
historical and superseded by GENTZEN_CONJR_RIGHT_FIRST_REPORT.md. The three
811eceeb successor deliveries are complete in current SUCCESSOR_DELIVERY.json.
All earlier source/rank/atomization, writing and full-paper decisions persist.

''',1)
s=s.replace('The exact remaining native equation is unproved; the failed simplification is\nnot a counterexample.', 'At that reviewed predecessor the exact native equation was unproved; its\nfailed simplification was not a counterexample. The current result above resolves it.')
s=s.replace('The actual conjR_right_second equation/reconstruction and original-rank step\nare now proved; seven logical binary and fourteen blocked reductions remain\nopen.', 'At the retained 9af0a8a checkpoint, conjR_right_second was proved and seven\nlogical binary branches remained open. The current right-first result supersedes\nthat open count; its exact current status is recorded above.')
p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();start=s.index('Current checkpoint:');end=s.index('| Root and selected region',start)
s=s[:start]+'''Current construction incorporates successor 811eceeb. Four mix branches and both
right-side conjR branches have exact equations, reconstructions, eliminated
witnesses and instantiated original-rank steps. Six logical binary and fourteen
blocked reductions remain open. Global elimination and the full-paper endpoint
remain open. Original selected rank is measured before adapters.

The active successor remains CODEX_AFTER_77199AC_LOGICAL_BINARY_CUTS.txt;
CODEX_NEXT_SESSION.txt records its proved right-first endpoint and continuation
into conjR_left_first. All earlier builders and atomization decisions persist.

'''+s[end:]
s=s.replace('| conjR, first child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Clean/rank descent checked; equation, reconstruction and rank step pending |','| conjR, first child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightFirst/conjRRightFirst_equation; CutCommutation.conjR_right_first_rank_step) |')
s=s.replace('conjR_right_second is now complete; seven logical binary branches remain open.','both right-side conjR branches are now complete; six logical binary branches remain open.')
start=s.index('The right-second conjunction reconstruction');end=s.index('| Blocked constructor family',start)
s=s[:start]+'''Both right-side conjunction reconstructions preserve the retained A/B tag,
cut count and Atomized condition through actual native fold/unit and head-route
comparisons. The former right-first native equation is resolved. Its report and
evidence are GENTZEN_CONJR_RIGHT_FIRST_REPORT.md and
provenance/wsl-gentzen-conjr-right-first/. The preceding right-second/symmetry
phase is GENTZEN_LOGICAL_BINARY_CUTS_REPORT.md and
provenance/wsl-gentzen-logical-binary-cuts/. mixedDisj_swap remains an actual
Reduced equation, not a general G duality. The next left-first parametric-output
diagram is retained in current evidence open/next-conjr-left-first.lean and is
unproved. No blocked family is closed by these commutations.

'''+s[end:];p.write_text(s)
print('Archived the successor continuation and reconciled all active maps with the completed right-first branch')
