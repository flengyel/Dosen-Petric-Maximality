for src,dst in [('report','GENTZEN_LEFT_GAMMA_DISJ_REPORT.md'),('hostile','reviews/GENTZEN_LEFT_GAMMA_DISJ_HOSTILE.md'),('writing','reviews/GENTZEN_LEFT_GAMMA_DISJ_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-lg-'+src+'.md').read_bytes())
active='''## Current five blocked reductions (29 October 2026)

Successor 811eceeb remains incorporated. All twelve binary branches and five
blocked reductions are proved: BlockedL.gammaMix/gammaConj/gammaDisj and
BlockedR.gammaMix/gammaDisj. Each has an actual source equation, exact-output
reconstruction, eliminated witness and instantiated original-rank step. Nine
blocked reductions and global induction remain open. Preserve all earlier work,
the stash and prior committed-byte delivery receipts.

The new final declaration is CutCommutation.blockedL_gammaDisj_rank_step.
BlockedLeftDisj.gammaParent_source identifies the actual left2 source after its
list cast; gamma_equation proves its arbitrary-tag equation. Both original child
calls inherit full Clean and strict original-rank decrease through the contraction
and all three macro predecessors before adapters. The completed cut-free
reconstruction is atomized. The native equation uses the proved principal
conjunction equation as an arrow calculation, then the two existing disjL cores;
it introduces no recursive call on an artificial conjunction.

Appendix C's p.260 (w gamma 3) correspondence is now proved by
BlockedLeftDisj.gamma_first_descent/gamma_second_descent together with the source
equation. The formula C and its degree are unchanged, and each new rank is
strictly smaller. The p.262 sequential fresh-right-principal correspondence
remains open. V7 and all nine manuscript blobs are unchanged; no TeX rebuild
was needed.

See [the report](GENTZEN_LEFT_GAMMA_DISJ_REPORT.md),
[hostile review](reviews/GENTZEN_LEFT_GAMMA_DISJ_HOSTILE.md),
[writing review](reviews/GENTZEN_LEFT_GAMMA_DISJ_WRITING.md) and
[constructor/tag table](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Current evidence: provenance/wsl-gentzen-left-gamma-disj/. It retains 32 new
modules and 131 source declarations, 678 screened Lean files, 12,654 audited
project declarations, nineteen public check files and twenty-one expected
control rejections. Exact exits, source/archive hashes and delivery paths are
in FINAL_VERIFICATION.json and DELIVERY_REGISTER.json. Earlier four-family
proof/receipt commits are 1d09a27 / ecfe8da; all older evidence persists.

Next complete BlockedR.gammaConj, then eight sequential logical blocked cases,
including their actual two/three-copy arities. Put component routing below each
fresh native principal, and prove its selected leaf, one-sided rank one and full
Clean before the sequential call. No returned-proof rank bound is assumed.
Then discharge constructor dispatch, fixed-degree all-ranks Clean under strict
DegreeBelow, simultaneous cleaning, strong degree induction and arbitrary-G
normalization. Export actual unrestricted CutElimination and
AtomizedCutElimination inhabitants. Continue coherence, intended-presentation
and uniform-substitution/congruence bridges, both maximality routes, the model
corollary and every mathematical claim in all three v7 appendices. The three
milestones and complete-paper endpoint remain distinct. Independent replay,
Comparator, official/service verification and publication remain separate
unperformed statuses. Deliver committed-byte reports and changed records,
preserving differing Downloads files and verifying each copy. Continue the
full-paper contract without a routine approval stop.

'''
records=['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']
for rel in records:
 p=root/rel;s=p.read_text();a=s.index('## Current four blocked reductions');b=s.index('## ',a+3)
 block=active
 if rel=='README.md':block=block.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 s=s.replace('Selected address/predecessor cleanliness and strict rank laws compile; requires the actual gammaDisj blocked cut reduction with adapters. | Rendered source correction and general rank facts verified; concrete reduction proof open.', 'BlockedLeftDisj.gammaParent_source, gamma_equation, gamma_first_descent, gamma_second_descent and CutCommutation.blockedL_gammaDisj_rank_step. | Compiled actual source reduction, full inherited Clean and both strict original-rank inequalities; C and its degree are unchanged.')
 p.write_text(s)
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text().replace('the ten remaining source-shaped blocked reductions. BlockedL.gammaMix,\nBlockedR.gammaMix, BlockedL.gammaConj and BlockedR.gammaDisj have actual source/rank steps.', 'the nine remaining source-shaped blocked reductions. BlockedL.gammaMix,\nBlockedR.gammaMix, BlockedL.gammaConj, BlockedR.gammaDisj and BlockedL.gammaDisj\nhave actual source/rank steps.').replace('remaining five BlockedL and five BlockedR','remaining four BlockedL and five BlockedR');p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('BlockedL.gammaConj and BlockedR.gammaDisj are complete through actual source equations and rank steps.\nComplete the ten remaining blocked reductions', 'BlockedL.gammaConj, BlockedR.gammaDisj and BlockedL.gammaDisj are complete through\nactual source equations and rank steps. Appendix C p.260 is matched by both\noriginal-child strict inequalities and the actual gammaDisj source equation.\nComplete the nine remaining blocked reductions');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region');s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches and five
blocked families are complete: BlockedL.gammaMix/gammaConj/gammaDisj and
BlockedR.gammaMix/gammaDisj. Each has an actual source equation, exact
reconstruction, eliminated witness and instantiated original-rank step.
Nine blocked reductions and global induction remain open. Current report:
GENTZEN_LEFT_GAMMA_DISJ_REPORT.md; continuation: CODEX_NEXT_SESSION.txt.
Appendix C p.260 is matched by both actual gamma-3 source rank descents;
p.262 remains open. Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('gammaMix/gammaConj complete; five BlockedL reductions pending','gammaMix/gammaConj/gammaDisj complete; four BlockedL reductions pending').replace('The four completed blocked families','The five completed blocked families').replace('| gammaDisj | Pending actual cut reduction |','| gammaDisj | Actual source equation/reconstruction; blockedL_gammaDisj_eliminated/rank_step |').replace('adapters are proved for the four completed entries; the ten other entries','adapters are proved for the five completed entries; the nine other entries')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Fifth blocked reduction and concrete p.260 correction (29 October 2026)

BlockedL.gammaDisj is proved through BlockedLeftDisj.gammaParent_source,
gamma_equation, gamma_first_descent, gamma_second_descent and
CutCommutation.blockedL_gammaDisj_rank_step. Both recursive cuts keep C and its
degree and have strictly smaller original rank before adapters, with full Clean
and unchanged opposite h/z. This resolves the concrete Lean correspondence for
Appendix C's p.260 (w gamma 3) inequality r′ < r. The source macro retains its
three inference predecessors. Extending the two-copy contraction keeps the
terminal A∨B fixed, including when it equals C as a formula. Exact-index and
negative controls verify this distinction. The p.262 sequential fresh-right
correspondence and nine blocked reductions remain open. All nine manuscript
blobs, every prior correction and all earlier deliveries are preserved.
Current report/reviews: GENTZEN_LEFT_GAMMA_DISJ_REPORT.md and linked records.
The dated earlier progress sections below describe their historical checkpoints;
the current declaration map supersedes their then-open p.260 status.
'''+s[a:]
s=s.replace('Concrete blocked cut-reduction inequality remains to be proved. Existing strict predecessor-rank lemmas are available.', 'Compiled actual BlockedLeftDisj.gammaParent_source/gamma_equation and gamma_first_descent/gamma_second_descent; both original recursive ranks strictly decrease with C unchanged. blockedL_gammaDisj_rank_step uses those exact facts.')
p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();h=root/'docs/history/CODEX_NEXT_SESSION_ECFE8DA.txt';assert not h.exists() or h.read_bytes()==old
if not h.exists():h.write_bytes(old)
s=old.decode().replace('AFTER FOUR BLOCKED REDUCTIONS: TEN BLOCKED CASES REMAIN','AFTER FIVE BLOCKED REDUCTIONS: NINE BLOCKED CASES REMAIN')
s=s.replace('Read GENTZEN_BLOCKED_DISJ_REPORT.md', 'Read GENTZEN_LEFT_GAMMA_DISJ_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_BLOCKED_DISJ_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_F04B638.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_ECFE8DA.txt, archived verbatim.\nThe F04B638 continuation remains preserved.')
s=s.replace('The four actual source reductions are complete:', 'The five actual source reductions are complete:')
s=s.replace(' BlockedR.gammaDisj: BlockedDisj.gamma_equation; blockedR_gammaDisj_rank_step.', ' BlockedR.gammaDisj: BlockedDisj.gamma_equation; blockedR_gammaDisj_rank_step.\n BlockedL.gammaDisj: BlockedLeftDisj.gamma_equation; blockedL_gammaDisj_rank_step.')
a=s.index('four reductions and their exact tag/fold correspondence.');b=s.index('\n\nReuse full Reducibility',a)
s=s[:a]+'''five reductions and their exact tag/fold correspondence. The left gammaDisj
native equation uses ContractionSplice.binary, the completed principal conjunction
arrow equation and both existing disjL cores, without an artificial-formula ih.
Terminal fold/exchange and actual source/tag/residue comparisons are proved.
Appendix C p.260 is closed by the actual gamma source equation and both strict
original-child gamma descents; p.262 remains open. Next is BlockedR.gammaConj.
'''+s[b:]
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 678 screened Lean files, 12,654 audited declarations,
nineteen public files and twenty-one expected rejections; 32 new production
modules and 131 source declarations. Exact totals/exits and committed-byte
source evidence: provenance/wsl-gentzen-left-gamma-disj/. Earlier phase evidence
persists. Reviews are local author-side reviews; independent replay, Comparator
and official/service verification were not performed.
'''+s[b:]
s=s.replace('remaining ten source-shaped blocked reductions:', 'remaining nine source-shaped blocked reductions:').replace(' BlockedL: gammaDisj, conjunction, disjunctionFirst, disjunctionSecond, disjunctionBoth.', ' BlockedL: conjunction, disjunctionFirst, disjunctionSecond, disjunctionBoth.').replace('The two gammaMix, left gammaConj and right gammaDisj families are complete; reuse them.', 'Both gammaMix, both gammaDisj and left gammaConj families are complete; reuse them.')
s=s.replace("Close Appendix C's p.260 and p.262 Lean rows only after actual blocked instances.", "Preserve Appendix C's completed p.260 source/rank correspondence. Close its\np.262 Lean row only after the actual sequential blocked instance.")
s=s.replace('twenty controls.', 'twenty-one controls.')
s=s.replace('register at b95abc6 / f04b638.', 'register at b95abc6 / f04b638 and the seventeen-entry right-gammaDisj register\nat 1d09a27 / ecfe8da.')
p.write_text(s)
print('Updated five-family scope and all current p.260 correspondence rows; archived prior continuation')
