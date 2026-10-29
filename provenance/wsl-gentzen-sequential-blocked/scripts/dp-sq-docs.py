for src,dst in [('report','GENTZEN_BLOCKED_CONJUNCTION_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_CONJUNCTION_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_CONJUNCTION_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-sq-'+src+'.md').read_bytes())
active='''## Current seven blocked reductions (29 October 2026)

All twelve binary branches, all six gamma blocked families and
BlockedL.conjunction have actual source equations and instantiated original-rank
steps. Seven sequential logical blocked families and global induction remain
open. Successor 811eceeb and all preceding results/corrections are preserved.

BlockedConjunction.parent_source identifies the exact left2/conjLLast source.
source_equation proves the selected cut equal to a concrete routed two-cut
construction. original_descent gives the original child full Clean and strict
original rank, with unchanged h/z. The first ih occurs before component routing.
fresh_clean_and_rank proves the literal rebuilt G.conjL principal is a blocked
leaf with one-sided rank one and total h.rho+1 below the original contracted
rank. The second ih needs no returned-proof rank bound. Existing structural
replacement adapts the first result; duplicate input/output repair and final
atomization give the exact-output cut-free Atomized representative.

Appendix C p.260 remains closed by the actual left gammaDisj source equation
and both original-child descents. Its p.262 sequential disjunction correspondence
remains open; conjunction does not close that different source case. All nine
manuscript blobs and all earlier receipts persist; unchanged TeX is not rebuilt.

See [report](GENTZEN_BLOCKED_CONJUNCTION_REPORT.md),
[hostile review](reviews/GENTZEN_BLOCKED_CONJUNCTION_HOSTILE.md),
[writing review](reviews/GENTZEN_BLOCKED_CONJUNCTION_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Current evidence: provenance/wsl-gentzen-sequential-blocked/. Fourteen new
production modules contain 54 source declarations; 713 Lean files are screened.
Twenty-one public files and 26 expected rejections are checked. Exact audit
totals/exits, checked/committed bytes and Downloads paths are in
FINAL_VERIFICATION.json and DELIVERY_REGISTER.json. Four actual terminal-output
smoke witnesses are distinguished from the general equation/rank proof; no
unrestricted ih is pretended to exist. Reviews are local author-side reviews.
Independent replay, Comparator, official/service verification and publication
remain separate unperformed statuses.

Next complete BlockedR.disjunction, then BlockedL.disjunctionFirst/Second/Both
and BlockedR.conjunctionFirst/Second/Both. Preserve two/three-copy arities,
original Clean/ranks before adapters, components below fresh native principals
and final structural atomization. Discharge constructor/tag dispatch, fixed-degree
all-ranks Clean under strict DegreeBelow, arbitrary-premise cleaning, strong
degree induction and arbitrary-G normalization. Export unrestricted
CutElimination/AtomizedCutElimination inhabitants, then continue coherence,
intended-presentation and uniform-substitution/congruence bridges, both
maximality routes, model corollary and all claims in all three v7 appendices.
The three milestones and full-paper endpoint remain distinct. Deliver changed
reports/records from committed bytes with verified conflict-preserving copies.
Continue under existing authorization without a routine approval checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current six gamma blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 if rel=='docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md':
  s=s.replace('the eight remaining sequential logical blocked reductions. All six gamma\nfamilies on BlockedL and BlockedR have actual source equations and rank steps.', 'the seven remaining sequential logical blocked reductions. All six gamma\nfamilies and BlockedL.conjunction have actual source equations and rank steps.').replace('remaining four BlockedL and four BlockedR','remaining three BlockedL and four BlockedR')
 p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('Complete the eight remaining sequential logical blocked reductions', 'BlockedL.conjunction also has its actual sequential source equation and original-rank\nstep. Complete the seven remaining sequential logical blocked reductions');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches, all six
gamma blocked families and BlockedL.conjunction are complete. Each has an actual
source equation and instantiated original-rank step. Seven blocked families and
global induction remain open. Current report: GENTZEN_BLOCKED_CONJUNCTION_REPORT.md;
continuation: CODEX_NEXT_SESSION.txt. Appendix C p.260 is proved; p.262 remains
open. Measure original selected rank before adapters.

'''+s[b:]
s=s.replace('all three gamma families complete; four sequential BlockedL reductions pending','all three gamma families and conjunction complete; three sequential BlockedL reductions pending').replace('The six completed blocked families','The seven completed blocked families').replace('| conjunction / disjunction | Pending sequential actual cut reduction | Pending sequential actual cut reduction |','| conjunction / disjunction | Actual source_equation, reconstruction and blockedL_conjunction_rank_step | Pending sequential actual cut reduction |').replace('adapters are proved for all six gamma entries; the eight logical entries\nremain open.', 'adapters are proved for all six gamma entries and BlockedL.conjunction; the\nseven other logical entries remain open.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Sequential conjunction completed (29 October 2026)

BlockedL.conjunction now has its exact left2/conjLLast source, arbitrary-tag
Reduced two-cut equation, concrete exact-output repair and instantiated
original-rank step. The second cut is on a literal native G.conjL principal,
with component exchanges below it; full Clean and rank one are proved without
any returned-proof rank bound. Seven blocked families are complete and seven
remain open. Appendix C p.260 stays proved and p.262 stays open because it
concerns sequential disjunction. No new manuscript defect was established.
All nine manuscript blobs, preceding corrections, stash and deliveries persist.
See GENTZEN_BLOCKED_CONJUNCTION_REPORT.md and its two local reviews.
'''+s[a:];s=s.replace('## Six gamma reductions and reconciled current prose', '## Historical six-gamma checkpoint and reconciled prose');p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_787EE6C.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER SIX GAMMA REDUCTIONS: EIGHT LOGICAL BLOCKED CASES REMAIN','CONTINUE V7 AFTER SEQUENTIAL CONJUNCTION: SEVEN BLOCKED CASES REMAIN')
s=s.replace('Read GENTZEN_RIGHT_GAMMA_CONJ_REPORT.md', 'Read GENTZEN_BLOCKED_CONJUNCTION_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_RIGHT_GAMMA_CONJ_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_2F66237.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_787EE6C.txt, archived verbatim.\nThe 2F66237 continuation remains preserved.')
s=s.replace('Next are the eight\nsequential logical blocked cases, beginning with BlockedL.conjunction.', '''BlockedL.conjunction is also complete: BlockedConjunction.parent_source,
source_equation, original_descent, fresh_clean_and_rank and
CutCommutation.blockedL_conjunction_rank_step. The first ih uses the original
child before routing; the second uses unchanged h/z and a literal native G.conjL
principal, proved full Clean with h.rho+1 below the original contracted rank.
No rank bound on the returned proof is used. Exact duplicate repair and final
atomization preserve the original result sequent. Seven logical blocked cases
remain, beginning with BlockedR.disjunction.''')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: 713 screened Lean files, twenty-one public files and
26 expected rejections; fourteen new production modules and 54 source
declarations. Exact audited declaration totals/exits and committed-byte source
evidence: provenance/wsl-gentzen-sequential-blocked/. Actual terminal-output
witnesses are smoke checks, distinguished from the general source/rank proof.
Earlier evidence persists. Reviews are local author-side reviews; independent
replay, Comparator and official/service verification were not performed.
'''+s[b:]
s=s.replace('remaining eight sequential logical blocked reductions:', 'remaining seven sequential logical blocked reductions:').replace(' BlockedL: conjunction, disjunctionFirst,', ' BlockedL: disjunctionFirst,').replace('All three gamma families on both sides are complete; reuse them.', 'All three gamma families on both sides and BlockedL.conjunction are complete; reuse them.').replace('twenty-two controls.', '26 controls.')
s=s.replace('17b25c6 / fab64c2 / 2f66237.', '17b25c6 / fab64c2 / 2f66237, and the right-gammaConj proof/receipt 5278d5e /\n787ee6c.')
p.write_text(s)
print('Updated current seven-family scope; preserved Appendix C p.262 open and archived the preceding continuation')
