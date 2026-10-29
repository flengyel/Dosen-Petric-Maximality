for src,dst in [('report','GENTZEN_CUT_ELIMINATION_REPORT.md'),('hostile','reviews/GENTZEN_CUT_ELIMINATION_HOSTILE.md'),('writing','reviews/GENTZEN_CUT_ELIMINATION_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-gi-'+src+'.md').read_bytes())
active='''## Current unrestricted Gentzen cut elimination (29 October 2026)

`cut_elimination : CutElimination P` and
`atomized_cut_elimination : AtomizedCutElimination P` are proved for arbitrary P.
Every G proof has a CutFree representative at its exact original sequent with
Reduced equality; the second result also supplies Atomized. No handler, Clean,
degree or rank hypothesis is supplied by the caller. Coherence and full-paper
maximality remain separate continuing obligations; the three milestones are unchanged.

| Construction | Actual declaration | Scope |
| --- | --- | --- |
| All seven blocked cases on each side | CutCommutation.blocked_right_rank_step / blocked_left_rank_step | Original lower tag, full Clean and strict original-rank recursion; node-free gammaDisj association. |
| Every parametric G constructor on each side | CutCommutation.parametric_right_rank_step / parametric_left_rank_step | Actual original child with unchanged opposite premise before reconstruction. |
| Complete leaf/parametric/lower dispatch | PositionalCut.clean_rank_step | Clean gives root blockedness; two leaves invoke exhaustive rank-two degree step. |
| Fixed-degree all-ranks clean theorem | PositionalCut.clean_elimination | Strong original selected-rank induction under strict DegreeBelow. |
| Arbitrary cut-free premises at that degree | PositionalCut.cutFree_degree_step | Simultaneous cleaning follows completed all-ranks theorem; no cleaned-rank bound. |
| Strong formula-degree induction | head_cut_elimination | No supplied degree hypothesis; smaller degrees allow arbitrary ranks. |
| Arbitrary tagged cut-free premises | PositionalCut.cutFree_elimination | Exact erased output and Reduced equality. |
| Arbitrary proof trees, including nested cuts | G.cut_free_normalization; cut_elimination | Exact original sequent and Reduced equality. |
| Simultaneous final atomization | atomized_cut_elimination | Actual unrestricted CutFree/Atomized representative. |

All twelve binary branches and fourteen blocked reductions are reused unchanged.
Constants have degree one, literals zero; conjunction cuts A-then-B and disjunction
B-then-A. No returned-rank bound, output blockedness or general G duality is assumed.
Both concrete Appendix C source/rank correspondences remain proved. All nine
manuscript blobs, prior results, stash and delivery receipts are preserved.

See [report](GENTZEN_CUT_ELIMINATION_REPORT.md),
[hostile review](reviews/GENTZEN_CUT_ELIMINATION_HOSTILE.md),
[writing review](reviews/GENTZEN_CUT_ELIMINATION_WRITING.md) and
[constructor/tag map](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
Evidence: provenance/wsl-gentzen-global-induction/. Strict pinned verification,
all public checks, actual global witnesses and 44 expected rejections are recorded
with actual counts/exits/hashes in FINAL_VERIFICATION.json. Checked source bytes
are archived and compared with committed bytes. Reviews are local author-side;
independent replay, Comparator, official/service verification and publication
remain separate unperformed statuses. DELIVERY_REGISTER.json records exact
committed-byte repository/Downloads paths and verified conflict-preserving copies.

Next prove restricted mix/positive/reduced/Boolean coherence, instantiate the
intended-presentation and uniform-substitution/congruence bridges, and complete
both maximality routes, the model corollary and all remaining mathematical claims
in all three v7 appendices. The historical checkpoints below retain their dated
scope; their open normalization statuses are superseded by this current table.
Continue under the full-paper authorization without another routine checkpoint.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md']:
 p=root/rel;s=p.read_text();a=s.index('## Current all fourteen blocked reductions');b=s.index('## ',a+3)
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+block+s[b:]
 s=s.replace('Both erratum rows are closed. Global cut elimination, coherence and all other full-paper obligations\nretain their current status.', 'Both erratum rows are closed. Global cut elimination is now proved by the\ncurrent unrestricted interfaces; coherence and the other full-paper obligations\nretain their separate statuses.')
 p.write_text(s)
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text();a=s.index('The completed 77199ac run',s.index('## Immediate continuation'));b=s.index('At unchanged degree',a)
s=s[:a]+'''811eceeb and all successor reviews are incorporated. The retained conjR_right_first
equation, all twelve binary branches, all fourteen blocked families, complete
tag/constructor dispatch, original-rank induction, strict degree induction and
arbitrary-G normalization are now proved. Actual CutElimination P and
AtomizedCutElimination P inhabitants are exported in GentzenCutElimination.lean.
Reuse full Reducibility, Blocked-w, simultaneous cleaning and every completed
principal, structural, unary, binary and blocked source/rank theorem. Coherence
is the immediate mathematical continuation; cut elimination alone does not close
any remaining intended-presentation or full-paper bridge. Historical records do
not reset this compiled scope. Preserve the following accepted recursion contract.

'''+s[b:];p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('All fourteen blocked families are complete. Assemble\nexhaustive dispatch and global rank/degree induction.', 'All fourteen blocked families are complete. Exhaustive constructor/tag dispatch,\noriginal-rank induction, strong degree induction and arbitrary-G normalization\nnow prove actual CutElimination P and AtomizedCutElimination P inhabitants.\nContinue restricted mix/positive/reduced/Boolean coherence and the full-paper bridges.');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();a=s.index('Current construction');b=s.index('| Root and selected region')
s=s[:a]+'''Current construction incorporates 811eceeb. All twelve binary branches and all
fourteen blocked families are proved. Both parametric and blocked dispatchers,
the complete classification, nested rank/degree induction and arbitrary-proof
normalization now supply actual unrestricted CutElimination P and
AtomizedCutElimination P inhabitants. Current report: GENTZEN_CUT_ELIMINATION_REPORT.md.
Both Appendix C rows remain proved; original ranks are measured before adapters.

'''+s[b:]
s=s.replace('Existing rank-two/leaf classification; dispatcher pending','Leaf case in clean_rank_step; rank-two degree step when both sides are leaves')
s=s.replace('All fourteen local blocked reductions are proved; global dispatch/induction\nremains open.', 'All fourteen local blocked reductions are proved and instantiated by the two\ncomplete blocked dispatchers and global induction.')
a=s.index('Remaining induction assembly:');s=s[:a]+'''Completed induction assembly: PositionalCut.clean_rank_step exhausts all selected
classes, clean_elimination proves all original ranks at a fixed degree,
cutFree_degree_step applies simultaneous cleaning afterward, head_cut_elimination
discharges strict DegreeBelow, and G.cut_free_normalization handles arbitrary
proof trees. cut_elimination and atomized_cut_elimination supply both unrestricted
interfaces. Exact signatures and actual global witnesses are in
Checks/GlobalCutElimination.lean. Coherence and full-paper maximality remain open.
''';p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Global cut-elimination continuation (29 October 2026)

Complete constructor/tag dispatch and nested original-rank/formula-degree induction
now supply actual CutElimination P and AtomizedCutElimination P inhabitants.
Cleaning is applied only after fixed-degree all-ranks elimination. The left
gammaDisj dispatcher uses node-free context association preserving rank, Clean
and Eliminated. Equal-labelled positions remain distinct. All accepted source/
rank/atomization decisions and both Appendix C concrete rows persist. No new
manuscript defect was found; all nine blobs and the stash are unchanged. Current
maps and full-paper immediate continuation are reconciled in one pass; dated
historical evidence remains preserved. See GENTZEN_CUT_ELIMINATION_REPORT.md and
its two local reviews. Coherence and all later full-paper duties remain open.
'''+s[a:];p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_263C452.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER ALL FOURTEEN BLOCKED FAMILIES: ASSEMBLE GLOBAL INDUCTION','CONTINUE V7 AFTER UNRESTRICTED CUT ELIMINATION: PROVE COHERENCE')
s=s.replace('Read GENTZEN_ALL_BLOCKED_REPORT.md', 'Read GENTZEN_CUT_ELIMINATION_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_ALL_BLOCKED_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_19B3002.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_263C452.txt, archived verbatim.\nThe 19B3002 continuation remains preserved.')
s=s.replace('All fourteen blocked families are complete; global dispatch/induction remains open.', '''All fourteen blocked families are complete. Both blocked and parametric
dispatchers, clean_rank_step, clean_elimination, cutFree_degree_step,
head_cut_elimination and G.cut_free_normalization are now proved. Actual
cut_elimination : CutElimination P and atomized_cut_elimination :
AtomizedCutElimination P are exported for arbitrary P without supplied handlers.
Exact original sequents and Reduced equality are preserved.''')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Current local evidence: eight new production modules, exact general signatures
and actual global normalization witnesses, strict pinned source/dependency audit,
all public check files and 44 expected rejections. Actual counts/exits/hashes and
checked/committed source bytes: provenance/wsl-gentzen-global-induction/.
Checks/GlobalCutElimination.lean covers arbitrary P, signed/negative literals,
Empty/constants, a cut below thinning and duplicated arbitrary contexts, using
the actual unrestricted eliminator. All prior evidence remains preserved.
Reviews are local author-side; independent replay, Comparator and official/service
checks were not performed.
'''+s[b:]
a=s.index('1. Assemble complete constructor/tag dispatch');b=s.index('2. Continue restricted mix',a)
s=s[:a]+'''Complete constructor/tag dispatch, fixed-degree all-ranks Clean under strict
DegreeBelow, subsequent arbitrary-premise simultaneous cleaning, strong degree
induction and arbitrary-G normalization are now proved. Actual unrestricted
CutElimination P and AtomizedCutElimination P inhabitants preserve exact original
sequents and Reduced equality. No conditional handler bundle remains in these
endpoints. Reuse them; do not reopen their accepted recursion contract.

1. Continue restricted mix'''+s[b+len('2. Continue restricted mix'):]
s=s.replace('all\n40 controls.', 'all\n44 controls.')
s=s.replace('plus the second-conjunction proof/receipt 7d14053 / 19b3002. Deliver', 'plus the second-conjunction proof/receipt 7d14053 / 19b3002 and the all-fourteen\nproof/receipt 80b9472 / 263c452. Deliver')
p.write_text(s)
print('Reconciled actual unrestricted elimination and all active maps; coherence/full-paper duties continue')
