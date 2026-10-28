for src,dst in [('report','GENTZEN_LOGICAL_BINARY_CUTS_REPORT.md'),('hostile','reviews/GENTZEN_LOGICAL_BINARY_CUTS_HOSTILE.md'),('writing','reviews/GENTZEN_LOGICAL_BINARY_CUTS_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-logical-'+src+'.md').read_bytes())
active='''## Current logical binary construction (28 October 2026)

Successor b767c19 and the completed four mix branches are preserved, together
with stash dedfd8fc8cd49930e9a162d5be585215b062a43c. Mix proof/receipt commits:
a654ed0 / 408257b. Their 19 committed-byte Downloads deliveries are complete.

The right cut through the second child of G.conjR is now complete through
BinaryLogical.conjRRightSecond_equation and
CutCommutation.conjR_right_second_rank_step. The generic builder takes the
actual original child-cut output and rebuilds G.conjR with the retained B tag,
then applies only list-association comparisons. Count, Atomized, congruence and
eliminated-witness laws are proved. rankIH uses the original inherited clean
child before routing. Product/distribution, residual association, actual native
fold/unit and selected-tag diagrams are all instantiated. mixedDisj_swap is a
separate proved Reduced interchange, derived from dist_b_disj and symmetry laws;
it is available for subsequent cases, not a general proof duality.

See [the run report](GENTZEN_LOGICAL_BINARY_CUTS_REPORT.md),
[hostile audit](reviews/GENTZEN_LOGICAL_BINARY_CUTS_HOSTILE.md),
[writing review](reviews/GENTZEN_LOGICAL_BINARY_CUTS_WRITING.md) and
[live constructor/tag table](GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md).
The preceding four mix constructions and their exact implementation choices
remain recorded in GENTZEN_BINARY_MIX_CUTS_REPORT.md and its two reviews.

| Local proof phase | Lean files | Audited declarations | Exact check files | Rejected controls | Evidence directory |
| --- | ---: | ---: | ---: | ---: | --- |
| 21627c4; same-side construction | 522 | 11,765 | 9 | 7 | provenance/wsl-gentzen-after-67de18a/ |
| ea74a32; mix algebra | 524 | 11,780 | 10 | 7 | provenance/wsl-gentzen-mix-union/ |
| a654ed0; four mix branches | 538 | 11,886 | 11 | 8 | provenance/wsl-gentzen-binary-cuts/ |
| One logical binary branch and mixed-rule symmetry | 546 | 11,911 | 12 | 9 | provenance/wsl-gentzen-logical-binary-cuts/ |

Strict, expanded-type, actual literal/constant-witness, source-closure and
negative-control checks pass locally. Reviews are local author-side reviews;
no independent kernel replay, Comparator, official/service verification or
publication is claimed. All manuscript bytes remain unchanged from 408257b.

Seven logical binary equations/reconstructions/rank steps remain open, as do
all fourteen blocked reductions, the complete dispatcher, discharged rank/degree/
structural inductions, both unrestricted elimination endpoints, coherence and
later full-paper claims. All three milestones and the additional whole-paper
endpoint remain distinct. V7 and all three appendices remain in scope; Appendix C
is written and its two concrete blocked-rank Lean correspondences remain open.
The exact next native first-child candidate/equation is retained outside production
at provenance/wsl-gentzen-logical-binary-cuts/open/next-native-first.lean.

Prior 23, 18-entry, 14-entry and current 19-entry completed delivery registers
retain their completed status. The three b767c19 successor files are included
in the 19-entry register. This phase's finalized reports/reviews and changed
records use its own committed-byte DELIVERY_REGISTER.json. CODEX_NEXT_SESSION.txt
and the live table carry the exact continuation; old checkpoints are historical.

'''
for rel in ['MANUSCRIPT_STATEMENTS.md','MANUSCRIPT_COVERAGE.md','VALIDATION.md','CODEX_FULL_MANUSCRIPT_FORMALIZATION.md']:
 p=root/'docs'/rel;s=p.read_text();start=s.index('## Current actual mix-cut construction');end=s.index('## ',start+3);p.write_text(s[:start]+active+s[end:])
p=root/'README.md';s=p.read_text();start=s.index('## Current actual mix-cut construction');end=s.index('## Current manuscript',start);p.write_text(s[:start]+active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')+s[end:])
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text().replace('The four mix\nequations/reconstructions/rank steps are now proved; eight logical binary\nequations/reconstructions/rank steps remain open.','The four mix branches and conjR_right_second are proved through actual\nequations/reconstructions/rank steps; seven logical binary branches remain open.')
s=s.replace('Complete the eight\nlogical binary branches, proving every actual native diagram. Continue','Complete the seven remaining\nlogical binary branches, proving every actual native diagram. Continue');p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();hist=root/'docs/history/CODEX_NEXT_SESSION_408257B.txt';assert not hist.exists() or hist.read_bytes()==old
if not hist.exists():hist.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER ACTUAL MIX-CUT RECONSTRUCTIONS: LOGICAL BINARY BRANCHES','CONTINUE V7 AFTER CONJR RIGHT-SECOND: SEVEN LOGICAL BINARY BRANCHES')
s=s.replace('the current mix-cut report\nand both reviews','the current logical-binary report\nand both reviews, the retained mix-cut report/reviews')
s=s.replace('The eight logical binary\nequations/reconstructions/rank-step wrappers remain open.','The conjR_right_second branch now has its actual equation/reconstruction and\ninstantiated rank step; seven logical binary branches remain open.')
s=s.replace('Local current verification: 538 Lean files, 11,886 audited declarations, eleven\nexact check files and eight rejected controls, including actual native binary\nwitness checks. Current evidence: provenance/wsl-gentzen-binary-cuts/.','Local current verification: 546 Lean files, 11,911 audited declarations, twelve\nexact check files and nine rejected controls, including actual native logical\nbinary witnesses. Current evidence: provenance/wsl-gentzen-logical-binary-cuts/.\nPreceding four mix branches: a654ed0 / receipt 408257b, 538/11,886/eleven/eight\nin provenance/wsl-gentzen-binary-cuts/.')
s=s.replace('2. Complete the eight conjR/disjL binary branches using the successor\'s retained','2. Reuse the completed conjR_right_second branch and mixedDisj_swap. See\nGENTZEN_LOGICAL_BINARY_CUTS_REPORT.md, both reviews and current evidence. The\nactual builder is conjRRightSecond; its generic native version is conjSecondNative.\nIts count/Atomized/congruence laws and original-child rank step are instantiated.\nComplete the seven remaining conjR/disjL binary branches using the successor\'s retained')
s=s.replace('3. Prove all seven BlockedL', '''The immediate next target is conjR_right_first. The exact native candidate and
unresolved equation are retained in current evidence open/next-native-first.lean:
f : G P (C :: Γ) (A :: Δ), g : G P Θ (B :: Λ), h : G P I (C :: D).
Reconstruct G.conjR (G.cut h f) g, exchange I/Θ under Γ and D/Λ under
fresh A∧B and Δ, giving G P ((Γ ++ Θ) ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D).
The candidate is typed but its Reduced equation is not proved. Use the actual
mixedDisj_swap and fold/distribution laws; then lift to original selected tags,
count/Atomized/congruence, eliminated and rank_step. The old failed distributor
symmetry attempt is resolved by mixedDisj_swap, not an outstanding obstruction.
3. Prove all seven BlockedL''')
s=s.replace('Run local strict/dependency/type checks and all seven controls, including','Run local strict/dependency/type checks and all nine controls, including')
s=s.replace('The three B8FCD28 successor files (instruction, source review and writing review)', 'The completed 19-entry mix-binary register includes its run report/reviews and\nthe three B8FCD28 successor files (instruction, source review and writing review)')
s=s.replace('Current local run\nreports and both reviews require their finalized committed-byte Downloads copies,','Current logical-binary run\nreports and both reviews use their own finalized committed-byte Downloads copies,')
s=s.replace('current\nDELIVERY_REGISTER.json.', 'current\nprovenance/wsl-gentzen-logical-binary-cuts/DELIVERY_REGISTER.json.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a='## Current correction status\n\n';s=s.replace(a,a+'''The actual conjR_right_second equation/reconstruction and original-rank step
are now proved; seven logical binary and fourteen blocked reductions remain
open. mixedDisj_swap is proved from actual Reduced distribution/symmetry laws.
Its earlier simplification failure was resolved, not a counterexample or source
erratum. The next native first-child equation is retained as an open proof
obligation outside production. No new manuscript correction is established.
All previous mathematical/writing decisions and completed deliveries persist.

''',1)
s=s.replace('writing and all-three-appendix requirements persist. Eight logical binary and\nfourteen blocked reductions remain open.','writing and all-three-appendix requirements persist. The current logical-binary\nstatus is given above.')
p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();s=s.replace('This live table records all four actual mix branches after b767c19.','This live table records all four actual mix branches and conjR_right_second\nafter b767c19, a654ed0 and receipt 408257b.')
s=s.replace('| conjR, second child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Clean/rank descent checked; equation, reconstruction and rank step pending |','| conjR, second child parametric tag | Clean/rank descent checked; equation, reconstruction and rank step pending | Equation/reconstruction and instantiated rank step checked (BinaryLogical.conjRRightSecond/conjRRightSecond_equation; CutCommutation.conjR_right_second_rank_step) |')
s=s.replace('the eight logical binary branches remain open.','conjR_right_second is now complete; seven logical binary branches remain open.')
s=s.replace('| Blocked constructor family |', '''The right-second conjunction reconstruction preserves the retained B tag,
cut count and Atomized condition, with actual native fold/unit and head-routing
diagrams. mixedDisj_swap is a proved Reduced interchange available for later
cases, not a native first-child equation or a general G duality. Exact next native
first-child candidate/equation: current evidence open/next-native-first.lean.
Report/evidence: GENTZEN_LOGICAL_BINARY_CUTS_REPORT.md and
provenance/wsl-gentzen-logical-binary-cuts/.

| Blocked constructor family |''',1)
p.write_text(s)
print('Reconciled the actual fifth binary branch, seven remaining logical cases and full contract')
