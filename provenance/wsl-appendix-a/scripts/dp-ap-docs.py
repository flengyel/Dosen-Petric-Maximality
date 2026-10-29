proof_commit=Path('/tmp/dp-ap-proof-commit.txt').read_text().strip()
assert len(proof_commit)==40
for src,dst in [('report','FULL_PAPER_COMPLETION_REPORT.md'),('hostile','reviews/FULL_PAPER_COMPLETION_HOSTILE.md'),('writing','reviews/FULL_PAPER_COMPLETION_WRITING.md'),('claim-map','MANUSCRIPT_COMPLETE_CLAIM_MAP.md')]:
 b=Path('/tmp/dp-ap-'+src+'.md').read_text()
 b=b.replace('The final sweep proves', 'Completed mathematical-source commit: `'+proof_commit+'`.\n\nThe final sweep proves') if src=='report' else b
 (root/'docs'/dst).write_text(b)
active='''## Current complete full-paper formalization (29 October 2026)

All mathematical content of v7 is now proved for the actual equation-generated
Došen–Petrić presentation, with the status/citation refresh preserved in v8.
This includes both maximality routes, the full-source model corollary, all
unnumbered claims, the complete substitution action and actual occurrence/block/
profile/ordinal/renaming/skeleton constructions, all examples and all three
appendices' equations and diagrams. All published inputs used by the actual
proofs are proved or supplied by compatible verified core Lean constructions;
no uninstantiated handler/coherence/conclusion field remains at those endpoints.

The active exhaustive ledger is [MANUSCRIPT_COMPLETE_CLAIM_MAP.md](MANUSCRIPT_COMPLETE_CLAIM_MAP.md).
See [completion report](FULL_PAPER_COMPLETION_REPORT.md),
[hostile review](reviews/FULL_PAPER_COMPLETION_HOSTILE.md) and
[writing review](reviews/FULL_PAPER_COMPLETION_WRITING.md), plus the separate
FULL_SOURCE_MODELS_REPORT.md and all preserved earlier reports. The three old
milestones are explicitly separate rows in the current map. Full-paper closure
includes every additional appendix/model/operation obligation; it is not inferred
from actual maximality alone. Exact mathematical-source commit: PROOF_COMMIT.

Local checks cover 883 Lean files, 14,849 declarations, all 35 public files,
full transitive dependency/source closure and 74 expected rejections. Exact exits,
hashes, checked/committed archive and delivery paths are in provenance/wsl-appendix-a/.
Both reviews are local author-side. Independent replay, Comparator, official
preflight, service verification and publication were not performed. The repository
remains private. The original stash and all preceding source/results/receipts persist.

V8 updates the date and the abstract/introduction/section 6 formalization status,
and cites the immutable completed proof source. V4–v7 remain preserved; all
mathematical text, all appendices and ten diagrams are unchanged. Three stable
TeX passes and visual inspection cover all 13 pages and the updated citation.
FP-SCOPE-20261029 and FP-CITATION-20261029 are resolved. Older dated checkpoints
below retain their historical open statuses and are superseded by this complete
map; they are not new outstanding mathematical tasks.

'''.replace('PROOF_COMMIT',proof_commit)
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md','docs/PRESENTATION_CORRESPONDENCE.md']:
 p=root/rel;s=p.read_text().replace('## Current full-source models and model corollary','## Retained full-source models and model corollary checkpoint');a=s.index('\n')+1
 block=active if rel!='README.md' else active.replace('](MANUSCRIPT_','](docs/MANUSCRIPT_').replace('](FULL_','](docs/FULL_').replace('](reviews/','](docs/reviews/')
 p.write_text(s[:a]+'\n'+block+s[a:])
p=root/'docs/MANUSCRIPT_STATEMENTS.md';lines=p.read_text().splitlines()
for i,t in enumerate(lines):
 if t.startswith('| Appendix A |'):lines[i]='| Appendix A | ProfileComposition.Data, PatternProfiles actual finite coordinate/label/ordinal constructions; Formula skeleton/renaming/action theorems; ManuscriptSubstitution signed specializations | Complete all profiles, D/C injections and unique gamma/chi/delta, all squares, prefix sums/inverse/locator including zero blocks, actual left-to-right index/book correspondence, skeleton reconstruction, eight-position example, noninjective renaming and both signs. See the exhaustive complete claim map. |'
 if t.startswith('| `eq:occ-substitution` |'):lines[i]='| `eq:occ-substitution` | Formula.expand/contract and inverses; blockLabel/block_square/contract_label; Term.substitution_coordinates; PatternProfiles.actual_ordinal_square | Complete actual tags, labels, full raw/quotient arrow relation, profile/finite-ordinal correspondence, empties and repeated positions. |'
p.write_text('\n'.join(lines)+'\n')
s=p.read_text().replace('General arrow-action identity/composition with endpoint identifications remains\na separate obligation.', 'General arrow-action identity/composition/extensionality with explicit endpoint\ntransports is now proved by PresentationSubstitutionActionQuotient.lean.').replace('The full-source model corollary is now proved and instantiated. Remaining\narrow-action and Appendix A/profile/ordinal correspondences stay open.', 'The full-source model corollary, arrow-action laws and complete Appendix A\nprofile/ordinal/skeleton/renaming correspondences are now proved and instantiated.')
p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('The current manuscript in `manuscript/` is v7;\nv4, v5 and v6 remain preserved.', 'The current manuscript in `manuscript/` is v8;\nv4, v5, v6 and v7 remain preserved. V8 updates only the formalization status,\ndate and immutable proof-source citation; the full mathematical contract is\nall v7 content unchanged.')
s=s.replace('corollary are now proved and instantiated. Continue remaining substitution-action and\nAppendix A profile/ordinal/renaming/example claims, and final manuscript scope\nrefresh.', 'corollary are now proved and instantiated. General substitution-action transports,\nall Appendix A profile/ordinal/renaming/example/skeleton claims, every unnumbered\nmathematical assertion and the final manuscript scope/citation refresh are now\nproved and locally verified. The full-paper mathematical endpoint is complete;\nindependent verification, Comparator, official/service checks and publication\nremain separate, unperformed statuses.')
s=s.replace('`docs/CODEX_NEXT_SESSION.txt` governs the immediate continuation after 811eceeb integration.', '`docs/CODEX_NEXT_SESSION.txt` records the completed endpoint and preservation\nrequirements after 811eceeb integration. The active complete ledger is\n`docs/MANUSCRIPT_COMPLETE_CLAIM_MAP.md`.')
p.write_text(s)
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text();a=s.index('811eceeb and all successor reviews',s.index('## Immediate continuation'));b=s.index('At unchanged degree',a)
s=s[:a]+'''811eceeb and all successor instructions are incorporated. Every mathematical
requirement of this full-paper contract is locally complete. See the current
complete claim map and completion report for exact declarations, local verification,
immutable source and committed-byte delivery. Both proof routes, all three
appendices and all unnumbered assertions are covered. The model, action, profile,
ordinal, renaming, skeleton and final scope/citation duties formerly listed here
are discharged. Preserve the complete source and every accepted correction.
Independent replay, Comparator and official/service verification remain future
statuses, not mathematical proof holes or completed checks. No publication is
authorized. Historical implementation/recursion constraints below are retained.

'''+s[b:];p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;p.write_text(s[:a]+'''
## Final scope and citation corrections resolved (29 October 2026)

FP-SCOPE-20261029 is resolved in preserved manuscript v8: its abstract,
introduction and section 6 now describe actual coherence/input instantiation,
both maximality proofs, the model corollary and appendix correspondences.
V4–v7 remain byte-preserved. All mathematical text, appendices, ten diagrams,
references and AI disclosure are unchanged except the proof-source revision
anchor described next. Current linked maps, README, AGENTS, continuation and
validation records all point to the complete local scope.

FP-CITATION-20261029: the inherited Formalization bibliography anchor cited
1e967bcb913a, an early source revision lacking the completed proofs now described.
V8 cites completed mathematical-source commit PROOF_COMMIT. This avoids a
self-referential commit citation; the later manuscript/evidence commit records
its own exact bytes separately. Prior versions retain their historical anchor.
Three stable TeX passes, source/PDF hashes, reference/overflow checks and visual
inspection of all 13 pages and the corrected bibliography are retained in
provenance/wsl-appendix-a/. The complete text of all three appendices is byte-identical
between v7 and v8; the later bibliography has only the recorded anchor update. Both corrections are closed; no false mathematical theorem
was established during the work.

Final correspondence additions include exact p⇒p nonexistence and its
hom/global-point bijection, the genuine congruence quotient retaining products/
coproducts/units, the finite relation functor, the contextual-zero alternative,
and the actual signed single-variable substitutions and double-negation diagram.
The complete source-index/ordinal bridge is proved, rather than assuming an
arbitrary finite bijection matches the printed order. Every parallel affected
passage and the active claim map were reconciled. Earlier failed elaboration
attempts are retained as development checks; they do not count as successful
negative controls or as manuscript defects.
'''.replace('PROOF_COMMIT',proof_commit)+s[a:])
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();s+='''
## Complete full-paper endpoint (29 October 2026)

All source/rank/cleaning/atomization/coherence and both actual maximality routes
are retained. Full model semantics, action transports, all Appendix A profiles/
ordinal/renaming/skeleton/example constructions, all unnumbered consequences,
Appendix B and both Appendix C source/rank correspondences are now complete.
See MANUSCRIPT_COMPLETE_CLAIM_MAP.md and FULL_PAPER_COMPLETION_REPORT.md. Local
source/audit/check scope is complete; independent/service/publication statuses
remain separate and unperformed. Every previous correction and proof remains.
''';p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_37CCE28.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
p.write_text('''FULL-PAPER MATHEMATICAL FORMALIZATION COMPLETE — PRESERVE VERIFIED SOURCE

Read AGENTS.md, MANUSCRIPT_COMPLETE_CLAIM_MAP.md, FULL_PAPER_COMPLETION_REPORT.md
with both local reviews, MANUSCRIPT_CORRECTIONS.md and the final evidence under
provenance/wsl-appendix-a/. The current manuscript is v8, preserving all v7
mathematics and all three appendices; only formalization status/date/citation
changed. V4–v7, all ten diagrams, references and AI disclosure remain preserved.
The full mathematical-source commit cited by v8 is PROOF_COMMIT.

The full-paper contract is locally complete. Do not reopen historical open
statuses as current mathematical duties. The prior continuation and all its
linked handoffs, corrections, reviews, verification and delivery requirements
are archived verbatim in history/CODEX_NEXT_SESSION_37CCE28.txt and predecessor
histories. 811eceebf9991640cf9dcd3923925f75235d4199 and its reviews are incorporated;
all earlier requested successors were preserved and incorporated. No reset was
used. Preserve stash dedfd8fc8cd49930e9a162d5be585215b062a43c and unrelated checkouts.

COMPLETED ENDPOINTS

All twelve binary and fourteen blocked source/selected equations, exact
reconstructions and original-rank calls; Reducibility, Blocked-w, simultaneous
atomization/blocked cleaning, exhaustive constructor/tag dispatch, original Clean/
rho contracts, original-rank/degree/global induction, actual cut elimination and
atomized cut elimination; both Appendix C concrete source/rank comparisons.

Actual positive/Reduced/Boolean coherence, signed normalization, intended faithful
interpretation, nonthin Nat and empty hom-sets; full raw/quotient congruence and
uniform closure bridges; actual maximality, raw maximality and equality/total
dichotomy. Both proofs remain: symmetric fold/mix and the exact short q/e proof
with constructed inverses and every displayed intermediate equation. The three
milestones remain separately recorded, and the extra full-paper obligations are
individually closed in the complete claim map.

Complete-source models, all-valuation/full interpretations, quotient functors,
evaluation correspondence and substitution precomposition; universal-agreement
full congruence, model instantiation and model corollary for all native target
parallel arrows. No fixed-kernel closure or surjectivity assumption.

All source operation/substitution/negation laws and general raw/quotient action
identity/composition/extensionality with both endpoint transports; actual complete
31-constructor occurrence-block/label/relation square; all Appendix A profiles,
D/C injections, unique gamma/chi/delta and all squares, zero-block prefix sums,
encoders/inverses/unique locator/one-based book formula, exact actual occurrence
indices, skeleton/profile/generalized-composite reconstruction, all eight example
outputs and delta(2)=3, noninjective renaming and both signed context specializations.

All unnumbered consequences, including exact p⇒p exponential obstruction and
hom/global-point bijection, finite-relation functor, witnessed zero independence/
absorption and contextual alternative, genuine congruence quotients retaining
products/coprod/units/zero identities/empty hom-sets, exact DN diagram and all
Appendix B source identities. FP-SCOPE-20261029 and FP-CITATION-20261029 are repaired
and verified in v8 with all linked current records reconciled.

VERIFICATION AND DELIVERY

Pinned Lean 4.35.0 core only. Strict local build, 883 source files, 14,849 audited
project declarations, all 35 public checks and 74 expected rejections. One heavy
build/audit at a time, actual exits/logs retained. All sources use module headers
and are below 10,000 physical lines. No custom mathematical axioms, proof holes,
native_decide, assumed source handlers/coherence/normalization or conclusion-
restatement fields occur at actual endpoints. Empty hom-sets and witnessed zeros,
repeated tags, both signs and original left-first composition are preserved.

V8: three stable TeX passes, no undefined references/citations or overfull boxes,
all13 pages visually inspected, corrected immutable proof citation checked, all
appendices and ten diagrams preserved. Exact hashes, source archive readback and
checked/committed comparisons are in the final evidence. Local hostile/writing
reviews are retained under docs/reviews and delivered with every new report.

All reports/reviews/changed records and v8 artifacts are delivered from committed
bytes to /mnt/c/Users/fleng/Downloads, preserving differing existing filenames
with commit suffixes and verifying every copy. Exact repository/Downloads paths,
source commits and SHA-256 values are in provenance/wsl-appendix-a/DELIVERY_REGISTER.json.
The previous model register (4f40450/37cce28), full block/isolation register
(c366dc3/b257325), short proof (3d30b77/d8dc710), actual main (640cc9e/d68da50),
coherence (8c9e0f3/a80a353), cut elimination (852502b/75b8e48), all-blocked
(80b9472/263c452) and every preceding receipt remain preserved. The three
811eceeb instruction/review files were already delivered and verified.

SEPARATE FUTURE STATUSES

Independent kernel replay, Comparator, official preflight, service verification
and publication were not performed. They are not mathematical proof holes and
must not be reported as complete. Follow PALOMAR_REQUIREMENTS.md and recheck
upstream only if submission/independent verification is later authorized.
Keep this repository private. No arXiv/Palomar submission, author contact,
distribution license selection, visibility change or publication is authorized.
For future requested changes, preserve both proof routes, every accepted
correction and the complete current claim-to-declaration correspondence; rerun
only checks justified by the affected scope and deliver all new reports.
'''.replace('PROOF_COMMIT',proof_commit))
print('Reconciled complete full-paper endpoint, exact claim map and both resolved scope/citation corrections')
