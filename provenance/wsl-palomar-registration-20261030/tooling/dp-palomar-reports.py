import re
whole=json.loads((ev/'WHOLE_SOURCE_AUDIT.json').read_text())
assert whole['status']=='pass'
defs=json.loads((ev/'DEFINITION_AUDIT_RESULT.json').read_text());assert defs['status']=='pass'
mandatory=json.loads((ev/'MANDATORY_REPLAY.json').read_text());assert mandatory['status']=='pass'
conron=json.loads((ev/'CON_RON_REPLAY.json').read_text());assert conron['status']=='accepted'
controls=json.loads((ev/'PACKAGE_CONTROLS.json').read_text());assert controls['status']=='pass' and controls['required_rejections']==6
strict=json.loads((ev/'STRICT_VERIFICATION.json').read_text());assert strict['exit_status']==0
log=(main/strict['log']).read_text();counts=re.findall(r'PASS: (\d+) source files',log);axioms=re.findall(r'PASS: transitive axiom checks for (\d+) project declarations',log)
assert counts and axioms
stage_record=dict(schema_version=1,date='2026-10-30',source_base='2c8e0968ad4fa3d318b98bcab4e531bb728b86cd',mathematical_source='630c4b6e47da16a1434476a211fd29ce6adc5569',branch='palomar/registration-20261030',stages=dict(local_mathematics='complete; existing full-paper endpoint preserved',package_build='pass',type_and_definition_comparison='pass; unmodified public Comparator plus expanded declaration audit',local_independent_replay=dict(Lean='accepted',NanoDa='accepted',con_ron='accepted'),official_full_preflight='not run; awaits concrete release/license decision',service_verification='not requested',editorial_outcome='not requested',registration='not requested'),production_files=int(counts[-1]),audited_declarations=int(axioms[-1]),whole_tree_lean_files=whole['regular_lean_files'],expanded_concrete_declarations=defs['concrete_declarations'],selected_types=5,negative_packaging_controls=6,permitted_axioms=['propext','Quot.sound','Classical.choice'],challenge=dict(lines=562,bytes=23920,proof_holes=5,definition_holes=0,sha256=sha((rc/'Challenge.lean').read_bytes())),repository=dict(name='flengyel/Dosen-Petric-Maximality',visibility='private',license='Apache-2.0 proposal on isolated candidate only',root_license_on_main=False),stash=whole['stash'],main_clean=True,publication_or_service_action_performed=False)
(ev/'REGISTRATION_STAGE.json').write_text(json.dumps(stage_record,indent=2)+'\n')
report=f'''# Palomar registration local verification — 30 October 2026

The independent five-statement package passes local verification. Lean, NanoDa
and the authenticated protected con-ron checker accept its complete selected
proof closure. The expanded audit also compares all 360 concrete presentation
declarations and the five selected types. This is a verified private release
candidate; official full preflight and service registration have not run.

## Source and preservation

The main checkout was fast-forwarded safely from
`6a66b14b382aac214b52c055b8bf281b35302239` through
`2c8e0968ad4fa3d318b98bcab4e531bb728b86cd`, incorporating `a2467d0` and the
registration handoff. Preparation takes place on `palomar/registration-20261030`
in an isolated worktree. Main remains clean at `2c8e0968ad4fa3d318b98bcab4e531bb728b86cd`.
The stash remains `{whole['stash']}`. Existing proof modules and all 11 manuscript
files are unchanged; v8 and the earlier versions are preserved. No other project
checkout was modified.

The immutable candidate SHA and exact committed file hashes are assigned in a
subsequent evidence-only record after this source snapshot is committed. That
record identifies the verified source, independently of later report/delivery
commits. No public release, repository visibility change, service intake or
registration was performed.

## Selected mathematics

`DosenPetric.Palomar.maximality`, `short_maximality`, `congruence_dichotomy`,
`identity_ne_zero` and `no_top_to_bot` are production declarations, imported by
`Solution`. The first route uses actual-source isolation and symmetric-fold
collapse. The second uses actual source isolation, uniform contextual equations
and `Presentation.ShortProof.total` with the particular q/e arrows. The exported
proof dependency audit confirms that the short route reaches those constructions
and does not use selected fold maximality, `relative_maximality`, fragment
maximality/dichotomy or the closed-fragment extension. It also has no dependency
on `ContextualCollapse.total`.

`PalomarCorrespondence` proves quotient descent, reverse restriction, both
pointwise inverse relation correspondences, substitution closure, totality and
distinctness correspondence, and derived-negation compatibility for closed
primitive congruences. The full-congruence extension uses the previously proved
fragment dichotomy. This use is recorded separately from the independent short
proof. The three maximality wrappers intentionally retain `[Nonempty P]` to
match the manuscript; the underlying actual-source theorem is stronger.

See [the mathematical account](PALOMAR_STATEMENT_CORRESPONDENCE.md). The complete
full-paper claim map remains unchanged. The five selected statements do not
purport to select every coherence, model or appendix result independently.

## Results and scope

| Stage | Actual result |
| --- | --- |
| Clean library build | Pass: fresh candidate `.lake`, 849 baseline build jobs, no reused main-checkout objects. |
| Solution | Pass after compiling the new correspondence and endpoint modules. |
| Independent canonical Challenge | Pass: compiled directly against pinned core, with a protected per-run module alias and four hashed artifacts. Its only source dependency is SDK `Init.lean`; no project import. |
| Public package Challenge build | Pass; exactly five intentional theorem holes, with the warning exception confined to the Challenge library. |
| Public Comparator | Pass with the exact final five-field `comparator.json`; no definition holes or extra permitted axioms. The verifier-owned copy supplies only the protected alias and mandatory kernel setup. |
| Expanded definition audit | Pass: {defs['concrete_declarations']} concrete declarations, five selected types, every constructor/recursor and relevant value closure. Two generated declarations require alpha-renaming bound universe names containing module identities. Arity, order and all uses remain checked. The public Comparator consumes unmodified exports. |
| Proof dependency audit | Pass for all five selected values; only `propext`, `Quot.sound`, `Classical.choice`. Short and fold route checks pass. |
| Lean kernel | Accepted. |
| NanoDa | Accepted. |
| Authenticated con-ron | Accepted 9,639 declarations in `--verified` mode. Its report records the two in-process inductive blocks and the two pinned Nat-operation hoists. |
| Trusted checker controls | Pass: matching pair accepted; changed statement, ill-typed proof and illicit axiom rejected; con-ron accepts the positive control and rejects the ill-typed control. |
| Packaging controls | Six intended rejections: changed generating side condition; changed selected hypothesis; illicit axiom through a helper; selected Challenge-hole dependency; direct and transitive forbidden project imports. |
| Final source rebuild | Pass; after removing two trailing spaces, the newly compiled Solution export is byte-for-byte identical to the export accepted by all three kernels (`FINAL_EXPORT_IDENTITY.json`). |
| Required strict project verification | Pass: {counts[-1]} source files, {axioms[-1]} transitive declaration audits. |
| Whole-tree source policy | Pass: {whole['regular_lean_files']} regular Lean files, compiler-parsed module headers, maximum {whole['maximum_physical_lines']} physical lines; no symlinks, prebuilt objects, submodules or LFS pointers. No dependency packages. |
| Source closure | Pass: Challenge is core-only, and Solution's full local import graph has no Challenge or protected alias dependency. |
| Metadata | Pass: pinned official loader, v0.4 schema and taxonomy; human author/maintainer Florian Lengyel; actual source-based ChatGPT/Codex roles; no invented model IDs/costs or external peer review claim. |
| Manuscripts | All 11 retained files match the integrated source bytes. |
| Official full preflight | Not run. The pinned manual-only full workflow is prepared. |
| Service verification, editorial outcome, registration | Not requested or performed. |

The 35 earlier public check files and 74 earlier rejection controls remain
retained evidence of the complete-paper endpoint. This packaging task adds six
focused controls and reruns the affected strict build/axiom and closure checks;
it does not relabel the historical checks as newly rerun.

## Exact tools and local commands

Compiler: pinned Lean `4.35.0`; Lake `5.0.0-src+eb6cafb`. The verifier source is
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; policy is
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`; metadata standard is
`99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. Live upstream heads were rechecked and
match these pins. The service instructions were read at
https://submit.palomar-registry.org/llms.txt.

Con-ron is the policy-authenticated v4.36.0-rc1 checker, SHA-256
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`.
The pinned Lean compiler and bundled checker were not overwritten. Tool digests,
release/archive authentication and isolated tooling versions are retained.

Commands include `lake build`, `lake build Solution`, `lake build Challenge` and
`bash scripts/verify.sh`, with `LEAN_NUM_THREADS=1`. Protected comparison uses
the pinned verifier's canonical Challenge compiler, exporter, `judge_exports`
and authenticated checker replay. The actual judge invokes release
`lake comparator --config ... --challenge-from-export ... --solution-from-export ...`;
its concrete arguments and complete captured streams are retained under
`provenance/wsl-palomar-registration-20261030/logs/`. `LOG_REGISTER.json` gives
retained paths and hashes. Tooling scripts, configurations, targets, source/import
closures, selected export hashes and outcome JSON are retained alongside them.
The large exports and compiler objects remain local ignored artifacts, not
committed prebuilt proof material.

Before large jobs the host had about 16 GiB RAM and no swap; memory and disk were
inspected. The fresh build took 1,623.327 seconds. A single global build/replay
lock was used; builds, exports and kernel replays ran sequentially. Con-ron's
policy-prescribed internal `--jobs=2` is retained. No machine-specific predecessor
cgroup settings or invented hardware/cost measurements were used. These local
protected checks do not constitute the official `palomar-standard-v1` reusable
full-preflight workflow.

## First failures and resolutions

| Actual diagnostic | Resolution and boundary |
| --- | --- |
| Con-ron archive extraction: missing `zstd`. | Authenticated Debian package extracted into isolated tooling; no system installation or compiler replacement. Archive and binary authentication then passed. |
| Protected exporter could not execute `lean`. | Put the real pinned toolchain bin directory on its confined PATH. The failed attempt is retained. |
| Initial excerpt's `Formula.subst._f` referenced `Formula.subst.match_1`, while the actual module reused `Formula.Occ.match_1`. | Include the original concrete `Formula.Occ` definition before substitution. Final exact statement/definition comparison and kernels pass. Production mathematics was unchanged. |
| Expanded audit compared module-qualified bound universe names in generated `Op.noConfusionType`/`Op.noConfusion`. | Alpha-rename only bound universe parameter names in the extra all-declaration audit. The public Comparator remains unmodified and passes separately. |
| NanoDa rejected the expanded export's unused compiler-generated partial recursion helpers. | Retain that export for the additional definition audit. Kernel replay uses exactly the public configuration's required targets and their entire proof closure, as the official exporter does. Lean, NanoDa and con-ron all accept this closure. |
| Auxiliary harness import/native-symbol/syntax/name/logger-initialization errors; first control compiled outside its source root. | Preserve the diagnostics, use explicit SDK imports/native Lake library, correct the harness and fixture source root, and require actual intended rejection verdicts. No unrelated parser/missing-module failure is counted as a control. |

Four historical non-module fixtures were renamed byte-for-byte to `.lean.txt`;
[the source-layout record](PALOMAR_SOURCE_LAYOUT.md) supplies the path/hash mapping
and resolution script. No failed production proof was moved out of the build.

## Release and delivery boundary

The candidate installs the proposed Apache-2.0 text, root metadata/configuration
and full-preflight workflow on the private isolated branch. Main has no adopted
root license and repository visibility remains private. The next decision must
identify the exact candidate commit, Apache-2.0 including the contained original
manuscript, publication of the substantive repository and its retained history,
root `comparator.json`, and Florian Lengyel's relationship, “I am a responsible
author or maintainer.” Preparation authorization does not supply that unrecorded
release decision.

After approval, dispatch the pinned full reusable workflow for that exact source
and require mechanical `pass` before intake. Service authentication and exact
submission agreement follow the then-current instructions. The eventual service
review must be shown to the author before any registration of its digest.

Every finalized report/review and requested instruction is delivered from
committed bytes to Windows Downloads. Differing existing files are preserved;
exact paths, hashes and source commits are recorded in the separate delivery
register and receipt. Copy/verification failures, if any, must remain explicit.
'''
(rc/'docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md').write_text(report)
status='''# Palomar registration release candidate — 30 October 2026

The local package is complete and verified on the private branch
`palomar/registration-20261030`. Main remains clean at
`2c8e0968ad4fa3d318b98bcab4e531bb728b86cd`; the original stash is preserved.
The full-paper mathematical endpoint and all manuscript versions remain intact.

| Stage | Current status |
| --- | --- |
| Full-paper formalization | Complete at the recorded endpoint, mathematical source `630c4b6e47da16a1434476a211fd29ce6adc5569`; broader claim map preserved. |
| Independent Challenge/Solution | Complete; core-only canonical Challenge, separately compiled actual-source Solution. Challenge: 562 lines, 23,920 bytes, five deliberate theorem holes, no definition holes. |
| Statement/definition comparison | Pass: public release Comparator and expanded audit of 360 concrete declarations plus five selected types. |
| Local independent replay | Lean, NanoDa and authenticated protected con-ron accepted. |
| Strict production verification | Pass: 887 files and 14,907 transitive declaration audits. |
| Whole-tree policy/closure | Pass: 1,870 Lean sources, compiler-parsed headers and complete local import closures; four historical fixtures preserved byte-for-byte under mapped `.lean.txt` paths. |
| Packaging controls | Six intended rejections; original full-paper public-check/control evidence preserved. |
| Metadata/workflow | Official loader/schema/taxonomy pass. Root configuration, metadata, proposed license and pinned manual-only full workflow prepared. |
| Repository/license | Repository remains private. Apache-2.0 is proposed on the isolated candidate only; main has no adopted root license. |
| Official full preflight | Pending the concrete publication/license decision. |
| Service verification / editorial outcome / registration | Not requested or performed. |

The selected namespace is `DosenPetric.Palomar`: `maximality`,
`short_maximality`, `congruence_dichotomy`, `identity_ne_zero`, and
`no_top_to_bot`. The [statement/correspondence account](PALOMAR_STATEMENT_CORRESPONDENCE.md)
gives the exact raw-to-quotient meaning and the separate proof routes. The wider
[complete-paper claim map](MANUSCRIPT_COMPLETE_CLAIM_MAP.md) remains authoritative
for additional coherence, model, substitution and appendix results.

See the [local verification report](PALOMAR_REGISTRATION_LOCAL_REPORT.md),
[mathematical review](reviews/PALOMAR_REGISTRATION_REVIEW.md),
[writing review](reviews/PALOMAR_REGISTRATION_WRITING.md), and
[source-layout record](PALOMAR_SOURCE_LAYOUT.md). The machine-readable current
stage is `provenance/wsl-palomar-registration-20261030/REGISTRATION_STAGE.json`.
The immutable source SHA, exact file hashes and release fields are recorded
after committing the source in the separate release-candidate evidence.

Upstream pins remain verifier `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, policy
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`, metadata standard
`99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. They were rechecked locally. The
prepared workflow uses full mode, `palomar-standard-v1`, `preflight001`, the exact
source commit and root `comparator.json`.

The concrete release decision concerns Apache-2.0, including the contained
original manuscript, publication of `flengyel/Dosen-Petric-Maximality` as the
substantive development with its retained history, and Florian Lengyel's
responsible author/maintainer relationship. No visibility change, intake or
registration is inferred from local kernel success. The author must also see
the eventual service review before approving registration of its digest.

The registration handoff and the two previously cloud-only FULL_PAPER_6A66B14
reviews are included in the committed-byte Downloads delivery, together with all
new finalized reports/reviews. The delivery register identifies exact paths and
hashes and preserves any differing pre-existing file.
'''
(rc/'docs/PALOMAR_REGISTRATION_STATUS.md').write_text(status)
p=rc/'docs/history/CODEX_NEXT_SESSION_2C8E096.txt';p.write_bytes(subprocess.check_output(['git','show','2c8e096:docs/CODEX_NEXT_SESSION.txt'],cwd=rc))
next_session='''Current task: the local Palomar registration release candidate is verified.

Do not reopen the completed full-paper proof sequence. Preserve all existing
mathematics, manuscript versions, historical evidence, the original stash and
unrelated checkouts. Main remains clean at 2c8e096; preparation is on the isolated
private branch palomar/registration-20261030. The previous continuation is retained
in docs/history/CODEX_NEXT_SESSION_2C8E096.txt.

Read AGENTS.md, docs/CODEX_PALOMAR_REGISTRATION.txt,
docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md, docs/PALOMAR_REGISTRATION_STATUS.md,
and the PALOMAR_REGISTRATION_REVIEW/WRITING reports. Exact immutable candidate
identity and hashes are recorded in the release-candidate evidence after the
source commit. Later evidence/delivery commits do not change the verified source.

Completed locally: five production endpoints, raw/full quotient correspondence
including derived negation, independent core-only Challenge, exact public
Comparator, extended 360-definition/five-type audit, complete selected proof
closure, Lean/NanoDa/authenticated con-ron acceptance, six packaging controls,
strict verification of 887 production/check files and 14,907 declarations, and
all 1,870 committed Lean source headers/closures/layout checks. All 11 manuscript
files are unchanged. Earlier full-paper 35 public checks/74 controls remain
retained evidence. No official reusable full preflight or service stage has run.

The prepared root Apache-2.0 file is a proposal on the private candidate. Main
has no adopted root license and repository visibility remains private. The next
required author decision identifies the exact candidate SHA, license including
the original manuscript, publication scope of the substantive repository and
history, root comparator.json, and Florian Lengyel's responsible maintainer
relationship. Reuse any later explicit approval of those exact values; do not
ask again or introduce routine implementation checkpoints.

After authorized publication/license action, run the exact pinned full reusable
workflow, for the immutable candidate, with mode full/profile palomar-standard-v1
and request preflight001. Require mechanical pass before actual intake. Recheck
current upstream and service instructions immediately before intake; do not
automate browser sign-in. Keep service review private and show it to the author
before any registration request for that review's digest.

Downloads delivery uses committed bytes, preserves differing files, and records
exact paths/hashes/source commits in the registration delivery register. Keep
local mathematical completion, packaging, comparison, independent replay,
official preflight, service verification, editorial outcome and registration
as distinct statuses.
'''
(rc/'docs/CODEX_NEXT_SESSION.txt').write_text(next_session)
print('Current stage, verification report, status and preserved continuation written')
