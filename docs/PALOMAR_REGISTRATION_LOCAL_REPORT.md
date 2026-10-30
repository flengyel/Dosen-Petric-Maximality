# Palomar registration local verification — 30 October 2026

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
The stash remains `dedfd8fc8cd49930e9a162d5be585215b062a43c`. Existing proof modules and all 11 manuscript
files are unchanged; v8 and the earlier versions are preserved. No other project
checkout was modified.

Verified immutable candidate: `2e771844077fd8cebfbe365230f13d4dd13a75b1`, pushed to the isolated private
branch. All 1,870 committed Lean files and the critical submission inputs were
matched against the checked bytes from the Git object database. The exact source
tree and file hashes are recorded in `RELEASE_CANDIDATE.json` and
`COMMITTED_SOURCE_AUDIT.json`. Later evidence/delivery commits retain this
verified source identity. No public release, repository visibility change,
service intake or registration was performed.

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
| Expanded definition audit | Pass: 360 concrete declarations, five selected types, every constructor/recursor and relevant value closure. Two generated declarations require alpha-renaming bound universe names containing module identities. Arity, order and all uses remain checked. The public Comparator consumes unmodified exports. |
| Proof dependency audit | Pass for all five selected values; only `propext`, `Quot.sound`, `Classical.choice`. Short and fold route checks pass. |
| Lean kernel | Accepted. |
| NanoDa | Accepted. |
| Authenticated con-ron | Accepted 9,639 declarations in `--verified` mode. Its report records the two in-process inductive blocks and the two pinned Nat-operation hoists. |
| Trusted checker controls | Pass: matching pair accepted; changed statement, ill-typed proof and illicit axiom rejected; con-ron accepts the positive control and rejects the ill-typed control. |
| Packaging controls | Six intended rejections: changed generating side condition; changed selected hypothesis; illicit axiom through a helper; selected Challenge-hole dependency; direct and transitive forbidden project imports. |
| Final source rebuild | Pass; after removing two trailing spaces, the newly compiled Solution export is byte-for-byte identical to the export accepted by all three kernels (`FINAL_EXPORT_IDENTITY.json`). |
| Required strict project verification | Pass: 887 source files, 14907 transitive declaration audits. |
| Whole-tree source policy | Pass: 1870 regular Lean files, compiler-parsed module headers, maximum 2278 physical lines; no symlinks, prebuilt objects, submodules or LFS pointers. No dependency packages. |
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
