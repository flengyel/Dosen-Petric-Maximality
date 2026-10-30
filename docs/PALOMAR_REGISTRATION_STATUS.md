# Palomar registration release candidate — 30 October 2026

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
