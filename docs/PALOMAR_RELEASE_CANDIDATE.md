# Verified Palomar release candidate

Verified immutable source: **`2e771844077fd8cebfbe365230f13d4dd13a75b1`**.

Private repository: `flengyel/Dosen-Petric-Maximality`.
Current integration branch: `main`. The candidate and evidence were fast-forwarded
into main through `23ec1bc6a492fab4de42c209f00f692b1851cf9a` on 30 October 2026.
The preserved preparation branch is `palomar/registration-20261030`.
Subsequent documentation commits do not replace the verified submission SHA.
[Exact source tree](https://github.com/flengyel/Dosen-Petric-Maximality/tree/2e771844077fd8cebfbe365230f13d4dd13a75b1).
Git tree: `51c600eda4a839e519d89e28efdca100723b210a`.

The source was committed and pushed after the local checks passed. All 1,870
committed Lean files were then read from the Git object database and matched
against the checked source hashes. The critical submission files were checked
from committed bytes as well. The final strictly rebuilt Solution export is
byte-for-byte identical to the export accepted by Lean, NanoDa and authenticated
con-ron. Later report/evidence/delivery commits do not change this source identity.

The five selected statements are the actual-source fold maximality, actual q/e
short maximality, congruence dichotomy, nonzero literal identity, and empty
top-to-bottom hom-set, all under `DosenPetric.Palomar`. The primitive/full
quotient congruence correspondence is proved, including derived negation for
closed relations. The retained complete-paper scope remains unchanged.

## Verification and exact inputs

| Check | Result |
| --- | --- |
| Independent core-only Challenge and actual-source Solution | Pass |
| Exact public Comparator/type/definition closure | Pass |
| Expanded 360-declaration/five-type comparison and proof-route audit | Pass |
| Lean / NanoDa / authenticated con-ron | Accepted / accepted / accepted |
| Focused packaging controls | Six required rejections |
| Strict production checks | 887 files, 14,907 declaration audits |
| All-source headers/layout/import closures | 1,870 files; pass |
| Manuscript preservation | All 11 files unchanged |
| Metadata official loader/schema/taxonomy and pinned workflow | Pass |
| Commit-byte/source correspondence | Pass |
| Official full preflight / service / editorial / registration | Not performed |

| Submission input | SHA-256 |
| --- | --- |
| `Challenge.lean` | `2bbfaf6f18b1385adc6d36694f1b05a632e4ebc26a775ed455c60abf19b856f5` |
| `DosenPetric.lean` | `eb76110e1dfdbf18f7d75ba4a86e775b19668fb3669243487a902596a8a17a3c` |
| `Solution.lean` | `418b69bd252a93b7f420be67f5d0418a1a39f79e17988cd81dfe0f2eec4f9b91` |
| `Checks/Axioms.lean` | `32fe1605e5b14d07aa9d0ffb6171fdcb923199c30870f3892e87ff80aae5c0a6` |
| `DosenPetric/PalomarCorrespondence.lean` | `05c0087512136a77c4ced9c2a466dee7d40a65a3247ba69f131d437321d962e9` |
| `DosenPetric/PalomarDefinitions.lean` | `20aebf0d443f561646d183418e5c211dc9dbface77fe4be32b8359924296a1e6` |
| `DosenPetric/PalomarMaximality.lean` | `d203c8c017e32d755938a5a1f0caae2d83bd2d7c119a54885e0f4bc339eadf39` |
| `scripts/PalomarClosureAudit.lean` | `b733d92f3e3365eca651c520765515d300bb0e125abc75cebac57f211e134ebe` |
| `comparator.json` | `db36e6b9256356ca97a16be363a878b1feb337afd3217ef86096a29218290abb` |
| `formalization.yaml` | `ffd9b763a744d0e2f895772a36a01321ec1dc128476dfebc19d91a569f5efb03` |
| `LICENSE` | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `1a20167e2938ffcc6ffeca143dfd65883be292f2ffd039953fb5ea24fc188796` |
| `lake-manifest.json` | `01a12079da418a0c2cb55ddb97259aeb6b1a66c9ccc15b222e172b17f56c5822` |
| `.github/workflows/palomar-preflight.yml` | `f96f61d30ae94145a0a75c8862c3c0b7d621bbb42ef731cbf6a8fc2263be1176` |
| `scripts/check-source.py` | `1dd02d451eaf4a6334c821191a09e9346287389c72e6c5a5032efb3f16c627a9` |
| `scripts/verify.sh` | `1a3b0cc1c0677c40bab8ab742c30b73a6d1a10eb58f227f16f606a400f22047b` |

Machine records: `provenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json`
and `COMMITTED_SOURCE_AUDIT.json`. The [local report](PALOMAR_REGISTRATION_LOCAL_REPORT.md)
retains the mathematical scope, tools, outcomes and corrected first failures.
The source, original cloud reports, current reviews and instructions are retained
on main and in the preserved preparation worktree. Committed-byte Downloads
receipts identify the exact versions previously delivered.

## Concrete release decision

The proposed decision is to adopt **Apache-2.0, including the contained original
manuscript**, and publish the substantive repository
**`flengyel/Dosen-Petric-Maximality`**, including its retained source history,
manuscripts and evidence, for the exact candidate
**`2e771844077fd8cebfbe365230f13d4dd13a75b1`**, using root **`comparator.json`**.
The author/maintainer is **Florian Lengyel**, with the authorization relationship
**“I am a responsible author or maintainer.”**

The repository remains private. Main now includes the complete candidate and
receipts through `23ec1bc6a492fab4de42c209f00f692b1851cf9a`, including the root
Apache-2.0 license text and prepared workflow. The stash remains
`dedfd8fc8cd49930e9a162d5be585215b062a43c`. Explicit public release/license
confirmation is pending; the recommendation to approve release has been
recorded without treating it as a completed visibility change.

This gate comes from `AGENTS.md`, “Complete authorized reversible preparation
before presenting the exact publication/license/submission decision,” and
`docs/CODEX_PALOMAR_REGISTRATION.txt` §3, which states that the retained license
proposal is not the repository's currently adopted license. General preparation
authorization therefore does not silently supply this concrete release choice.

## Toolchain and next required check

Keep Lean pinned at 4.35.0. The current verifier remains
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; its
[checker policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/checker-revisions.json)
explicitly supplies the protected con-ron checker for Lean 4.35.0. No Lean
upgrade is required. Reuse the completed local comparison and kernel evidence.
Official full preflight is the next verification stage.

An authenticated Windows GitHub CLI session for `flengyel` and the registered
manual-only workflow are available. Publication and dispatch can proceed after
the explicit release confirmation.

## After that decision

Use the prepared manual-only reusable workflow, with both `uses` and
`pipeline_commit` pinned to `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, exact
source `2e771844077fd8cebfbe365230f13d4dd13a75b1`, mode `full`, profile `palomar-standard-v1`, request
`preflight001`, and root `comparator.json`. Require mechanical status `pass`
before intake. Recheck current upstream/service instructions and use the exact
repository/commit/configuration/relationship agreement. Existing SSH access is
not by itself the service's API authentication proof.

The eventual private service review must be shown to the author before any
registration of that review's digest. No unseen review is approved here. This
release-candidate preparation does not claim a service verdict or registry entry.
