# Official full Palomar preflight — passed

**Official mechanical status: `pass`; phase: `verification`; stage: `complete`.**
[GitHub run 41129351329](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41129351329) completed successfully for the immutable submission
`2e771844077fd8cebfbe365230f13d4dd13a75b1`. The repository is public under the author-approved Apache-2.0
license, including the original manuscript and retained history.

## Exact run and evidence

| Field | Verified value |
| --- | --- |
| Repository | `flengyel/Dosen-Petric-Maximality` |
| Submitted proof source | `2e771844077fd8cebfbe365230f13d4dd13a75b1` |
| Comparator path | `comparator.json` |
| Pipeline pin | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` |
| Mode / profile | `full` / `palomar-standard-v1` |
| Request | `preflight001` |
| Workflow caller head | `ac2503166ebbb5084a3da4999f4193c8607e1d14` |
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Lean toolchain commit | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Official mechanical report SHA-256 | `b21cdb78ae39b47b11e96be06a388787cd8d6d8ace045e4d403fb50cd14db8c9` |
| Artifact ZIP SHA-256 | `d6b0921b4b8d6b237a39c8d47e760fbb3a47b435877ff59dcd6d06a3957e36ff` |
| GitHub artifact | `mechanical-report-preflight001`, ID `13012687151` |

The downloaded ZIP's SHA-256 matches GitHub's advertised artifact digest. Its
single `mechanical-report.json` was retained byte-for-byte and checked for the
exact repository, immutable source, workflow URL, standard profile and full
verification phase. The caller head identifies the workflow launch, while the
submitted proof source above identifies what was checked. `preflight001` is the
workflow request identifier, not a Palomar service submission or registry ID.

## Mechanical outcomes

| Check | Actual official result |
| --- | --- |
| Source and license | Exact source fetched; Apache-2.0 declared and detected. |
| Whole-source policy | All 1,870 regular Lean sources checked with `lean --deps-json`; module/line policy passed. |
| Challenge provenance | High trust; no project imports, no untrusted sources; one core source dependency. |
| Independent Challenge | 562 lines, 23,920 bytes; concrete definitions and five intended statement-proof placeholders. |
| Solution build | Fresh build passed: 758 build jobs. |
| Public Comparator | Exact five selected types and their required definition closure matched; definition holes `[]`; only `propext`, `Quot.sound`, `Classical.choice` permitted. |
| Lean kernel | Accepted. |
| NanoDa | Accepted. |
| Protected authenticated con-ron | Accepted 9,639 declarations in `--verified` mode. |
| Resource outcome | No OOM/OOM-kill, deadline or supervisor timeout event. |

The protected con-ron binary is SHA-256
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`, from the policy-authenticated
v4.36.0-rc1 checker update for the submitted Lean 4.35.0 toolchain. **The Lean
compiler was not upgraded.** Its output records two inductive blocks modelled
in-process (Lean.Syntax and DosenPetric.TraceTree; 51 generated records checked
as declarations) and the two pinned Nat-operation hoists. These actual outcomes
are retained, not inferred from the earlier local replay.

The sole official warning is that the Challenge exceeds the preferred
300-line/32-KiB review surface. Its 562 lines exceed the preferred line count;
its 23,920 bytes are below 32 KiB. Both hard limits, 1,000 lines and 100 KiB,
are satisfied. The finite concrete presentation is preserved.

The standard GitHub-hosted runner reported 4 CPUs and 16,760,332,288 bytes of
host memory. Measured solution build time was 282.559 seconds, Solution export
5.621 seconds, Comparator 39.781 seconds, and con-ron 26.059 seconds. These are
observed phase measurements, not estimates of proof-development cost or total
job duration. Supervised proof phases returned success. Deliberate confinement
negative probes have expected nonzero exits; they are not failed proof phases.
Full resource records, tool digests and complete public job logs are retained.

## Source and publication scope

The author approved the concrete public-release question with “Yes.” The source,
root Comparator and all 17 critical input hashes remain fixed. The completed
local package, strict audit, expanded definition audit and focused controls were
reused. No local proof rewrite, new mathematical assumption or Lean upgrade was
introduced for this official run. The complete-paper claim map and manuscripts
remain preserved; the five selected statements are the two maximality routes,
the maximality dichotomy, and two structural witnesses.

The release authorization, public visibility check, dispatch inputs, run/job
records, artifact listing, original mechanical JSON and ZIP, and tool digests are
retained under `provenance/wsl-palomar-official-preflight-20261030/`.

## Next stages and author control

No Palomar service intake, editorial review or final registration has occurred.
The agreed scope is to bring this official result to the author before intake.
When proceeding, use repository `flengyel/Dosen-Petric-Maximality`, exact source `2e771844077fd8cebfbe365230f13d4dd13a75b1`, root
`comparator.json`, and the responsible author/maintainer relationship for Florian
Lengyel. Recheck current service instructions and registration identity before
intake; do not reuse another project's registry ID or automate browser sign-in.

The actual private service review must be shown to the author, with its digest
and what registration publishes, before final registration. Public-release
approval does not approve an unseen review. Keep service tokens and private
review material out of public Git history.

The author explicitly specified **Palomar Registry registration first, then
arXiv submission**. No arXiv submission has occurred. The Local connectedness in
recursion categories and essential incompleteness project follows arXiv.

## Metadata correction

One temporary clone-credential field in a repository-metadata log was redacted
after the final audit. GitHub documents a five-minute lifetime; the credential
had expired before the log was committed. The original official report and ZIP
remain byte-identical. See [the correction record](PALOMAR_PREFLIGHT_METADATA_CORRECTION.md).

## Delivery

Final reports and principal machine evidence are delivered from committed Git
bytes to `/mnt/c/Users/fleng/Downloads`. Differing prior files are preserved.
The official-preflight delivery receipt records exact source commits, repository
paths, Downloads paths and hashes; the evidence source commit does not replace
the verified submission SHA above.
