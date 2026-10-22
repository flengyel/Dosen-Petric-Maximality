# Palomar contract checked for this project

Checked on 22 October 2026 UTC. The [official verifier](https://github.com/PalomarRegistry/PalomarSubmission/tree/5cfaefe2f4c18f237c63d9635f9f54ab68785d89)
is pinned to `5cfaefe2f4c18f237c63d9635f9f54ab68785d89`. The policy snapshot is
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`. The three relevant JSON policy
files are preserved under `provenance/`. Recheck upstream before submission.

## Changes from FailureOfComposition

| Area | Current contract and project action |
| --- | --- |
| Toolchain | Schema 2 specifies minimum v4.35.0-rc2. This project selects stable v4.35.0, rather than copying the predecessor's release candidate. |
| Proof tools | The submitted Lean release supplies Lake Comparator, exporter, checker, and independent kernels. Do not copy the predecessor's standalone-tool pins. |
| Required acceptance | Lean and NanoDa must accept. The verifier independently attempts con-ron. A recognized support, fuel, or authenticated capacity decline may be inconclusive; rejection, an unknown error, or a nonstandard axiom blocks acceptance. |
| Checker update | For v4.35.0, the protected manifest selects con-ron from v4.36.0-rc1, release commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e. The archive and executable hashes are in `palomar-checker-revisions.json`. Source Lean, exporter, and NanoDa stay at v4.35.0. |
| Metadata | `formalization.yaml` uses version v0.4 and current provenance fields. The verifier's separate formalization profile has schema version 4. These are different version identifiers. |
| License | One recognized, nonempty repository-root license must match `project.license` as an SPDX identifier. No distribution license has been selected for this private project. |
| Repository | Service verification requires a public GitHub repository and a full immutable commit. This repository remains private; public release and submission are later actions. |
| Selection | Exactly one Comparator configuration per entry; one configuration may select several declarations. Names must state conditional scope accurately. |
| Challenge | Independently compiled against canonical allowed inputs. Maximum 1,000 physical lines and 100 KiB. It cannot import the submitted Solution or arbitrary project modules. Shared definitions must be included and compared faithfully. |
| Source | Regular Lean files use the module system; all submitted Lean files have at most 10,000 physical lines. The lakefile.lean module-header exemption does not remove the line limit. |
| Dependencies | Full 40-character commits of public GitHub sources; complete manifest closure. No submitted submodules, LFS pointers, or prebuilt proof artifacts replacing source. |
| Axioms | At most `propext`, `Quot.sound`, `Classical.choice` in Solution dependencies. Deliberate selected theorem holes belong only in Challenge. |
| Reports | Inspect full JSON verdicts, including `kernels`, `kernel_attempts`, actual tool digests, and con-ron provenance. Record declines separately from acceptance. |

The current verifier's [README](https://github.com/PalomarRegistry/PalomarSubmission/blob/5cfaefe2f4c18f237c63d9635f9f54ab68785d89/README.md)
documents the implementation contract, including the protected checker update.
Older policy wording about standalone binaries must not silently override it.

## Adapted predecessor procedure

The inspected FailureOfComposition snapshot is
`506d1f1494d6c05b0ba304edf5fe0bfa6c32864b`; its registered source is
`fb32a19c4883baad83b286d4594cfbc6b1d2ad5c`, entry
[PALOMAR-2026-10-01-000013 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-01-000013&version=1).

The two manuscript maps preserve mathematical scope. The independent interface
check compares selected types and transitively reachable shared definitions
under consistent universe renaming. Dependency audits reject unexpected
axioms and illicit Challenge dependencies. Focused negative controls change
a shared definition or inject an illicit dependency and require rejection.
These checks must be adapted after the first actual theorem is selected; no
arithmetic dependencies or “Nine” naming are carried into this project.

The current scripts provide only source screening, a strict build, and a
transitive axiom audit. Exact Challenge/Solution comparison, source-closure
policy, negative controls, and official verification remain to be implemented.

Before an authorized registry submission, prepare a license and metadata,
build each side independently, run the current Comparator and official
verifier on one immutable commit, reconstruct from that commit, and preserve
logs, command exit statuses, source hashes, tools, and complete reports.
Read `https://submit.palomar-registry.org/llms.txt` when submission is actually
requested. Local compilation, local Comparator acceptance, official preflight,
service verification, automated editorial review, and publication remain
distinct statuses.
