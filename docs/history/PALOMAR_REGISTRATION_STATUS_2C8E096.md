# Palomar registration preparation — 30 October 2026

The author has requested Palomar registration. The full-paper Lean development
is complete; its current source and evidence were reviewed at
`6a66b14b382aac214b52c055b8bf281b35302239`, and the two resulting reviews were
committed at `a2467d0fc64704be27e0eab8e1726c24fb5766b9`.

The next executable local task is [CODEX_PALOMAR_REGISTRATION.txt](CODEX_PALOMAR_REGISTRATION.txt).
It prepares the independent statement/proof package and its verification. Local
WSL Codex remains responsible for implementation and Lean builds under AGENTS.md.
This preparation commit does not contain compiled Challenge/Solution wrappers.

| Stage | Current status |
| --- | --- |
| Full-paper formalization | Complete at the recorded local endpoint; both maximality proofs, coherence, model corollary and all appendices are included. |
| Local production audit | Retained evidence: 883 Lean files, 14,849 declarations, 35 public check files and 74 rejection controls. |
| Current Palomar requirements | Rechecked on 30 October; verifier updated to `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. Policy remains `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`. |
| Independent Challenge/Solution | Construction and checking assigned by the new Codex handoff. |
| Metadata/configuration/workflow | Concrete proposals retained under `docs/palomar/`; not installed as a verified root submission package. |
| Repository/license | Repository remains private and has no adopted root license. Apache-2.0 is proposed, following FailureOfComposition, for explicit consideration with the release candidate. |
| Independent replay / full official preflight | Not yet performed for this submission package. |
| Service verification / editorial review / registration | Not yet requested or performed. |

## Proposed registration scope

Use one configuration at repository root, `comparator.json`, with independently
compiled modules `Challenge` and `Solution`. Proposed declaration names are:

| Declaration | Mathematical content |
| --- | --- |
| `DosenPetric.Palomar.maximality` | An additional equation between distinct parallel arrows forces totality of a uniformly substitution-closed congruence, using the actual source and the fold route. |
| `DosenPetric.Palomar.short_maximality` | The same statement through the manuscript's particular q/e argument. |
| `DosenPetric.Palomar.congruence_dichotomy` | Every such congruence is generated equality or the total relation on each hom-set. |
| `DosenPetric.Palomar.identity_ne_zero` | A variable identity and its primitive zero are distinct modulo the generated equations. |
| `DosenPetric.Palomar.no_top_to_bot` | There is no raw source arrow from top to bottom. |

These are packaging targets, not declarations claimed to exist yet. The
maximality wrappers must imply manuscript Theorem 2.1 by a proved correspondence
with the existing full proof-congruence formulation. The existing
`Presentation.maximality`, `Presentation.short_maximality`, and all subsequent
paper results remain the completed development. The entry's selected declarations
and the broader project's completed coverage must be described separately.

A raw formulation can keep the Challenge readable without importing the proof
library. The source excerpts for formulas, the complete primitive grammar,
generating equations/derivations and substitution occupy about 535 physical lines
and 22,088 bytes before removing incidental imports and adding the compact
congruence, statements and explanation. This is a feasibility measurement, not a
compiled Challenge or a guarantee of its final size. All statement definitions
must have concrete matching bodies; no opaque replacement of the source category
is permitted.

## Concrete materials

- [Current requirements and pins](PALOMAR_REQUIREMENTS.md).
- [Metadata proposal](palomar/formalization.proposed.yaml), using the current v0.4 schema.
- [Comparator proposal](palomar/comparator.proposed.json).
- [Full preflight workflow example](palomar/palomar-preflight.yml.example).
- [Proposed Apache-2.0 text](palomar/LICENSE.Apache-2.0.proposed.txt).
- [Upstream file hashes](../provenance/palomar-registration-2026-10-30/UPSTREAM.json).
- [Preparation checks](../provenance/palomar-registration-2026-10-30/PREPARATION_CHECKS.json).

The proposed publication target is the substantive repository
`flengyel/Dosen-Petric-Maximality`, including its manuscript and retained evidence.
The exact public commit is not known until packaging succeeds. The proposed
authorization answer is that Florian Lengyel is a responsible author or
maintainer. The release decision must identify the exact commit, license,
publication scope, Comparator path and relationship together; it must not describe
the existing private repository as already public.

## Findings affecting packaging

Palomar scans every committed Lean file, including unused historical fixtures.
The reviewed tree contains **1,868** `.lean` files: 883 production/check files and
985 under `provenance/`. The current production checker covers the former set.
The final package therefore needs a repository-wide header, physical-line,
symlink and compiled-artifact scan. The 74 latest retained control sources have
module headers; that observation is not a scan of all historical fixtures.

The verifier downloader now uses a revision-specific directory so the October 22
checkout is preserved. `bash scripts/fetch-palomar.sh` fetches source only; it
does not run verification or submit anything.

No local Lean or TeX build was run by the cloud preparation session. The proposals
were checked for JSON/YAML syntax, schema shape, taxonomy membership, upstream
hashes and consistency of pins and paths. Those checks do not establish that a
Solution passes Comparator or the independent kernels.

Repository reports are retained under `docs/`. This environment cannot access
`/mnt/c/Users/fleng/Downloads`; the Codex handoff includes copying this status
report, the new instructions and the two previous cloud reviews there and
verifying their bytes. No new Downloads delivery is claimed here.
