# Palomar requirements checked on 30 October 2026

The author has requested registration. [The active handoff](CODEX_PALOMAR_REGISTRATION.txt)
and [stage record](PALOMAR_REGISTRATION_STATUS.md) describe the current work.

## Current authoritative sources

| Source | Immutable revision |
| --- | --- |
| [PalomarSubmission verifier](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7) | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` |
| [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md) and [protocol specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/docs/specification.md) | `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60` |
| [formalization.yaml standard](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e) | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` |
| [Service instructions](https://submit.palomar-registry.org/llms.txt) | Live service document read on 30 October; reread before intake. |

Hashes of inspected upstream files and the small current policy JSON files are
retained in `provenance/palomar-registration-2026-10-30/`. Earlier snapshots remain
historical evidence. Recheck upstream before the actual service submission;
record a changed pin and rerun only the checks affected by the change.

## Statement and proof package

Use one Comparator configuration for this entry. Its required fields are
`challenge_module`, `solution_module`, nonempty `theorem_names`, and
`permitted_axioms`. The optional `definition_names` is empty for this project.
Do not put workflow profiles or external-kernel configuration in this JSON.

The Challenge is independently compiled. Its only nonlocal dependencies may be
Lean core or verified canonical Mathlib, Tau Ceti or CSLib closures. It cannot
import a DosenPetric module, directly or transitively. Prefer core-only definitions
for this package. The actual source grammar, generating equations and derivation
relation must be visible and concrete; Solution then uses the completed library.

The Challenge limit is 1,000 physical lines and 100 KiB. More than 300 lines or
32 KiB produces an auditability warning, not automatic rejection. Keep meaningful
docstrings and the actual mathematical statement instead of compressing code to
evade readability requirements. Exactly the selected theorem declarations may
have deliberate Challenge proof holes. Solution and its transitive proof
dependencies may use only `propext`, `Quot.sound`, and `Classical.choice`.

Every regular committed Lean file, including historical negative controls and
unused files, must use `module` and have at most 10,000 physical lines. The
`lakefile.lean` header exemption does not remove its line limit. Reject Lean
symlinks, submitted compiled artifacts, LFS pointers and submitted submodules.
Exclude `.git` and `.lake` from the source scan. Preserve historical evidence
through an explicit byte-preserving relocation/archive if a fixture needs a
different retention form; do not silently rewrite its recorded bytes.

Pin public GitHub dependencies to full 40-character revisions with credential-free
HTTPS manifest URLs. This project currently has no external Lake packages and
should not acquire Mathlib or Foundation solely to imitate the predecessor.

## Compiler and kernels

The current toolchain minimum remains Lean `v4.35.0-rc2`. Preserve the project's
stable `leanprover/lean4:v4.35.0`. The release supplies Lake Comparator, exporter,
Lean checker and NanoDa. Palomar requires acceptance by Lean and NanoDa and
independently attempts con-ron. Its protected checker manifest selects the
authenticated con-ron from Lean `v4.36.0-rc1` for this source compiler. A recognized
support/fuel/capacity decline is recorded as inconclusive for con-ron; an actual
rejection, unknown error, authentication failure or nonstandard axiom blocks the
run. Retain the full report's `kernels`, `kernel_attempts`, `tool_digests` and
`con_ron_checker`, and do not turn a decline into an acceptance.

## Metadata and publication inputs

Use `version: v0.4` in `formalization.yaml`; the verifier's metadata repair profile
has schema version 4, which is a different identifier. Required facts include a
project title and description, human authors and responsible maintainers, SPDX
license, valid arXiv classifications, substantive sources, automation methods and
accurate pre-submission review status. Use `sources[].relationship` precisely;
this project formalizes its existing manuscript and the published dependencies.
It must not claim the formalization was the first presentation of the result.

The submitted repository is the substantive development, so no thin-wrapper
section is needed. Any change to a separate wrapper repository would require a
public pinned substantive repository and corresponding metadata; it does not
avoid the source-publication requirement.

The repository must be public at a full immutable commit. Exactly one recognized
root license file must match `project.license`. The project remains private and
has no selected license at this preparation checkpoint. The Apache-2.0 text and
metadata under `docs/palomar/` are release proposals, not an adopted license or
claim that the package is mechanically ready.

## Official full preflight

After the candidate is public with its agreed license, invoke the exact reusable
workflow `.github/workflows/submission.yml` from the pinned PalomarSubmission
revision. Use the same full revision for the workflow `uses` and `pipeline_commit`,
`mode: full`, and `execution_profile: palomar-standard-v1`. Supply a 12-character
lowercase alphanumeric `request_id`, the repository, exact candidate commit,
Comparator path and truthful authorization relationship. The retained workflow
example uses `preflight001`, which has exactly twelve characters.

The standard external profile is `ubuntu-24.04`, with a 19,800-second execution
budget and a minimum host memory of 15,032,385,536 bytes. Palomar's own default
Namespace profile is different. The local WSL run must inspect actual memory and
swap; setting `LEAN_NUM_THREADS=1` is not a RAM limit.

Read the complete mechanical report and require `status: pass`. A standalone
Comparator success or preparation-only `mode: preflight` does not meet this gate.
On resource or infrastructure failures, follow the structured diagnosis; do not
blindly resubmit or repeatedly rerun unchanged successful checks.

## Intake, review and registration

`https://submit.palomar-registry.org/` is the sole intake. Before agent-driven
intake, the service requires the author to agree to the displayed repository,
full commit, Comparator path and authorization relationship. Prepare all these
values and the publication/license proposal before requesting that decision.

The author may use the browser flow personally. An agent must not automate the
browser sign-in or reuse a browser session to impersonate that authorization.
The documented agent alternative uses authenticated `gh`, a temporary tag at the
candidate commit and a newly created secret gist. Use it only when its existing
authorization and permissions suffice; never solicit a password or put tokens
in reports. Remove the temporary artifacts after verification. Preserve the
submission bearer token privately and keep private review content out of public
commits before registration.

For an ordinary new submission, leave `existing_id` absent unless the registry's
repository/identity lookup finds an existing entry for this exact registration
identity. Poll running verification at most once a minute and awaiting review at
most once every five minutes. Honor service cooldowns and terminal states.

After the service supplies its review, show the author that exact review and what
registration will publish. `POST /register` requires the digest from
`GET /api/review` and the author's decision concerning that review. A request to
prepare registration does not establish consent to an unseen review. Mechanical
preflight, service verification, editorial review and registered status remain
distinct facts.
