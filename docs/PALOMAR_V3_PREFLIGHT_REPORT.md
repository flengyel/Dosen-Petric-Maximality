# Palomar v3 candidate: official full preflight passed

3 November 2026. Repository: `flengyel/Dosen-Petric-Maximality`.
Candidate: **`76a4ea71f257746bb6ea2cb2e686e85914c7347c`**.
Durable release tag: **`dosen-petric-v25-palomar-v3`**.
Existing registry ID: `PALOMAR-2026-10-30-000014`; intended successor: version 3.

The official **full** mechanical preflight for this exact candidate passed:
[run 41580971518](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41580971518).
Both workflow jobs completed successfully. The complete mechanical report has
`status: pass`, `phase: verification`, `stage: complete` and `errors: []`.
This is a new-candidate preflight, not reuse of a v1/v2 run or ordinary Lean CI.
It is not registration or a service editorial review.

## Exact candidate and protocol

Origin was fetched. The remote durable tag resolves directly to the full
candidate SHA above, as does the existing local tag. The tag was not created,
deleted, moved or forced. The initially clean main checkout was fast-forwarded
to the release; the existing stash was preserved.

The handoff and release records were read from the candidate itself. All 37
artifact hashes in its release manifest match that snapshot. All 56 manuscript
Lean links use the durable tag and resolve to the preserved 49 declaration
destinations. The current paper, bibliography, metadata and claim-map source
links contain no floating main reference. No paper, PDF, package, metadata,
release link, Lean source or verifier input was revised.

The production proof and verifier inputs are byte-identical to registered v2
source `5dbee39bea09539bd130f729e82636419f71f920`: DosenPetric, its root
aggregator, Challenge, Solution, Checks, Comparator configuration, toolchain
and Lake files. Existing manuscript/package build evidence and earlier proof
audits were reused. They did not substitute for this new official preflight.

The live protocol was rechecked. PalomarSubmission's current head and the
wrapper's `uses`/`pipeline_commit` agree on
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; the workflow ran in `full` mode
under `palomar-standard-v1`. The current PalomarPolicy head is
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`.
The source project is the repository root, with `comparator.json` and
`formalization.yaml`.

## Mechanical result

The downloaded artifact is `mechanical-report-preflight001`, artifact ID
`13205289687`. Exact report SHA-256:
`61c666fbe96eea6346716ab7ceafa7a3ffa4e13e9ea1633e65fb5aefe5a8706b`.

The report binds the exact candidate, five selected declarations, configuration,
Challenge, Solution, formalization metadata, Lakefile, manifest, licence and
`leanprover/lean4:v4.35.0`. Those file hashes were checked against committed
bytes. The Challenge has no untrusted source dependencies. The complete source
scan checked 1,870 Lean files with the module/header and line-cap requirements.

Lean's kernel and NanoDa accepted. The protected con-ron replay also accepted
9,639 declarations, with exit code 0. Its two modelled inductive blocks and
two reordered Nat declarations are recorded in the complete report; this is
an accepted replay, not an inconclusive attempt.

The sole reported warning is the existing Challenge audit-surface warning:
the 572-line Challenge exceeds the preferred 300-line surface while remaining
within the hard limits. There are no blocking errors.

Complete public evidence and the exact-hash validation are retained under
`provenance/palomar-v3-preflight-20261103/`.

## Remaining stages and delivery

The public indexes inspected before intake list only registered versions 1
and 2. The candidate is absent from the registered-commit identity index.
Version 3 remains unconfirmed. The ordinary update must use the existing ID;
service verification, delivery of the exact private review, the author's
digest-bound decision and exact public v3 readback remain separate stages.
The service transaction and its outcome are recorded separately.

The candidate's v3 citation remains anticipated until the public record confirms
version 3 at the exact candidate. The frozen release must not be changed to
accommodate a different version or source. No arXiv upload was performed.

Downloads delivery uses committed bytes and a separate verified receipt under
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v3-20261103/`, preserving
any conflicting existing copy. Credentials and unregistered review material
remain in ignored private staging, outside this public evidence.
