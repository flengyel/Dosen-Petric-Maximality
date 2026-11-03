# Palomar v3 service verification

3 November 2026. Palomar mechanically verified the ordinary update for
`PALOMAR-2026-10-30-000014`, submission `j92h1fl2enqs`. The service workflow
completed successfully and its full mechanical report has `status: pass`,
`phase: verification`, `stage: complete` and `errors: []`. This report records
mechanical verification; registration and its required review decision remain
separate stages.

## Candidate and workflow

- Repository: `flengyel/Dosen-Petric-Maximality`.
- Source commit: `76a4ea71f257746bb6ea2cb2e686e85914c7347c`.
- Preserved durable tag: `dosen-petric-v25-palomar-v3`.
- Project: repository root; Comparator: `comparator.json`; metadata:
  `formalization.yaml`.
- [Service workflow, run 41587644731](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41587644731).
- Pipeline commit: `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
- Service execution profile: `palomar-namespace-16x32-v1`.
- Mechanical-report SHA-256:
  `a99c3d7e48ac5383e9c3f6bad564284f836eeab879e1fe2c4d1f5f8d0a0066b8`.

The service uses its Namespace runner profile. The preceding full preflight
used `palomar-standard-v1`; its passing report is retained separately and was
reused. Neither run was replaced by ordinary Lean CI or a prior-version check.

## Evidence checked

The workflow concluded `success`. Its report identifies the exact candidate,
repository and root Comparator. The five selected declaration names, Challenge
and Solution modules, shared-definition list and permitted axioms agree with
`comparator.json` at the candidate. The reported SHA-256 values for Challenge,
Solution, Comparator, metadata, Lake manifest, Lakefile and license agree with
the committed bytes. Challenge reports no untrusted source files.

The pinned toolchain is `leanprover/lean4:v4.35.0`. The service completed Lean
verification and the independent NanoDa and con-ron checks. Con-ron accepted
9,639 declarations with `--verified` and exit code 0. The full report retains
its detailed treatment of generated records and declaration ordering.

The only reported warning concerns the configured Challenge source exceeding
the preferred 32 KiB / 300-line review surface. This is a mechanical-report
warning, distinct from any service review finding. The report's errors list is
empty.

The full mechanical report, workflow and job metadata, artifact index and
local binding validation are retained under
`provenance/palomar-v3-service-20261103/`. The service-generated report is kept
byte for byte. Credentials and authenticated private responses remain under
ignored `.codex-work/palomar-v3-update-20261103/`.

## Remaining publication stages

The saved authenticated submission must be continued. Do not repeat intake,
the successful full preflight or service verification. Deliver the exact
returned review and its service digest privately, explain what registration
publishes, and obtain the author's decision before a digest-bound registration
request. Opening the submission page does not provide that decision.

Registration must be followed by public readback confirming version **3** at
`76a4ea71f257746bb6ea2cb2e686e85914c7347c`. A different version or commit stops
final publication. No release artifact, proof, metadata, durable tag, earlier
version or stash was changed. No arXiv upload occurred.

This report and the separate update status are delivered from committed bytes
under `/mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v3-20261103/`, with
conflict preservation and byte verification recorded in the delivery receipt.
