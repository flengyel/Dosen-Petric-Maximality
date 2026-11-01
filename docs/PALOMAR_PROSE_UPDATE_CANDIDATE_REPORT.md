# Palomar prose update: candidate and official preflight

The revised public prose is committed and pushed. Official full preflight passed for the exact candidate. Intake, service verification, service review and registration of this update have not been requested or completed. Version 1 remains the current registered version; version 2 is the expected ordinary successor.

## Exact candidate and authorization to be agreed before intake

| Field | Value |
| --- | --- |
| Repository | flengyel/Dosen-Petric-Maximality |
| Candidate commit | 5dbee39bea09539bd130f729e82636419f71f920 |
| Project | Repository root; project_path omitted. |
| Comparator configuration | comparator.json |
| Formalization metadata | formalization.yaml |
| Existing registration | PALOMAR-2026-10-30-000014, version 1. |
| Expected next version | 2. |
| Authorization relationship | Florian Lengyel is a responsible author or maintainer; API label maintainer. |
| Version-1 source retained | 2e771844077fd8cebfbe365230f13d4dd13a75b1 |
| Reviewed manuscript retained | v13 at 84d913d4ab30490ddf9c51788ed89ea5c7e9a601; all manuscript and package bytes unchanged. |

The [candidate commit](https://github.com/flengyel/Dosen-Petric-Maximality/commit/5dbee39bea09539bd130f729e82636419f71f920) contains the complete rewritten text, its before/after report, unified diff and public preview. The later commits recording preflight and delivery evidence do not replace this candidate. Both proof routes are preserved.

The unchanged Comparator selection is:

- `DosenPetric.Palomar.maximality`
- `DosenPetric.Palomar.short_maximality`
- `DosenPetric.Palomar.congruence_dichotomy`
- `DosenPetric.Palomar.identity_ne_zero`
- `DosenPetric.Palomar.no_top_to_bot`

## Verification evidence

The required repository check, separate Challenge/Solution targets, pinned metadata schema and official loader passed. All 887 registered Lean source files were compared with version 1. Six differ only in comments and the other 881 match byte for byte. A separate Lean 4.35.0 expression comparison includes opaque theorem bodies and confirms identical types and values for 26 declarations, including every selected proof term. The initial accessor omitted opaque bodies; evidence review caught this before commit, and the corrected comparison explicitly includes and requires all five proof values. The retained script and hashes describe the corrected comparison. No successful build was repeated for that accessor correction.

Official full preflight: [run 41266833954](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41266833954). The workflow and pipeline_commit both pin PalomarSubmission 14aa8d6b3c2f14a8540605e37144560b9a00e7e7. It used mode full, profile palomar-standard-v1, request_id preflight001 and the repository-root comparator.json. Workflow conclusion: success. Mechanical report: pass; phase verification; stage complete. Its exact source, five names, axioms, toolchain, Challenge/Solution hashes and metadata hash match the candidate. Lean/Comparator and mandatory NanoDa accepted; recorded additional independent kernels: con-ron.

Official report SHA-256: 951da94ee305e525eb4b5a9d3be2de4d92bd97c069f30341187e7e613212aa49.
Artifact ZIP SHA-256: 70b31afd745e7b0871d835906be0367f26f1d6ca980ab83f3a724ae657db16d0.
The ZIP digest agrees with GitHub's artifact digest. The complete report, tool digests, source-closure evidence, resource measurements and kernel attempts are retained in provenance/palomar-prose-update-20261031/official-mechanical-report.json. Its errors list is empty. These are mechanical results, not an editorial outcome or registration.

Warnings in the official report:

- configured Challenge source exceeds the preferred 32 KiB / 300-line review surface

Recorded advisory kernel attempts:

- {"argv": ["/home/runner/work/_temp/palomar/trusted-checker-update/con-ron", "--jobs=2", "--verified"], "budget_seconds": 1800, "detail": "con-ron: accepted 9639 declarations (--verified)\n\ncon-ron: 2 inductive blocks modelled in-process: Lean.Syntax, DosenPetric.TraceTree (51 generated records, checked by the fold as declarations and not counted as records of the file)\ncon-ron: 2 declarations hoisted ahead of the pinned Nat operations they ground: Nat.mul._f, Nat.mul", "exit_code": 0, "name": "con-ron", "reason": "complete", "status": "accepted"}

## Rewritten text and public source readback

[Complete old/new text and unified diff](PALOMAR_PROSE_UPDATE_BEFORE_AFTER.md) prints the supplied opening and abstract and all 60 changed blocks/values. [Continuous preview](PALOMAR_PROSE_UPDATE_PUBLIC_PREVIEW.md) includes every metadata field and every Challenge docstring in order. [HTML preview](../provenance/palomar-prose-update-20261031/public-preview.html) is a readable preparation artifact, not a service-rendered Challenge. [Writing review](reviews/PALOMAR_PROSE_UPDATE_WRITING_2026-10-31.md) records the consulted Knuth–Larrabee–Roberts source and exact review scope.

GitHub readback of Challenge.lean and formalization.yaml at the candidate matches local committed bytes. Challenge SHA-256: ad8c0322978f4f9da3f44070eac45b0e0e2ec5b9f67c929bfbaa37aa662819ef. Metadata SHA-256: 02c71f0fa096cbb4607ace5289a857c444476ca7e4e454519dc48dd1b09946b8. This readback confirms the public candidate, not a new registry abstract or a rendered version-2 Challenge. The current public version index and entry were read before choosing version 2; those records remain retained and unchanged.

## Remaining service stages

Palomar's [live agent instructions](https://submit.palomar-registry.org/llms.txt), under the ordinary submission procedure, explicitly require showing the repository, full commit, Comparator path and authorization relationship and obtaining agreement before POST /api/submit. That author agreement remains pending. The nonsecret request is prepared in provenance/palomar-prose-update-20261031/prepared-intake-request.json; no intake, temporary access-proof tag or secret gist has been created. The route is an ordinary update under the existing ID, not the Technical Maintainer correction procedure.

After pre-intake agreement, use the documented temporary-tag and fresh-secret-gist proof, remove both as instructed and keep service credentials and review responses private. Deliver the exact returned review privately with its review_sha256 and explain what registration will publish. The author must then decide on that delivered review before POST /register. Approval of this candidate or its intake does not approve an unseen review. Only after authorized registration and successful public readback should active registry links and status records change. Any later manuscript citation change requires the next manuscript version, preserving v13 and its supplied version-1 BibTeX.

## Reports and delivery

Repository reports are docs/PALOMAR_PROSE_UPDATE_BEFORE_AFTER.md, docs/PALOMAR_PROSE_UPDATE_PUBLIC_PREVIEW.md, docs/PALOMAR_PROSE_UPDATE_PREPARATION_REPORT.md, docs/reviews/PALOMAR_PROSE_UPDATE_WRITING_2026-10-31.md and this candidate report. The first four, the HTML preview and the raw diff were delivered from candidate-commit bytes and verified by SHA-256. The shared destination is /mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v2-preparation-5dbee39/. This report is delivered after its own commit; the subsequent delivery receipt records the exact committed source, destination, byte count and hash for every copy. Differing destination files are preserved. No new registry links, manuscript releases or arXiv upload are reported.
