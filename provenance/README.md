# Input and upstream provenance

The private repository preserves the supplied manuscript v4 without edits.
`manuscript/SHA256SUMS` records its TeX and PDF hashes; run
`sha256sum --check SHA256SUMS` from the manuscript directory.
`docs/CONTINUATION.txt` is the supplied continuation text, also unchanged.

| Supplied artifact | SHA-256 |
| --- | --- |
| Continuation_Maximality_Lean_Palomar_2026-10-22.txt | e8e91dc6060714bd87dc926a09f077b430fe27591db700e526dfafe44156f6e0 |
| Maximality_Lean_Continuation_Bundle_2026-10-22.zip | e25b8016f9f52443b8eefa873e64d038eaaa7f83e7aa245010191fd7aede0798 |

The original archive is not duplicated in the repository. Its manuscript and
continuation content are retained at the documented paths.

`pins.json` identifies the exact Lean, optional Mathlib, predecessor, and
Palomar revisions. The three policy snapshots come from
[PalomarSubmission at 5cfaefe2](https://github.com/PalomarRegistry/PalomarSubmission/tree/5cfaefe2f4c18f237c63d9635f9f54ab68785d89):

| Local snapshot | Upstream path |
| --- | --- |
| palomar-toolchains.json | toolchains.json |
| palomar-checker-revisions.json | checker-revisions.json |
| palomar-formalization-profile.json | formalization-profile.json |

`ci-75b3a704-build.txt` is the build/audit excerpt from the successful workflow
linked in `docs/VALIDATION.md`. It preserves CI timestamps and source hashes;
terminal color escape sequences were removed. The workflow artifact contains
the original verification log and Lake manifest. These are preliminary Lean
build records, not Palomar acceptance evidence.
