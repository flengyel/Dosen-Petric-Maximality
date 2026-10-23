# Current v5 full-review evidence

Reviewed commit: cfa37604e539dc85d854959b20aca752d06774ce, 23 October 2026.
The two reports are `docs/reviews/V5_FULL_HOSTILE_2026-10-23.md` and
`docs/reviews/V5_FULL_WRITING_2026-10-23.md`. Historical reports are preserved.
The manuscript source and PDF were not edited. Their Git blob IDs match the
reviewed remote tree. No Lean source, toolchain, dependency, or mathematical
coverage status changed. No Lean build or axiom audit was rerun.

## Commands and results

- The command arrays in `verification.json` record two LaTeX passes and
  rendering of the committed PDF; each process exited 0.
- Subsequent inspection found the intermediate rebuilt PDF truncated, despite
  the successful LaTeX statuses. `pdftotext` exited 1. One root-rendered page-5
  PNG was also truncated. Neither was the committed manuscript PDF.
- The exact LaTeX command in `verification.json` was rerun a third time,
  redirecting output to `pdflatex-3.log`; exit 0. The final PDF is readable,
  10 pages and 419117 bytes, and its extracted text equals the committed PDF's.
  Its final log has no LaTeX warnings, unresolved references or box warnings.
- `pdftoppm -f 5 -l 5 -scale-to 1450 -png` on the original PDF regenerated
  the affected page, exit 0. All ten original pages were visually inspected;
  separate reviewer renders were intact. No layout defect was observed.
- `python3 full-review-v5/evidence/check_appendix_coordinates.py`: exit 0.
  The retained script is a finite consistency check, not a general proof.
  Counts are recorded in `final-verification.log`.
- `python3 full-review-v5/evidence/verify_review.py`: exit 0. This workspace
  check reconfirmed the unchanged manuscript hashes, 10 readable pages,
  equal extracted text, nine resolved citation keys, exact v8 URL destination,
  absence of source comments, and the six-section hostile-report structure.
  The final inspection data are in `inspection.json`.

## Access and delivery

The book and mathematical-writing course report were consulted in full-text
copies; their source URLs and actual hashes are retained in `sources.json`.
The corresponding primary PDFs are cached in the review workspace, not added
as new repository copies. The earlier full-paper access records remain in
`docs/PRIOR_ART_UPDATE_V5.md` and the historical literature review.

This review ran in a cloud workspace. The WSL repository and Windows Downloads
mount were unavailable; no local-main status, SSH push, or Downloads copy is
claimed. Reports are retained in the repository and delivered as downloadable
files. Repository updates use the connected GitHub service with an expected
head and `force:false`; no visibility setting is changed.

Raw command logs and patches are retained losslessly as `.gz` files.
