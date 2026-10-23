# V5 validation and delivery record

> **Current v5 update.** The Introduction and bibliography were subsequently revised after full-text review of three additional papers. Current hashes, compilation and preservation checks are in [PRIOR_ART_UPDATE_V5.md](PRIOR_ART_UPDATE_V5.md). The build and delivery record below describes the initial v5 bytes and remains preserved.

Date: 23 October 2026 (UTC).

## Scope

Prepared a new manuscript v5 from v4 at `flengyel/Dosen-Petric-Maximality` commit `6192328eccde5e4aa912017409289255bc8c5cb1`. V4 remains preserved. The revision changes the date, adds MSC2020 classifications and keywords, adds two related-work paragraphs, and adds four bibliography entries. It makes no change to the abstract, mathematical definitions, theorem statements, hypotheses, proofs, or Appendix A.

The accompanying literature report records the search, primary-source comparisons and access limits. The hostile and mathematical-writing reports are AI-assisted author-side reviews, not independent peer review. Their final source hashes include the final line-breaking and end-of-file whitespace corrections.

## Exact bytes

| Item | SHA-256 |
| --- | --- |
| Baseline v4 TeX | `aebd6a8be39dcbdcc1a7e5061b4e65a585de2345784011fb03d28cc3326fc93e` |
| Final v5 TeX | `5d9ab4080a52a57d0e3e69bc732ada39e6911bc63cb235bb61fea17448365d2e` |
| Final v5 PDF | `5e72d64ba108d17d539d26e12b3456a51877781e74c232b615cff90466b6480a` |
| Unchanged mathematical region, Section 2 through Appendix A | `696ae7de13f7cf5f1be7f29bd6a873417273400f73a16a303c46daadc418289b` |

The mathematical-region comparison begins at `\section{The Boolean proof category}` and ends immediately before `\paragraph{Use of AI tools.}`. The AI disclosure is also unchanged. The delivered review bundle retains the baseline source and complete v4-to-v5 patch under `evidence/`, with a package checksum manifest. Repository build evidence is retained under `provenance/manuscript-v5/`; `manuscript/SHA256SUMS` covers both manuscript versions.

## Commands and results

The exact absolute-path command arrays and exit codes are in `provenance/manuscript-v5/commands.json` (also `evidence/commands.json` in the delivered review bundle). Each final build pass ran:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory /workspace/scratch/316c37836844/v5/evidence /workspace/scratch/316c37836844/v5/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex
```

Both passes exited **0**. The resulting PDF has **10 pages**. The final TeX log contains no LaTeX warnings, undefined citations/references, overfull boxes, or underfull boxes. All six cited bibliography keys resolve to entries. The PDF's public notes hyperlink has the exact pinned commit and PDF path used in the source.

Whitespace check:

```sh
git diff --no-index --check /workspace/scratch/316c37836844/arxiv-review/manuscript.tex /workspace/scratch/316c37836844/v5/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex
```

This exited **1**, with empty output: `--no-index` reports that the files differ. There were no whitespace-error diagnostics. An earlier check reported an extra blank line at EOF; it was removed before the final two build passes.

## PDF inspection

PyMuPDF 1.26.6 rendered every page at 1.5 times its PDF dimensions. Every resulting PNG was fully loaded with PIL, and a ten-page contact sheet was generated. All pages were visually inspected in that sheet; the title/MSC/related-work page, final appendix diagrams and bibliography were also inspected at full-page resolution. No clipping, overlap, missing glyphs or broken diagrams were observed. Rendered PNGs, contact sheet, extracted text, TeX logs and build metadata are retained in the delivered review bundle. The repository retains the TeX build logs, command record and source diff.

An earlier Poppler-wrapper render exited 0 but produced a truncated PNG. That output was replaced by the successfully decoded PyMuPDF renders. An earlier new paragraph had a 5.16 pt overflow; shortening its first sentence removed it. A preliminary output-decoding wrapper also failed on a non-UTF-8 log byte; subsequent commands captured raw bytes. These production issues are not manuscript content or mathematical findings.

## Boundaries

The preparation phase did not rerun Lean, change its toolchain, modify the WSL working tree, commit or push repository changes, copy files to Windows Downloads, or submit to arXiv. A subsequent user instruction authorized committing the prepared v5 artifacts to the existing repository. The existing Lean checkpoint and its separately reported verification remain distinct from these manuscript checks.

For the repository delivery, the reviewed TeX and PDF bytes are unchanged. The connected GitHub service is used because this session cannot access the WSL checkout, and an SSH Git read failed to resolve github.com. The update preserves the existing main history and repository visibility. The Windows path `/mnt/c/Users/fleng/Downloads` is unavailable here; no Downloads copy or WSL working-tree check is claimed. The reports remain available in the delivered bundle and are retained in this repository.

Local LaTeX compilation and visual inspection succeeded. The arXiv compilation service itself was not invoked. The literature finding is bounded: no earlier resolution of the exact conjecture was identified, with Medium confidence in that negative finding; it is not an exhaustive novelty certificate.
