# arXiv source package, manuscript v12

Prepared 31 October 2026. No arXiv upload has occurred.

Upload `Dosen-Petric-Maximality-v12-arxiv-source.tar.gz`. Its four root members
are `main.tex`, `main.bbl`, `references_v12.bib` and `palomar_v12.bib`.
The archive contains no proof build outputs, reports or third-party source
PDFs. It has been extracted and compiled to 13 pages; its layout text and
bibliography agree with the manuscript release.

Use pdfLaTeX. A rebuild with bibliography regeneration is:

```
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

`submission-fields.json` contains proposed form fields and release hashes.
`abstract.txt` and `comments.txt` contain copyable text.
Primary category: math.CT; cross-list: math.LO. The author selects an
arXiv-supported distribution license and checks the arXiv server preview.
No new license selection is recorded here.

The registered formalization is PALOMAR-2026-10-30-000014 v1, proof source
`2e771844077fd8cebfbe365230f13d4dd13a75b1`. The supplied Palomar BibTeX entry
is unchanged. This manuscript revision does not initiate another registration.

See [the report](../../docs/MANUSCRIPT_V12_REPORT.md),
[the line review](../../docs/reviews/V10_LINE_REVIEW_2026-10-31.md),
[the hostile review](../../docs/reviews/V12_HOSTILE_REVIEW_2026-10-31.md), and
[validation](../../provenance/manuscript-v12-review-20261031/validation.json).
