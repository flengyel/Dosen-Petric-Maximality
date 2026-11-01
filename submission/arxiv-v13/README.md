# arXiv source package, manuscript v13

Prepared 31 October 2026. No arXiv upload has occurred.

Upload Dosen-Petric-Maximality-v13-arxiv-source.tar.gz. Its four root members
are main.tex, main.bbl, references_v13.bib and palomar_v13.bib.
The archive contains no proof build outputs, reports or third-party source
PDFs. It was independently extracted and compiled to 14 pages; its layout text
and bibliography match the manuscript release.

Use pdfLaTeX. To regenerate the bibliography:

```
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

submission-fields.json contains proposed fields and release hashes.
abstract.txt and comments.txt contain copyable text. Primary category: math.CT;
cross-list: math.LO. The author selects an arXiv-supported license and checks
the arXiv server preview. No new license selection is recorded here.

The registered formalization remains PALOMAR-2026-10-30-000014 v1, source
2e771844077fd8cebfbe365230f13d4dd13a75b1. The supplied Palomar BibTeX entry
is unchanged. This revision does not initiate another registration.

See [the report](../../docs/MANUSCRIPT_V13_REPORT.md),
[statement review](../../docs/reviews/V13_STATEMENT_REVIEW_2026-10-31.md),
[literature review](../../docs/reviews/V13_LITERATURE_REVIEW_2026-10-31.md),
[hostile review](../../docs/reviews/V13_HOSTILE_REVIEW_2026-10-31.md), and
[validation](../../provenance/manuscript-v13-review-20261031/validation.json).
