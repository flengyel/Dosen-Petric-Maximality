# arXiv source package, manuscript v14

Prepared 1 November 2026. No arXiv upload has occurred.

Upload Dosen-Petric-Maximality-v14-arxiv-source.tar.gz. Its four root members are
main.tex, main.bbl, references_v14.bib and palomar_v14.bib.
The archive was independently extracted and compiled to 14 pages; its
layout text matches the released manuscript exactly. No reports or third-party
source PDFs are included.

Use pdfLaTeX. To regenerate the bibliography:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    bibtex main
    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

submission-fields.json records proposed fields and file hashes. abstract.txt
contains the exact TeX abstract; comments.txt supplies copyable comments.
Primary category: math.CT; cross-list: math.LO. MSC 2020: Primary 03G30;
Secondary 03F07, 18A32. The author selects an arXiv-supported distribution
license and checks the server preview in the submission account.

The supplied Palomar BibTeX entry is byte-identical to v13 and cites version 1,
source 2e771844077fd8cebfbe365230f13d4dd13a75b1. That record remains available.
Registry version 2 is separately registered at source
5dbee39bea09539bd130f729e82636419f71f920. This editorial release does not alter
registered inputs or request another registration.

See [the report](../../docs/MANUSCRIPT_V14_REPORT.md),
[hostile review](../../docs/reviews/V14_HOSTILE_REVIEW_2026-11-01.md),
[writing review](../../docs/reviews/V14_WRITING_REVIEW_2026-11-01.md), and
[validation](../../provenance/manuscript-v14-review-20261101/validation.json).
