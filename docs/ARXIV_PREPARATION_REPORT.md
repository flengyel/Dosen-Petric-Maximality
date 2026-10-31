# arXiv preparation — manuscript v10

The current 13-page manuscript is v10, dated October 31, 2026. Its source package
is `submission/arxiv-v10/Dosen-Petric-Maximality-v10-arxiv-source.tar.gz`, containing
only `main.tex`, identical to
`manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v10.tex`.
The author preview PDF has the same manuscript basename with `.pdf`.

V10 publishes the terminology revision: the signed-literal generator class,
the general theorem's hypotheses and their application to the presentation,
interpretations preserving the specified operations, shorter qualifiers and
the Appendix B heading. Mathematical definitions, statements, proofs, diagrams,
labels, source citations, MSC codes and authorized disclosure are retained.
The front page and PDF metadata identify v10. Every manuscript revision must
increment the version number; this author instruction is recorded in AGENTS.md.

The original v9 source, PDF and upload package are restored byte for byte from
678ea6d. The temporary editorial snapshot under the old number remains in Git
history at fd29c0c; its detailed writing report is historical evidence. Earlier
versions are untouched. The registered proof source remains
`2e771844077fd8cebfbe365230f13d4dd13a75b1`, comparator.json, Lean 4.35.0.
The Palomar citation is preserved; no new intake or registration was performed.

Both v10 TeX builds succeeded with 13 pages, resolved citations/references and
no overfull boxes. Four duplicate-destination warnings for equation.6 and one
underfull bibliography line are inherited from the baseline. No Lean rebuild
was needed. The archive's sole source member, abstract fields and SHA-256 fields
were checked against the exact revised manuscript and PDF.
See [v10 report](MANUSCRIPT_V10_REPORT.md) and
`provenance/wsl-v10-20261031/`. Full local logs/renders are retained in
`.codex-work/v10-20261031/`.

Use `submission/arxiv-v10/submission-fields.json`, `abstract.txt` and
`comments.txt` for the form: math.CT, cross-list math.LO; MSC 2020 Primary 03G30,
Secondary 03F07 and 18A32. The author selects the arXiv distribution license.
No arXiv upload or submission has occurred. The arXiv server preview remains
a later step in the author's submission account. Deliveries from committed
bytes, exact Downloads paths and SHA-256 values are recorded in the v10
delivery register. Differing older Downloads copies are preserved.
