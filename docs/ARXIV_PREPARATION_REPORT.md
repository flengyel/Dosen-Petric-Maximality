# arXiv preparation — manuscript v9

The 13-page manuscript and minimal TeX upload archive are ready following
verified Palomar registration [PALOMAR-2026-10-30-000014, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000014&version=1). No arXiv upload has
occurred. The source upload is
`submission/arxiv-v9/Dosen-Petric-Maximality-v9-arxiv-source.tar.gz`; it contains only `main.tex`, identical
to `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v9.tex`. All diagrams are inline TikZ and the bibliography is inline.
The PDF author preview is `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v9.pdf` and is outside the source archive.

## Authorized changes

V8 already had MSC 2020 **Primary 03G30; Secondary 03F07, 18A32**, and a ChatGPT
acknowledgment. V9 preserves those codes and expands the expressly requested
disclosure to cover Codex's development and checking of the Lean formalization,
with author responsibility for the mathematical claims and final text. It adds
the actual registry citation and updates the date to October 30, 2026.
At the original publication commit 44f2d68, reversing those four metadata edits
recovers the complete v8 source byte for byte. The subsequent 31 October terminology
refresh is recorded below; all prior manuscript versions remain preserved.
The registered Lean proof remains `2e771844077fd8cebfbe365230f13d4dd13a75b1`; v9 does not create a new proof
submission or replace the registered source snapshot.

## Original 30 October checks

Two PDFLaTeX passes returned exit 0 using pdfTeX 1.40.26 (TeX Live 2025/dev/Debian).
All cross-references and citations resolved. Rendered pages 1, 8, 12 and 13 were
inspected: front matter/MSC, registry-selection paragraph, Appendix C/disclosure,
and bibliography. PDF annotations contain the exact versioned registry URL.
The source archive was opened and its sole member compared byte for byte with
v9. No Lean source or pinned toolchain changed; completed Lean verification was
reused. The final TeX log has the disabled-shell-escape epstopdf notice and one
underfull bibliography line; no overfull box or unresolved reference was found.
Build logs and inspected images are under `.codex-work/arxiv-v9-20261030/`;
compact check records are in `provenance/wsl-arxiv-v9-20261030/`.

The [focused writing review](reviews/ARXIV_V9_WRITING_2026-10-30.md) records its
source consultation and actual scope. It does not claim a new mathematical
referee review of unchanged proofs.

## 31 October terminology refresh

The supplied editorial review is implemented in v9 and its matching arXiv source
and abstract fields. It clarifies the signed-literal generator class, the general
theorem's hypotheses and their verification for the presentation, and the model
corollary's operation-preserving interpretations. Redundant qualifiers are
removed and Appendix B is titled “Diagrams for three defining equations.”
The revised manuscript retains its October 30 date. Statements, proofs,
definitions, diagrams, labels, bibliography, disclosure and registered Lean
source citation are preserved.

The revised manuscript and identical arXiv main.tex both compiled successfully
to 13 pages. References/citations resolved; no overfull boxes occurred. Affected
pages were rendered and inspected. The four equation.6 duplicate-destination
warnings and one underfull bibliography line were reproduced from the exact
original source. This comparison qualifies the inherited log summary above.
No Lean rebuild or new registration was performed. The minimal source archive
still contains only main.tex, checked byte for byte against v9; source, PDF and
archive hashes in submission-fields.json were refreshed. No arXiv upload occurred.

See the [complete terminology report](reviews/V9_TERMINOLOGY_2026-10-31.md).
Compact checks are in provenance/wsl-v9-terminology-20261031/; full local logs and
page renders are retained under .codex-work/v9-terminology-20261031/.

## Form fields and next action

Use the title, Florian Lengyel author field, abstract and comments in
`submission/arxiv-v9/submission-fields.json`, with primary category **math.CT**,
cross-list **math.LO**, and the MSC codes above. Separate abstract/comments text
files are supplied for copying. Palomar is a registry; no journal reference or
DOI was invented. The author selects an arXiv-supported distribution license in
the form; the existing Apache-2.0 repository/manuscript approval is retained and
no new license was selected. ArXiv's server compilation/preview has not run.

Upload the source archive through the author's arXiv account and check its
preview before completing submission. The package follows the current
[arXiv TeX guidance](https://info.arxiv.org/help/submit_tex.html): no unused files,
PDF output or build intermediates in the archive. The publication order remains
Palomar registration, then arXiv submission, then the later Local connectedness
project. Exact committed-byte Downloads paths are recorded in the final
publication delivery receipt; differing prior copies are preserved.
