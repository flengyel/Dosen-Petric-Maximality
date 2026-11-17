# V27 abstract revision

Date: 17 November 2026.

V27 replaces the abstract with a six-sentence, 111-word account of the paper.
It states maximality, specifies the equality-or-totality dichotomy under the
operations on morphisms and uniform formula substitution, identifies the
disproved conjecture, summarizes the two proofs, and states the scope of the
Lean formalization.

The model-corollary sentence containing “such an additional equation” is omitted
from the abstract. Corollary 5.3 and its proof remain in the paper. The outline
states the premise and conclusion of the shared proof method; it no longer
refers to unnamed isomorphisms. The occurrence-coordinate correspondence is
listed among the formalization's contents without being described as a
dependency of maximality.

## Reviews

The [hostile review](reviews/V27_ABSTRACT_HOSTILE_2026-11-17.md) compared the exact
abstract with the theorem, the two proof routes, the relevant Lean declarations,
and the registered statements. The
[writing review](reviews/V27_ABSTRACT_WRITING_2026-11-17.md) examined its outline,
quantifiers, terminology, sentence structure and scope using the original
Knuth–Larrabee–Roberts text: Section 1, Wilf's Sections 27–29 (printed pp. 59–65),
and van Leunen's Section 36 (printed p. 87). Both reviews concern the abstract.
Their required changes are incorporated in the delivered wording.

## Validation

- The manuscript and an independent extraction of the source archive both pass
  pdfLaTeX, BibTeX, pdfLaTeX, pdfLaTeX.
- Both PDFs have 23 pages and identical extracted words and positions.
- There are no unresolved citations or references and no overfull boxes.
  One underfull bibliography paragraph remains, as in v26.
- All pages were inspected in contact sheets; the first page was inspected at
  reading size.
- Apart from the abstract, date, version and bibliography filename suffixes,
  the TeX source is byte-identical to v26. Both BibTeX databases are unchanged.
- The manuscript abstract, `abstract.txt`, and both representations in
  `submission-fields.json` agree. The metadata retains the selected arXiv license.

The checks and file hashes are recorded in
`provenance/manuscript-v27-20261117/validation.json`, with the build exits and
final logs. No Lean source or registered input changed; no new Lean build was
performed for this prose revision.

## Delivery

The replacement archive is
`submission/arxiv-v27/Dosen-Petric-Maximality-v27-arxiv-source.tar.gz`.
It contains the TeX source, generated bibliography and both BibTeX databases.
`submission/arxiv-v27/arxiv-metadata.txt` supplies the form entries.
The PDF is `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v27.pdf`.

Palomar version 3 and the fixed tag `dosen-petric-v25-palomar-v3` remain unchanged.
The v27 replacement was prepared but not uploaded to arXiv in this session.
The WSL Downloads directory is unavailable in this environment; reports are
retained in the repository.
