# V26 manuscript revision

13 November 2026. *Maximality of the Došen–Petrić Boolean Category*, 23 pages.

## Changes

Appendix D.5 now explains the construction of the common factorization. It
identifies the induction on eta/epsilon constructors, the source and target
extensions, the use of the diagonal and projections after factoring the
conjunction of the two terms, and the endpoint zero endomorphisms that give
the asserted direct-image relations.

One sentence opening Appendix E identifies the proof dependencies: the inverse
identities use Boolean Coherence, while the split-comparison identities needed
to establish coherence follow directly from the presentation equations.

The two additions contain no reference to a review or revision procedure.
The current version, date, PDF metadata, source package, README, continuation,
corrections record, and correspondence map identify v26. The preceding
continuation is preserved byte for byte under `docs/history/`.

## Reviews

The [focused hostile review](reviews/V26_HOSTILE_REVIEW_2026-11-13.md) checked
the additions against the Lean construction and its proof dependencies. Its
factor/summand terminology correction is incorporated; no unresolved defect
was established in the additions.

The [mathematical-writing review](reviews/V26_WRITING_REVIEW_2026-11-13.md)
consulted Knuth–Larrabee–Roberts, §1 and §§4–5, and read the complete source
for notation, definition order, economy and continuity. The suggested paragraph
breaks are incorporated. No further prose correction was required in the two
additions.

## Build and preservation checks

The manuscript and independently extracted four-file source archive both pass
pdfLaTeX, BibTeX, pdfLaTeX, pdfLaTeX. Their text and word coordinates match on
all 23 pages, and their generated bibliographies are byte-identical. Neither
build has an unresolved citation, unresolved reference, or overfull box. One
underfull bibliography paragraph remains, with no text outside the margins.

All 23 pages were inspected in page overviews; pages 1 and 20–22 were inspected
at higher resolution. These are the only pages whose text or coordinates differ
from v25. The title page has the new date/version; pages 20–22 contain the
additions and their pagination consequences. The remaining 19 pages have
unchanged text and coordinates.

Automated comparison confirms preservation of all seven theorem-like statements,
twelve numbered displays, thirteen TikZ diagrams, thirty-five labels, and all
56 source-link occurrences. Appendix D.4 is unchanged. The two bibliography
databases and generated bibliography retain their v25 contents. No Lean source,
frozen registry input, earlier manuscript, or earlier upload package was changed.
No new Lean build or registry submission was required or performed.

The [validation record](../provenance/manuscript-v26-20261113/validation.json),
[source diff](../provenance/manuscript-v26-20261113/v25-to-v26.diff), build exit
records, and final logs are retained under `provenance/manuscript-v26-20261113/`.

## Registered source and delivery

The paper retains Palomar registration PALOMAR-2026-10-30-000014 version 3,
commit `76a4ea71f257746bb6ea2cb2e686e85914c7347c`, with fixed source tag
`dosen-petric-v25-palomar-v3`. The tag identifies the registered Lean source
and the v25 snapshot. V26 is a later exposition revision; it does not create
a new registry version or move that tag. The completed registration is recorded
in [the v3 report](PALOMAR_V3_REGISTRATION_REPORT.md).

- [PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v26.pdf)
- [LaTeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v26.tex)
- [Complete source package](../submission/arxiv-v26/README.md)

The source archive includes `main.tex`, `main.bbl`, `references_v26.bib` and
`palomar_v26.bib`. No arXiv submission was made. Windows/WSL Downloads is not
mounted in this environment, so no copy to `/mnt/c/Users/fleng/Downloads` was
possible; the reports are retained in the repository and delivered with the
manuscript files.
