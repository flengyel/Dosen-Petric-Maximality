# V25 fixed-release paper

2 November 2026. Release name: `dosen-petric-v25-palomar-v3`. The paper has 23 pages.
It is prepared for the intended Palomar version-3 update; registration remains
pending. This report does not assert that the candidate has passed service
verification or that the registry has issued version 3.

## Changes

All 56 Lean-source hyperlink occurrences now use the preassigned release tag.
The 49 distinct declaration paths and line anchors remain unchanged. The
formalization bibliography identifies the same release, and the registry
bibliography is prepared for the explicit version-3 record. It does not use
an unversioned latest-entry URL. The mathematical text, abstract, hypotheses,
proofs, equations, diagrams, labels and visible declaration names are unchanged.

The release name was chosen before the commit was made. The completed paper,
metadata and source package belong to one candidate commit. The fixed tag must
point to that commit; Palomar receives its full SHA. This removes the need to
put a commit's own hash into its contents. Never move or reuse this tag.

The version-3 bibliography is prepared candidate text, not a citation supplied
by a completed registration. The paper is ready for final publication only
after the actual version-3 record is verified at the tagged commit. If the
service issues a different version, stop final publication and preserve this
tag; do not silently change the reference to a floating latest link.

## Verification

The manuscript and independently extracted four-file source archive pass
pdfLaTeX/BibTeX/pdfLaTeX/pdfLaTeX. Their 23-page text, text coordinates and
bibliographies match. Only the title-page date/version and bibliography have
visible changes; those two pages were inspected. All other page text and
coordinates match the previously inspected v24 PDF. The PDF itself contains
all 56 fixed-tag source links. There are no unresolved references/citations
or overfull lines. One unchanged underfull bibliography paragraph remains
within the margins.

An independent link audit confirms all 49 declaration path/line targets and
the matching 29 source-module blobs against the registered manifest. The
mathematical source is identical to v24 after reversing only the version/date,
reference-key and hyperlink-ref changes. No new mathematical review, Lean build
or kernel replay is claimed for this link-only revision. The writing check
preserves the reviewed v24 prose and keeps release instructions outside it.

## Files

- [PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v25.pdf)
- [TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v25.tex)
- [Source package](../submission/arxiv-v25/README.md)
- [Validation](../provenance/manuscript-v25-release-20261102/validation.json)
- [Source diff](../provenance/manuscript-v25-release-20261102/v24-to-v25.diff)
- [Release manifest](../provenance/palomar-v3-candidate/release-v25.json)
- [Codex handoff](PALOMAR_V25_CODEX_HANDOFF.md)

V24 and all earlier manuscripts and registered v1/v2 snapshots remain preserved.
No arXiv upload has occurred. Windows/WSL Downloads is unavailable in this
environment; the handoff gives the corresponding local delivery instructions.
