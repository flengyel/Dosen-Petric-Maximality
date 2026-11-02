# Manuscript v19: citation, qualifiers and comparison definitions

1 November 2026. Input: v18 at e2e9c85f4b33171594eab5608bdeb1d96014b8a7.
Output: v19, 23 pages. The author's later instructions are incorporated together:
use the supplied version-2 Palomar BibTeX, omit “particular” around Appendix E,
review empty adjectives throughout, and put each D.5 c-arrow formula and type
on one line. V18's revised abstract is preserved.

Current files: [PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v19.pdf),
[TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v19.tex),
[source archive](../submission/arxiv-v19/Dosen-Petric-Maximality-v19-arxiv-source.tar.gz)
and [BibTeX](../manuscript/palomar_v19.bib). No arXiv upload has occurred.

## Changes

The Palomar entry matches the author's supplied bytes, with a terminal newline.
Both manuscript citation keys now use palomar-2026-10-30-000014-v2. The
Formalization bibliography note identifies the registered source as
5dbee39bea09539bd130f729e82636419f71f920; its mathematical-source revision
630c4b6e47da16a1434476a211fd29ce6adc5569 remains. All other bibliography content
is preserved. The submission version, URL, source and comments agree on v2.
Earlier v1-cited releases and both immutable registered sources remain.

All 49 distinct declaration links now target the version-2 source. Each path,
source hash, declaration opening and line was checked locally. Two lines move:
Palomar.PrimitiveCongruence from 13 to 14, and its Closed property from 28 to 31.
All 49 URIs occur in the PDF annotations; no version-1 source URI remains.
The five selected statement types and proof code are unchanged.

The qualifier review makes eleven prose edits, including the two “particular”
deletions. It removes “complete” before the substituted relation, “resulting”
before the defined signs, three redundant “required” qualifiers and two
redundant “corresponding” uses. The two “explicit” descriptions are replaced
by the inverse terms or named appendices; “several intermediate equations”
is replaced by the coherence argument in D.5. The four proof-table steps are
identified directly. The heading remains “Inverses of q_A and e_A”.

Qualifiers expressing mathematical content remain: naturality, the canonical
product/coproduct comparisons, direct images of relations, original occurrence
coordinates, specified operations, uniqueness, universal quantification, and
the hypotheses and types. Their contextual reasons and every edit are recorded
in the [qualifier decisions](../provenance/manuscript-v19-review-20261101/adjective-decisions.json).

The D.5 comparison display has two lines: each definition and its complete
source/target type occupies one line. Only alignment markup changes. The
existing font size is used without scaling. The shorter display moves the
start of common atomic factorization onto p.19; its account now spans pp.19–20,
and the active claim map is updated. The one-line u_A path is retained.

## Review and verification

The [writing review](reviews/V19_WRITING_REVIEW_2026-11-01.md) covers the
whole-source qualifier search and contextual prose pass, the citation/source
correspondence and the display. It uses the mathematical-writing workflow and
retains the v18 Knuth–Larrabee–Roberts consultation at its recorded scope.
No new mathematical milestone or independent proof-body audit is claimed.

Undoing the 62 recorded citation, URI, prose and layout edits and restoring
suffixes recovers v18 byte for byte. The abstract, seven statement bodies,
twelve numbered displays, thirteen diagrams and 34 labels remain identical.
The c-arrow mathematical tokens are identical after removing alignment markup.
All seventeen footnotes, Appendix A and its main-text references, both proof
routes, MSC codes and the authorized disclosure remain.

All four manuscript commands and three extracted-archive passes returned zero.
The archive contains main.tex, main.bbl, references_v19.bib and palomar_v19.bib.
Its PDF layout text matches the manuscript's 23 pages. Final logs have no
reference/citation, box or duplicate-destination warnings. All pages were viewed
on six contact sheets; pp.19, 20 and 23 were also inspected individually.
The comparison lines fit, Appendix E's opening omits “particular”, and the
bibliography displays version 2 and the matching source revision.

All 139 preceding release files and 857 registered proof/input blobs are
preserved, as is the stash. No Lean source, frozen input, verification script
or workflow changes. No successful proof/kernel/Palomar check or registration
is repeated. Credentials and unregistered service material remain ignored.
The prior preparation report is retained at [the v18 checkpoint](history/ARXIV_PREPARATION_V18_2026-11-01.md).
See [validation](../provenance/manuscript-v19-review-20261101/validation.json)
for hashes, exits, field agreement and preservation evidence.

Reports and release files are delivered from committed bytes to
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v19-20261101/`.
The [receipt](../provenance/manuscript-v19-review-20261101/delivery-receipt.json)
records exact paths and byte/SHA-256 checks. Differing copies are preserved.
Main and the receipt commit are pushed and the remote ref verified before
readiness is reported.
