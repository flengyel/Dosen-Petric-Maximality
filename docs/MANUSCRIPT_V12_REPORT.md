# Manuscript v12: hostile mathematical and prose review

31 October 2026. The review began with v10 at
`89ebf8390f8906a6c2529cea6f910c65ece8889f`. Main advanced to v11 at
`97d728820d87f712c32c77dcb29fcd6fa0856e3d` during the review. V12 incorporates
the remaining corrections after comparison with that release. V11 and all
earlier releases are preserved.

## Result

The complete manuscript was read: the introduction and its literature
discussion, proofs, displays, diagrams, appendices and bibliography. The review
uses Knuth, Larrabee and Roberts, *Mathematical Writing*, and the author's
request for Došen–Petrić's direct mathematical exposition.

V12 replaces vague descriptions by specified maps, equations and hypotheses.
It states the nonempty-generator hypothesis in the abstract, specifies the
occurrence-selection result cited, identifies the class of Boolean categories
in the Lamarche–Straßburger theorem, and names the composite in the
Führmann–Pym comparison. It gives explicit pairing/copairing types, describes
coordinate maps by equations, and states both endpoint patterns in contextual
substitution. Terms with a definite use, including structural induction on a
formula, remain.

No mathematical defect in the formal proof was established. The added types
are an exposition change. The registered source already defines

```
pair   : Term P X A → Term P X B → Term P X (.conj A B)
copair : Term P A X → Term P B X → Term P (.disj A B) X
```

See [PresentationSyntax.lean](https://github.com/flengyel/Dosen-Petric-Maximality/blob/2e771844077fd8cebfbe365230f13d4dd13a75b1/DosenPetric/PresentationSyntax.lean#L71-L77).
Its Git blob is `b36d96b3ad77cc87c473defc59bbbb799f575d15` at both the
registered source and v11. Calling the manuscript's implicit notation a missing
formal type would be incorrect.

## Review records

- [Line review](reviews/V10_LINE_REVIEW_2026-10-31.md): 77 consecutive ranges
  cover all 1003 original lines, followed by the v11 reconciliation and source
  comparisons. Complete coverage does not mean every line required an edit.
- [Hostile review](reviews/V12_HOSTILE_REVIEW_2026-10-31.md): blockers, major
  and minor findings, consistency, acceptance conditions and limits.
- [Exact source diff](../provenance/manuscript-v12-review-20261031/v11-to-v12.diff).
- [Source manifest](../provenance/manuscript-v12-review-20261031/primary-sources.json):
  primary URLs, checked locators and SHA-256 hashes of the inspected author PDFs.

The source comparisons include Došen–Petrić's book and four papers,
Lamarche–Straßburger, Straßburger, Führmann–Pym, and the cited occurrence
notation. Appendix C was checked against the source pages and rank definitions.
No exhaustive novelty search or new kernel replay is claimed.

## Preservation and validation

The [validation record](../provenance/manuscript-v12-review-20261031/validation.json)
records byte-for-byte preservation from v11 of seven theorem/lemma/proposition/
corollary statements, twelve numbered displays, ten TikZ diagrams, thirty
labels, Appendices B and C, and the authorized AI disclosure. The exact supplied
Palomar BibTeX is unchanged. Both proof routes and the MSC codes remain.

The manuscript builds to 13 pages. All final pages were rendered and visually
inspected. Final logs have no citation/reference, box or duplicate destination
warnings. Hidden equation destination names now include the section; visible
equation numbers are unchanged. PDF metadata identifies v12. Both Palomar links
contain the supplied URI and version.

The exact four-file archive was extracted and compiled independently. Its
members match the staged files, its bibliography matches the manuscript
bibliography, and its extracted layout text matches the manuscript PDF.
Compressed final logs and release hashes accompany the validation record.

No Lean source, comparator, toolchain or frozen input changes. The registered
source remains `2e771844077fd8cebfbe365230f13d4dd13a75b1`,
PALOMAR-2026-10-30-000014 v1. No new verification, intake, registration or arXiv
upload is claimed.

## Files and delivery

Current files are the v12 TeX, PDF, BBL and two BibTeX databases in
`manuscript/`, and `submission/arxiv-v12/`. The prior preparation report is
preserved at `docs/history/ARXIV_PREPARATION_V11_2026-10-31.md`.

This report, `docs/ARXIV_PREPARATION_REPORT.md`, and the two review reports
are retained in the repository. The author's WSL checkout and
`/mnt/c/Users/fleng/Downloads` are unavailable here. New Windows copies have
not been made or verified. Local Codex can deliver the committed bytes,
preserving differing existing files and checking SHA-256. The previous v11
receipt describes only its own completed deliveries.
