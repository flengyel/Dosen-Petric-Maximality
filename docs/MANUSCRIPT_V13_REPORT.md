# Manuscript v13: second complete review

31 October 2026. Input: v12 at
cbcd59ca1b9382bdcd0de8c648e4a351495ccf81. V13 implements the requested
second review of every statement and the broader literature search, using
Knuth–Larrabee–Roberts and Došen–Petrić's direct mathematical exposition.

## Findings and changes

The previous review missed a restriction in a cited result. Lemma 6 of
Isomorphic formulae concerns negation-free formulas; v12 did not state that
condition. V13 corrects it. The unrestricted reading fails for A=p and
B=¬p∨p if the negative target occurrence is selected. The paper's own isolation
argument already preserves signed literals, and no defect in that argument or
the registered formal proof was found.

The introduction now includes the CCC maximality antecedent, the book's
zero-identity distributive maximality/relative-maximality results, and proof-net
coherence with its Brauerian graph category. It explains why CCC maximality
does not apply to B. The FP inequality theorem and the cited Joyal hypothesis
are stated explicitly. The search found no prior proof of the exact Boolean
result in the inspected material; it does not certify priority.

The alternative collapse paragraph now supplies its intermediate equations:
jh≡jπ₂, equality of the injected projections, j≡ι₂!, h≡π₁ and equal
projections. These are existing deductions in Collapse.lean. Smaller edits
name the substituted pattern's skeleton, separate the positive and negative
contextual cases, and delete redundant wording. Standard terms with specified
objects, including structural induction on a formula, remain.

## Review records

- [Statement and line review](reviews/V13_STATEMENT_REVIEW_2026-10-31.md):
  89 consecutive ranges cover all 929 v12 lines; seven numbered statements,
  definitions, types and all unnumbered mathematical constructions are checked.
  The final 964-line v13 source was read continuously.
- [Literature review](reviews/V13_LITERATURE_REVIEW_2026-10-31.md): primary
  comparisons, omitted hypothesis, new antecedents and limits for every
  partially inspected candidate.
- [Hostile review](reviews/V13_HOSTILE_REVIEW_2026-10-31.md): anchored findings,
  counterexample, conditions and uncertainty log. No central mathematical
  blocker was established; no independent publication verdict is claimed.
- [Exact edits](../provenance/manuscript-v13-review-20261031/editorial-decisions.json)
  and [TeX diff](../provenance/manuscript-v13-review-20261031/v12-to-v13.diff).
- [Primary-source identities](../provenance/manuscript-v13-review-20261031/primary-sources.json)
  and [Lean source inspection](../provenance/manuscript-v13-review-20261031/lean-source-inspection.json).

## Validation and preservation

The [validation record](../provenance/manuscript-v13-review-20261031/validation.json)
records byte-for-byte preservation from v12 of all seven theorem/lemma/
proposition/corollary statements, twelve numbered displays, ten TikZ diagrams,
thirty labels, Appendices B and C, the authorized AI disclosure and the exact
supplied Palomar BibTeX. Both proof routes and the MSC codes are preserved.
The two new references bring the bibliography to thirteen cited entries.

The manuscript and independently extracted four-member source archive build
to 14 pages. Their layout text and bibliography match. All final pages were
rendered and visually inspected. Final logs have no citation/reference, box or
duplicate destination warnings. PDF metadata identifies v13, and both Palomar
links retain the supplied URI and version. Hashes and compressed final logs
are retained with the validation record.

No Lean source, comparator, toolchain or frozen registered input changes.
No new Lean/kernel replay, Palomar intake, registration or arXiv upload occurred.
The registered proof source remains 2e771844077fd8cebfbe365230f13d4dd13a75b1,
PALOMAR-2026-10-30-000014 v1. The relevant source endpoints were inspected;
earlier verification remains tied to its recorded commit and scope.

## Files and delivery

- [V13 PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v13.pdf)
- [V13 TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v13.tex)
- [Upload package](../submission/arxiv-v13/README.md)
- [Current preparation report](ARXIV_PREPARATION_REPORT.md)

All earlier manuscript versions, packages and review reports are preserved.
The prior preparation report is retained at
docs/history/ARXIV_PREPARATION_V12_2026-10-31.md as an exact byte copy. Its
original relative links work in the [v12 report at its original path](https://github.com/flengyel/Dosen-Petric-Maximality/blob/cbcd59ca1b9382bdcd0de8c648e4a351495ccf81/docs/ARXIV_PREPARATION_REPORT.md).
The explicit release write set
and hashes are in the v13 provenance directory.

The author's WSL checkout and /mnt/c/Users/fleng/Downloads are unavailable here.
New Windows copies have not been made or byte-verified. The repository paths
above are the retained report copies. Local Codex can deliver the committed
bytes, preserving differing existing files and checking SHA-256. A previous
delivery receipt does not certify delivery of these new v13 artifacts.
