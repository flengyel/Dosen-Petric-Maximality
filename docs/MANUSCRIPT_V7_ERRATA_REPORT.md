# V7 errata appendix: implementation and verification

The author-requested Appendix C is complete in manuscript v7, dated
28 October 2026. It contains the exact supplied TeX and introduction roadmap
sentence. The reviewed v6 source/PDF and the v4/v5 pairs are preserved.
The manuscript work was completed before continuing the Lean cut-elimination
construction; no new Lean elimination theorem is claimed by this report.

## Exact source and mathematical scope

Active source: manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.tex,
SHA-256 70b4f82c03e165e6a6da36d869968531a509341b93f90eedde964506568c8e96.
Active PDF: manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v7.pdf,
SHA-256 957048538137ef085c0a581b399272db753377b76c6a83c1adc307ad8b2e256a.

The input instruction is docs/CODEX_AFTER_5C72A84_CUT_ELIMINATION.txt at
1376bcbe1d1a8aa8eb69142f85401f078cfc14c9. Its exact Appendix C block is inserted
after Appendix B and before the accepted disclosure. The supplied roadmap
sentence appears before the September-2007 printed-pagination convention.
The date changes to 28 October 2026. A clear page before Appendix C keeps its
two corrections together. These are the only differences from v6.

The primary source is Došen–Petrić, Proof-Theoretical Coherence, revised
September 2007, SHA-256
e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Rendered printed pp.260–262 were rechecked locally: p.260 reverses the
recursive-rank inequality in (w gamma 3); p.262 omits the right-side qualification
in (w disjunction 1), while the analogous p.261 passage includes it. Appendix C
states r' < r and right rank one, with total rank at least two. It uses the
existing DP bibliography entry and defines r and r' before using them.

These are corrections to the external source's wording. They are not a
counterexample to cut elimination or a newly established error in v6.
The Appendix C explanations enter the claim ledger. Their concrete blocked-cut
Lean correspondence remains open; the existing native head-cut positivity
results are retained. The full-paper contract now fixes v7 as all v6 content
plus the authorized appendix, with no reduction in the original obligations.

## Local checks

The final latexmk PDF build exited zero, with references/citations resolved and
no LaTeX/package warnings, overfull boxes or underfull boxes. Both build attempts
and their actual exits are retained; the first layout split Appendix C across
pages, and the final page break resolves that layout issue.

The final PDF has thirteen pages. All pages were inspected as a contact sheet;
the diagram-bearing pages and Appendix C were also inspected at readable scale.
Appendix C and the unchanged disclosure are on p.12, and the references start
on p.13. Source comparison confirms all ten TikZ diagrams, the entire Appendices
A–B, disclosure and bibliography are unchanged. V4/v5/v6 pass their existing
SHA-256 values. The final source diff, renderings, TeX log, auxiliary labels,
PDF text and machine-readable check record are in provenance/wsl-manuscript-v7.

Current pointers, full-paper source/PDF anchors, statement/coverage/correspondence
maps, correction ledger, validation, README and continuation were updated
together. No unchanged Lean baseline rebuild is claimed or required for this
bounded TeX addition. The preceding checked proof scope remains 442 Lean files
and 11,105 audited declarations. Later changed Lean source requires its own
strict, signature, dependency and control checks.

## Retention and delivery

Retain this report under docs/ and its two reviews under docs/reviews/.
Deliver their committed bytes, the v7 TeX/PDF, and the three 1376bcb successor
artifacts to /mnt/c/Users/fleng/Downloads, preserving differing destinations.
The actual paths, SHA-256 comparisons, source commit, local/origin/live SSH
agreement and preserved stash are recorded after the commit in
.codex-work/gentzen-cut-elimination/V7_POST_COMMIT_DELIVERY.json.
The preceding six clean-cut deliveries remain complete.
No public release, submission, author contact or license change is performed.
