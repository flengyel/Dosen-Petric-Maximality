# Manuscript v17: specific map names and the one-line u_A path

1 November 2026. Input: v16 at 7a5d1cf43aaf1cd5d7497fd5c75034839dedb030.
Output: v17, 23 pages. The author requested that the u_A path on p.20 occupy
one line and that the adjective “structural” be removed or replaced by
specific mathematical terms throughout. The author also confirmed that
Appendix A and its main-text connections must remain.

Current files: [PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v17.pdf),
[TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v17.tex),
[four-member source archive](../submission/arxiv-v17/Dosen-Petric-Maximality-v17-arxiv-source.tar.gz).
No arXiv upload has occurred.

## Implemented edits

| Location | Revision |
| --- | --- |
| Section 3, p.4, sign preservation | Name identities, associativity/symmetry maps, projections/injections, diagonals/codiagonals, mix, dissociativity and unit maps. |
| Section 3, p.6, substituted relation | Name those generator families and the double-negation/De Morgan maps. Use “tagged relations” for the general action on blocks; diagonals and projections need not be graphs of total functions. |
| Appendix A.3, p.13 | Replace “structural induction on the formula” by “induction on the formula”. |
| D.5, pp.18–19 | Name the products, coproducts, units, associativity/symmetry maps, mix and dissociativity that share notation; specify the constituent maps and operations in the split comparisons. Two edits. |
| Appendix E title, p.20 | “Inverses of q_A and e_A”, naming the particular arrows whose inverses are constructed. The displayed associativity/symmetry maps remain auxiliary notation. |
| E.1, p.20 | Put A→A∧top→A∧(bottom∨top)→S_A on one display line at the existing font size. All objects, arrows and labels remain. |
| E.3, p.22 | Name the product, coproduct, associativity, symmetry, dissociativity and mix equations used. |

These are eight recorded edits, including all seven visible occurrences of
“structural”. The word remains only inside unprinted cross-reference keys;
those keys and all Lean identifiers are preserved. The author's terminology
instruction is recorded in AGENTS.md and the correction ledger for future work.

Appendix A remains part of the mathematical contract. Section 3 refers to
A.1–A.2 for blocks and ordinal coordinates, and Proposition 4.2 points to
A.3 for substitution in K_A. The full finite-ordinal calculation establishes
the exact correspondence with Došen–Petrić's substitution operation; the
maximality deduction uses the block substitution established in Section 3.
The author's confirmation is recorded in the claim map and continuation.

## Verification and preservation

The [focused writing review](reviews/V17_WRITING_REVIEW_2026-11-01.md) applies
the mathematical-writing skill to these prose/layout edits. It consults the
retained Knuth–Larrabee–Roberts source and reuses the broader v16 review at
its recorded scope. No new mathematical milestone or independent proof-body
audit is claimed, and the hostile review is not represented as repeated.

Undoing the eight edits and restoring the version/bibliography suffixes
recovers v16 byte for byte. All seven statement bodies, twelve numbered
displays, thirteen diagrams and 34 labels are identical. All equations and
the three-step u_A path preserve their expressions; the path's alignment
markup changes. The bibliography databases and generated bibliography are
byte-identical to v16. Both proof routes, the Lean reading guide, all seventeen
footnotes, 49 source links, MSC codes and authorized disclosure remain.

All four manuscript build commands and all three extracted-archive passes
returned zero. The archive has exactly main.tex, main.bbl, references_v17.bib
and palomar_v17.bib. Its PDF layout text matches the manuscript. Final logs
have no citation/reference, box or duplicate-destination warnings. The PDF
contains no visible “structural” and retains all 49 exact declaration URLs.
All 23 pages were inspected on six contact sheets; p.20 was additionally
viewed individually. The u_A path fits on one line without scaling.

All 111 preceding manuscript/package files are preserved. The 857 production
proof/input blob identities match the registered version-2 source, and the
stash remains dedfd8fc8cd49930e9a162d5be585215b062a43c. No Lean source,
registered input, verification script or workflow changes. No Lean/kernel/
Palomar check or registration is repeated. The prior preparation report is
preserved at [the v16 checkpoint](history/ARXIV_PREPARATION_V16_2026-11-01.md).

Exact edits, hashes, exits and preservation checks are in
[v17 provenance](../provenance/manuscript-v17-review-20261101/validation.json).
Reports, review and release files are delivered from committed bytes to
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v17-20261101/`.
The [receipt](../provenance/manuscript-v17-review-20261101/delivery-receipt.json)
records byte/SHA-256 verification and preserves differing copies. Completed
main and the receipt commit are pushed and the remote ref verified before
readiness is reported.
