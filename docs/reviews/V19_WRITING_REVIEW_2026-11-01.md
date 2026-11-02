# Mathematical-writing review of manuscript v19

1 November 2026. Author-side AI-assisted review applying the mathematical-writing
skill. Input: v18 at e2e9c85f4b33171594eab5608bdeb1d96014b8a7. Output: v19,
23 pages. The review checks qualifiers throughout the manuscript, implements
the author's citation and Appendix E corrections, and checks the D.5 display.
No unresolved prose, citation or layout defect was identified in that scope.

## Source and actual outline

Knuth, Larrabee and Roberts, Mathematical Writing, remains the governing source.
The [official report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)
and the v18 source-consultation record supply the consulted context. The
author's specific terminology and layout instructions govern these edits;
they are not attributed to a word blacklist in the book. The mathematical
qualifications are judged in context.

The order is retained: abstract; Introduction; category and main theorem (§2);
occurrences/substitution (§3); isolation and all K_A (§4); q/e collapse and
model corollary (§5); formalization, fold and union (§6); A.1–A.3 occurrence
maps, ordinals and shared variables; B diagrams; C source errata; D.1–D.5 terms,
reading Lean, selected declarations, congruence correspondence and coherence;
E.1–E.3 q/e inverses and split comparisons; disclosure and bibliography.
The v18 abstract remains nine sentences and 171 words. No reorganization is
proposed. Earlier paragraph-function records remain applicable, with the
revised provenance sentence identifying E's inverse terms and D.5's argument.

## Qualifier and layout audit

| Anchor | Wording assessed | Action and mathematical reason |
| --- | --- | --- |
| §3 p.4 | “resulting signs” | Omit “resulting”: the sign function is already defined. |
| §3 p.6 | “complete substituted relation” | Omit “complete”: the displayed equivalence already gives every pair in the relation. |
| §4 p.7; A.3 p.13 | Three “required” qualifiers | Omit them where the equations or typed zero have already been identified. |
| §5 p.8; E p.20 | “these particular arrows”; “the particular arrows” | Omit “particular”; the formulas, lemma reference and q_A/e_A title identify the arrows. |
| §6 pp.9,11 | “explicit inverse terms”; “several intermediate equations”; “explicit inverses” | Name Appendix E's inverse terms and D.5's coherence argument, and say the short proof uses the inverse terms. No construction or proof step is removed. |
| §6 p.9; D.2 p.17 | “corresponding source declarations”; “corresponding steps” | Remove the redundant first qualifier and identify the four proof-table steps in the second passage. |
| D.5 p.19 | c definitions broken before their types | Put each formula and type on one line, preserving all mathematical tokens and font size. |

The following are substantive qualifications, retained after contextual checks:
natural isomorphisms satisfy naturality equations; canonical comparisons are
determined by the product/coproduct data; direct images are images under the
displayed occurrence embeddings; original positions refer to coordinates before
normalization; specified products and operations are the chosen data preserved
by interpretations. Unique and arbitrary express quantifiers, and nonempty,
finite, parallel, distinct, positive and negative specify hypotheses or types.
“Remaining” excludes a stated list; “corresponding” is retained where it matches
tagged copies or selected cut ranks. “In particular” marks a specialization.
Bibliography titles and immutable source identifiers are preserved.

No hypothesis, type, sign, equation direction or coordinate distinction is
deleted. The whole-source candidate search was checked in context across the
abstract, exposition and appendices. The decisions record gives the before/
after strings and reasons, rather than treating a lexical search as a proof
that every adjective is empty.

## Citation and definition correspondence

The supplied BibTeX is used exactly, with a terminal newline. Both citation
keys, the registered-source bibliography note, comments and submission fields
refer to Palomar version 2 and source 5dbee39bea09539bd130f729e82636419f71f920.
All 49 declaration targets were resolved at that source. PrimitiveCongruence
and Closed have new line anchors, 14 and 31; all other line numbers remain.
The selected maximality header still matches the registered type, including
nonemptiness, implicit formulas and both term hypotheses. No new selection,
registration or proof verification is claimed.

The D.5 comparison types and equations retain their directions: c-wedge s=id
and t c-vee=id. Both formulas/types fit on one line each in the rendered page.
The common factorization now begins on p.19 and continues on p.20; the claim
map reflects that range. Appendix E's heading already names q_A/e_A; its
opening and the Section 5 pointer now omit the redundant qualifier.

## Verification and limits

Undoing the 62 recorded edits and suffixes recovers v18 exactly. All seven
statement bodies, twelve numbered displays, thirteen diagrams, 34 labels,
seventeen footnotes, the abstract, Appendix A and its main-text references,
both proof routes and disclosure remain. The c display's normalized mathematical
tokens are unchanged. The bibliography changes only in the supplied v2 entry
and matching registered-source note. The PDF contains all 49 new source URIs.

Manuscript and independently extracted archive compile to matching 23-page
text without final reference/citation, box or duplicate-destination warnings.
All pages were inspected on six contact sheets; pp.19, 20 and 23 were also
viewed individually. Metadata, both abstract forms and version-2 fields agree.
The source and prior-release preservation checks pass.

This is a prose/correspondence/layout review, not a new literature search,
hostile review, independent proof-body audit or Lean/kernel/Palomar check.
The arXiv server preview is uninspected because no upload has occurred.
The release provenance records edits, qualifier decisions, source lines,
exits and hashes; the delivery receipt records committed Downloads copies.
