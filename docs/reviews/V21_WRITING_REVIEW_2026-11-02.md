# Focused mathematical-writing review: v21

2 November 2026. Author-side AI-assisted review using the mathematical-writing
skill. Input: v20 at 4a6330b9518015f5fb01b4eb5b096c5858269992. Output: v21.
The abstract now states the conjecture itself and gives the disproof. The
author's requested opening and terminology are implemented throughout the
abstract and introduction. No defect remains in that focused scope.

## Source and outline

Governing source: Knuth–Larrabee–Roberts,
[Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
Section 1 points 12–13 were consulted in the retained retypeset copy: orient
the reader and make the prose intelligible without depending on formulas.
The author's mathematical audience determines the appropriate background level;
the book does not require an elementary categorical-proof-theory opening.
The v18 official-source consultation of the abstract discussion is retained.

Actual outline, unchanged: abstract (result and scope); §1 problem/literature;
§2 category/congruences/main theorem; §3 occurrences/coherence/substitution;
§4 isolation/all K_A; §5 q/e collapse/models; §6 formalization/fold/union;
A.1–A.3 occurrence maps, ordinal coordinates and shared variables; B defining
diagrams; C two source corrections; D.1–D.5 terms, reading Lean, five statements,
congruence correspondence and coherence; E.1–E.3 q/e inverses and split
comparisons; disclosure and references. No reorganization is proposed.

Theorem 2.1 concerns collapse after any nonderivable equation under the stated
closure. Its coherence, isolation, substitution, double-negation and q/e inputs
remain. The model corollary still quantifies over every interpretation.

## Findings and implemented repairs

| Anchor | Difficulty | Rationale | Repair |
| --- | --- | --- | --- |
| Abstract p.1 | A pointer to the conjecture does not state it. | Reader orientation; author's correction. | State that Došen and Petrić conjectured the category is not maximal, then give its disproof. |
| Abstract p.1 opening | General explanation of categorical proof theory is unnecessary for the intended reader. | Author's explicit instruction. | Restore the earlier result-first sentence, “We prove that ... is maximal”, following the author’s subsequent instruction. |
| Abstract and §1 p.1 | Elementary paraphrase repeats what collapse to a preorder says. | Author's explicit instruction; economy. | Delete the sentence in both places; use “is a preorder” for the model conclusion. |

## Definitions and exact wording

The result-first opening retains the category, nonempty generators and
freeness. The descriptive collapse sentence retains any nonderivable parallel
equation and both closure conditions. The following sentence explicitly states
that the disproved conjecture asserted that the category is not maximal.
The result concludes collapse to a preorder without the elementary paraphrase.
The §2 definition of preorder, congruence and quotient remains at its point
of mathematical use. No type, quantifier, hypothesis or equation is removed.

The conjecture was checked against the retained primary-source text of
[Proof-Theoretical Coherence](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
September 2007 revision, §14.2 printed p.322. The exact citation remains in §1.
The full revised abstract is in the [release report](../MANUSCRIPT_V21_REPORT.md);
both replacements are in [edits.json](../../provenance/manuscript-v21-review-20261102/edits.json).

## Scope and validation

The changed prose was read continuously. The whole-source prose/dependency
pass retains previous paragraph classifications for unchanged passages: the
abstract introduces the category, conjecture, disproof, method and consequences;
the introduction introduces the problem and compares it with the conjecture.
Outside the abstract, restoring the deleted introduction sentence and version/
date suffixes recovers v20 exactly. No process commentary is inserted.

Both builds pass with matching 23-page layout text and no final warnings.
All pages were viewed on six contact sheets; p.1 individually. All mathematical
statements, bibliography entries, source links and earlier releases remain.
This is a focused writing review, not a new independent mathematical, novelty
or hostile review. No Lean/kernel/Palomar checks are repeated. No source-access
or compilation limitation arose in this scope. No arXiv upload has occurred.

Retained: docs/reviews/V21_WRITING_REVIEW_2026-11-02.md.
Delivered: /mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v21-20261102/V21_WRITING_REVIEW_2026-11-02.md.
The release receipt records verification from committed bytes.
