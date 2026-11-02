# Focused mathematical-writing review of the v18 abstract

1 November 2026. Author-side AI-assisted review applying the mathematical-writing
skill. Input: manuscript v17 at 169a7e9c00fa20468d135907507bfc06d3db52ac.
Output: v18, 23 pages. The abstract's opening now supplies context before
the precise result. The literal equation is retained in the body and omitted
from the summary. No unresolved defect was identified in the revision.

## Source and current outline

The official [Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf#page=89)
includes van Leunen's exercise about summarizing an article in at most ten
sentences (§36, printed p.87). Wilf advocates a plain statement of the subject
in §27, p.59; §1, points 12–13, concerns the reader and intelligible prose.
The content order below is our application, not a fixed template attributed
to the book. No ban on formulas or citations is attributed to the source.

The abstract exercise was read in the official PDF's text extraction. Its
handout text is absent from the retained retypeset extraction, whose source
identity is recorded in the v14 provenance. These are distinct editions of
the report; the official PDF supplies the page references used here.

The actual organization remains: abstract; Introduction; the category and main
theorem (§2); occurrences/substitution (§3); isolation (§4); q/e collapse and
model corollary (§5); formalization, symmetric fold and union (§6); A.1–A.3
occurrence maps, ordinals and shared variables; B defining diagrams; C source
rank corrections; D.1–D.5 terms, reading Lean, five declarations, congruence
correspondence and coherence; E.1–E.3 q/e inverses and split comparisons;
authorized disclosure and bibliography. No reorganization is proposed.

## Anchored diagnosis and implemented wording

| Anchor | Difficulty in v17 | Revision and mathematical check |
| --- | --- | --- |
| Abstract, first sentence | The named category and maximality appear before any explanation of proof equations. | Add one sentence explaining equations as proof identifications; state the category and theorem immediately after it. |
| Main-result summary | Essential qualifications must survive a smoother opening. | Retain free generation, nonempty variables, distinct arrows with the same endpoints, operation/substitution closure and equality of all parallel arrows. |
| Method sentences | Local literal notation interrupts the summary before its objects have been introduced. | State occurrence selection, composition, uniform substitution, two isomorphisms and equal projections in words. The full equations and types remain in §§3–5 and E. |
| Model statement | “The model corollary” names a result without saying what it concludes. | State the all-interpretation condition and at-most-one-arrow conclusion, exactly as in Corollary 5.3. |
| Formalization sentences | The summary must distinguish the generated category from a theorem under abstract inputs. | Retain proof of coherence, maximality and the model consequence for the equation-generated category, plus the tagged-occurrence/ordinal correspondence. |

The revised abstract has nine sentences and 171 plain-text words. Their
functions are context; main theorem; its precise meaning; relation to the
conjecture; two sentences of method; model consequence; formalization scope;
and substitution correspondence. It introduces no local notation. “Parallel”
follows the phrase “same source and target”; “maximal” is explained by the
next sentence. The model statement preserves every-interpretation quantification.
The prior paragraph-function records apply unchanged to the preserved body.

## Verification and scope

The abstract was read against Theorem 2.1, Lemma 4.1, Proposition 4.2,
Lemmas 5.1–5.2, Corollary 5.3 and the existing formalization account. No
claim or hypothesis changes. Undoing the abstract replacement and suffixes
recovers the complete v17 source. Appendix A and its main-text references,
both proof routes, the one-line u_A path and specific map terminology remain.

All seven statement bodies, twelve numbered displays, thirteen diagrams,
34 labels, seventeen footnotes, 49 exact source URIs, both bibliographies
and generated bibliography are preserved. The exact abstract agrees across
the source, package, abstract.txt and abstract_latex field; the plain field
is the corresponding Unicode text. Metadata, date/version and package hashes
agree. Both manuscript and extracted archive compile to matching 23-page text
without final warnings. All rendered pages were inspected on contact sheets;
p.1 was additionally viewed individually.

This is a focused abstract and metadata review, not a new whole-paper
mathematical audit, literature search, hostile review, or Lean/kernel/Palomar
verification. No arXiv upload has occurred, so the server preview is not checked.
The source consultation, edit and build/preservation records are retained in
v18 provenance; committed Downloads copies are recorded by the delivery receipt.
