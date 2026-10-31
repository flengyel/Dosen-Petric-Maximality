# Hostile review of manuscript v10/v11, resolved in v12

Review date: 31 October 2026. Initial source: v10 at
`89ebf8390f8906a6c2529cea6f910c65ece8889f`. During review, main advanced to
`97d728820d87f712c32c77dcb29fcd6fa0856e3d`, containing v11 and its delivery
record. The v11 changes were inspected and incorporated; v12 preserves that
release and its exact supplied Palomar BibTeX. Original line anchors below are
to v10 unless identified otherwise. The companion line review gives complete
coverage and the source comparisons. No Lean source is changed.

## A. Kill-shots / hard blockers

None established. The review found no counterexample, ill-typed composite or
unproved step in the manuscript's maximality argument. This conclusion is
limited to the written argument and the source/declaration comparisons below;
it is not a new kernel replay or a re-audit of the complete Lean dependency graph.

## B. Major weaknesses

No confirmed major mathematical defect. The two points most likely to conceal
one were checked explicitly:

1. **The particular isomorphisms, lines 467–500.** The cited list supplies
   existence, not the names q and e. The manuscript bridges that distinction:
   at a single variable, q has the unique one-point bijection; the two-point
   bijection of an isomorphism with e's endpoints can be adjusted by swapping
   its source. Faithfulness identifies the resulting arrows with q and e.
   Substitution preserves their inverse equations. Lemma 7 of *Isomorphic
   formulae* independently supplies each prescribed label-preserving bijection.
   No converse to faithfulness or preservation of isomorphisms by a quotient
   is being assumed without justification.
2. **The model corollary, lines 571–580.** Agreement under every interpretation
   is closed under substitution because precomposition with F_sigma gives
   another interpretation. Agreement under one fixed interpretation would
   not suffice. Nonempty P permits interpreting a variable as an arbitrary
   target object; equality of its projections equates arbitrary target arrows
   by pairing. No fullness or surjectivity assumption is required.

## C. Minor issues

All items in this section are resolved in v12. They are expositional repairs,
not claims that an existing Lean theorem was malformed.

| Severity / failure label | Anchor | Finding and repair |
| --- | --- | --- |
| minor / ambiguous | 56–64 | A “relation distinguishing two arrows” leaves the two interpretations unnamed. State the choice of an edge in one relation and not the other. |
| minor / ambiguous | 76–79 | “Related occurrence-selection constructions” does not state what Lemma 6 supplies. State the selected same-variable occurrences and the tautological-implication hypothesis. |
| minor / ambiguous | 81–83 | “Their Boolean-category axioms” suppresses the specialization of the cited freeness theorem. Name the graphical, Delta–Nabla-strong K-flat/K-sharp categories of the proceedings theorem. The expanded preprint has different wording; do not silently substitute it. |
| minor / ambiguous | 89–92 | “Equates an endomorphism with the identity” fails to identify the composite. Refer to the displayed zero-identity composite and state the different equations imposed on it. Use equation (11), stable across the accessible author copy and the published reference. |
| minor / ambiguous | 127–132 | Pairing and copairing use standard implicit typing. Display their input and output types. This is a clarification of notation: `Term.pair` and `Term.copair` already have precisely these types. No missing Lean type or formalization error was found. |
| minor / ambiguous | 285–297 | Replace “correspondence of positions” by its typed bijection. Distinguish object formation from arrow generators in the signed-literal argument. |
| minor / ambiguous | 320–340, 690–711, 757–759 | Replace “organization”, “fits over”, and “keeps ... visible” by the maps, their composite equations, and the equalities or distinctions of their coordinates. |
| minor / ambiguous | 556–561 | List what an interpretation preserves instead of saying “structure-preserving”. |
| minor / ambiguous | 593–619 | Identify the general theorem's conclusion and assumptions and its use of the fold proof. Distinguish its application from the q/e proof. |
| minor / missing_definition | 774–777 | V10 uses “skeleton” without a prior explicit definition; v11 defines it. V12 retains that definition and makes preservation of constants/connectives and reconstruction by the profile explicit. |
| minor / ambiguous | 824–830 | State the two endpoint patterns, each with one variable occurrence, rather than calling p alone the outer pattern. |
| minor / inconsistent_use | PDF links | Repeated equation destinations could send a link to a different display. Include the section in the hidden destination name; visible equation numbers and labels are unchanged. |

## D. Cross-section consistency failures

No mathematical inconsistency was established. The review checked these
possible failures and retained the necessary qualifications:

- Zero arrows are defined only in nonempty hom-sets. All zeros used in the
  argument have witnesses; no global zero-morphism structure is introduced.
- Coherence is used in the original category. It is not transferred to the
  quotient after a new equation has been imposed.
- Composition reads right to left in the manuscript and left to right in the
  Lean constructor `comp`. The displayed zero path and q/e formulas respect
  that translation.
- The negative literal branch substitutes neg A for p, then uses the
  double-negation isomorphism. Its square has the correct directions.
- Repeated occurrences remain distinct tags. Empty blocks have no positions;
  prefix-sum decoding selects the unique nonempty containing block.
- The abstract now includes the nonempty-generator hypothesis. The separate
  substitution construction also explicitly permits an empty target variable
  set Q, consistent with the syntax and existing declarations.
- The Palomar family consists of the five names in `comparator.json` at the
  registered source. It is not described as a separate registration of every
  auxiliary result in the paper.

## E. Acceptance conditions, non-negotiable

The conditions for this revision are: preserve the mathematical statements and
proof routes; replace vague prose by specific claims; check the cited comparisons
against their primary texts; retain the supplied BibTeX; build the exact release
and arXiv package; verify references, diagrams and version pointers. The v12
report and validation record give the results. An unchanged registered proof
does not require another Lean build or Palomar intake for these prose changes.

## F. Not checked / uncertainty log

- No new Lean build, independent kernel run or exhaustive formal-source audit.
  Existing registered verification is preserved. Source inspection checked
  the typed syntax, coherence/maximality endpoints, the short proof, fold
  correspondence, model corollary, and the claim map.
- The literature check covers the cited works and exact claims, not an
  exhaustive search for every possible prior maximality theorem. It does not
  issue a new priority certificate.
- The two source errata were checked against rendered pages 260 and 262,
  their adjacent rank argument, and the rank definition on page 249. This is
  not a reproof of every case of the book's cut-elimination theorem.
- Author PDFs were obtained from their repositories when the browser index
  could not open them. The source manifest records the exact checked files.
- The Windows Downloads directory and the author's WSL checkout are not
  available in this review environment. New v12 Downloads delivery is not
  claimed; the earlier v11 delivery remains recorded separately.

Self-audit: the strongest confirmed issue was the lack of specificity in the
literature comparison and several descriptions of coordinate maps, not a false
theorem. No unresolved suspected counterexample was identified within the
checked argument. The relevant primary sources were available. Recommendation:
accept these revisions for mathematical exposition; retain the stated limits
on formal replay and exhaustive novelty review.
