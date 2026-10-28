# Writing review of manuscript v7's errata appendix

The supplied Appendix C states the two corrections precisely and explains the
rank distinction in mathematical language. V7 implements it without changing
the main argument or the occurrence-coordinate appendices. The complete appendix
now fits on p.12, before the accepted disclosure.

This author-side review uses
[mathematical-writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59).
The governing source is Knuth, Larrabee and Roberts, Mathematical Writing,
§1 points 5, 10–15 and 17, printed pp.2–3, with the retained §4 qualification
on definition placement, printed p.9. The retained MIT-hosted PDF has SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
The source was consulted; no unavailable-source fallback is claimed.

## Existing outline and functions

The source retains its existing organization:

1. Introduction: maximality question, proof strategy, relevant literature and roadmap.
2. Boolean proof category: presentation, structural maps, congruences and main theorem.
3. Occurrences and substitution: tagged coordinates, coherence and substitution maps.
4. Isolating an occurrence: selector/coselector calculation and contextual equation.
5. Contextual collapse: q_A/e_A isomorphisms, collapse, maximality and model corollary.
6. Lean formalization: conditional theorem and the retained symmetric-fold route.
7. Appendix A: profiles/fibres, ordinal coordinates and shared-variable substitution.
8. Appendix B: typed structural diagrams.
9. Appendix C: two source-rank corrections and their mathematical explanations.
10. Accepted disclosure and references.

The main results still depend on coherence and the specified structural
isomorphisms. Appendix C documents corrections to a dependency's proof; it does
not replace those dependencies with a claim of completed Lean verification.
No alternative outline is warranted.

## Findings and concrete actions

| Anchor | Issue or rationale | Source principle or requirement | Action |
| --- | --- | --- | --- |
| Introduction roadmap | The new appendix needs a corresponding route through the paper | KLR reader motivation and consistent references; explicit author wording | Insert the supplied sentence before the printed-pagination convention. |
| Appendix C opening | r and r' must be understood before the comparisons | KLR local statement clarity and notation at use; project definition-order convention | Retain the supplied definitions and left/right positivity convention. |
| p.260 paragraph | Direction of the strict inequality is claim-bearing | Primary-source comparison and mathematical predecessor argument | Preserve r' < r and the explanation that the other side is unchanged. |
| p.262 paragraph | Side rank and total rank have different meanings | KLR consistent notation; source p.261 comparison | Preserve the right-side qualification and the total-rank-at-least-two explanation. |
| First v7 layout | Two short correction paragraphs were split across pages | Independent layout preference, not a KLR theorem | Insert a page break before Appendix C; keep its exact text together on p.12. |
| Existing mathematical prose and diagrams | No further authorized correction was established | Preserve scope and substantive content | Keep all earlier text, diagrams, references and disclosure unchanged. |

## Definition order, connected reading and scope

The addition introduces r and r' before its two comparisons, distinguishes left,
right and total rank, and identifies the exact source cases before explaining
the corrections. Its citations use the existing DP entry and the introduction's
printed-page convention. Neither paragraph attributes motives to the source's
authors. Process, review, tool and delivery remarks stay in external records;
the explicitly accepted disclosure is preserved verbatim.

The complete revised source was checked for dependency/order and process-text
regressions, with the changed roadmap and Appendix C read continuously in their
surrounding text. The ten TikZ diagrams and complete Appendices A–B were compared
with v6 source; no prose contraction or theorem qualification was removed.
The mathematical functions of the retained paragraphs remain definitions,
statements, arguments, examples, source comparisons or explanations. No new
whole-paper mathematical or novelty certification is asserted.

The final latexmk build resolves citations and cross-references and reports no
layout warnings. All thirteen pages were inspected as a contact sheet, with
readable inspections of the diagram-bearing pages and Appendix C. Appendix C
and the disclosure are on p.12, with references on p.13. V4/v5/v6 hashes pass.
The concrete Lean blocked-rank correspondence remains an implementation
obligation recorded outside the paper. Retain this report under docs/reviews
and deliver its committed bytes with the manuscript report and mathematical
review, using the recorded conflict-preserving delivery checks.
