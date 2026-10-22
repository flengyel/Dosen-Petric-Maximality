# Normalization: provisional mathematical-writing review

The new exposition states a compiled objectwise normalization isomorphism
and its occurrence correspondence. It keeps global signed-edge preservation,
coherence, and naturality separate. No manuscript revision is needed for this
checkpoint; manuscript v4 remains unchanged.

This is an author-side, AI-assisted editorial review of the new Lean module
descriptions, normalization report, source correspondence, and current scope
maps. It is **provisional**: the governing source, Knuth, Larrabee, and Roberts,
[*Mathematical Writing*, Stanford report STAN-CS-88-1193](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
could not be retrieved in this session. The official Knuth URL and the
[Stanford report archive](https://i.stanford.edu/pub/cstr/reports/cs/tr/88/1193/CS-TR-88-1193.pdf)
timed out through the web tool; escalated curl attempts failed to connect
(exit 7). No local supplied copy was found. The prior presentation-writing
report records earlier direct consultation; that historical record is not a
fresh source check. Access outcomes are retained in
`provenance/wsl-normalization/writing-source-access.json`.

Accordingly, the judgments below use explicit independent editorial rationale.
They do not claim freshly verified compliance, quote the unavailable source,
or assign unchecked rule or page numbers. A source-grounded final review
remains to be completed when the governing text is accessible.

## Actual outline and contribution

| Reviewed text | Function and dependency |
| --- | --- |
| Normalization report: result and hypotheses | States arbitrary variable types, exact arrow endpoints, and the narrow endpoint before the evidence. |
| Source correspondence: comparison table | Locates primitive n/r/rho types and inverse equations before the derived recursive construction. |
| Normalization report: construction and occurrence transport | Explains sign recursion, inverse-arrow proofs, tagged coordinates, and relation transport in dependency order. |
| Statement and coverage maps | Connects the new instance to manuscript §3 while retaining the three separate milestones. |
| Validation and continuation records | Gives actual verification boundaries and the next global signed-edge proof. |
| Unchanged manuscript v4, §§2–5 and Appendix A | Existing mathematical argument; neither new process reports nor source-audit commentary is inserted into it. |

The problem is to supply the previously assumed normalization data in the
actual equation-generated presentation. The contribution is the constructed
instance and its proved coordinate transport, not a new coherence theorem.
This order is adequate. No replacement manuscript outline or new diagram is
warranted by the scoped review.

## Comparison table

All principles in this table are independent editorial judgments because
fresh consultation of the governing writing text was unavailable.

| Anchor | Actual difficulty or scope risk | Rationale | Concrete repair / observed outcome |
| --- | --- | --- | --- |
| Report, result and hypotheses | “Normalization” can be read as full arrow normalization or uniqueness. | A theorem summary should identify its exact data and quantifiers. | State `P : Type u`, signed-leaf `NormalForm`, typed forward/backward arrows, and both identities. Implemented; no uniqueness or coherence claim. |
| Correspondence, inverse table | Reversing composition makes the identity object ambiguous. | Explicit endpoints let readers check equations locally. | Give `comp f g` order and both identity endpoints before the table. Implemented. |
| Report, Boolean sign recursion | A bare Boolean parameter hides which formula is being normalized. | Explain an auxiliary parameter before its clauses are used. | Say false normalizes A and true normalizes ¬A, with recursion on A alone. Implemented in prose and the code docstring. |
| Report, graph and signed-label paragraphs | Signed coordinates could be mistaken for arbitrary-arrow label preservation. | Distinguish quantified domains of nearby assertions. | Restrict the proved literal claim to comparison coordinates and retain global signed edges as the next task. Implemented. |
| Correspondence, pp.313–314 | The source also defines a functor and proves naturality. | A local correspondence must say which source claims are covered. | State that object normalization and inverse comparisons are covered; Auxiliary Lemma, naturality, and equivalence remain open. Implemented. |
| Coverage, milestones I–III | Historical reports say normalization is open. | Readers need a dated current status distinct from historical evidence. | Current maps close normalization; validation labels earlier checkpoints historical and points to the new report. Implemented. |
| Verification paragraph | “Passed the audit” can imply independent certification. | A validation claim must identify its method and limits. | Give 25 files, 1601 declarations, permitted axioms, five observed rejections, source hashes, and checks not run. Implemented. |

## Definition and notation audit

Confirmed prior definitions: `Formula`, `Formula.Occ`, `Formula.label`,
`Literal`, `NormalForm`, `NormalForm.literalAt`, and the existing `Normalization`
record precede this construction. `Hom`, source comparison arrows, generated
equations, quotient laws, and the descended `occurrenceMap` also precede it.
They are not missing definitions.

The new order is `Literal.flip/letter/negative`, `Formula.signedLabel/polarity`,
the normal-form literal comparison, then `NormalComparison` and its explicit
constructors. `form/source/comparison` precede `normal/forward/backward` and
the actual instance. Coordinates are defined before their graph, literal,
label, polarity, and transport statements. This supplies every new symbol
before its use in the reporting argument.

The report defines `N(A)`, forward/backward, and coordinate maps p_A/q_A
together with their types. These mathematical names are explicitly matched
to Lean names. No source arrow is renamed without a correspondence entry.
Printed and PDF page numbers have a fixed stated offset. Boolean “negative”
means parity along a tagged path. Sum tags distinguish repeated occurrences;
Empty, not a chosen dummy coordinate, handles constants.

## Prioritized wording and revised-outline decision

Retain these precise sentences in future summaries:

- “`Presentation.normalization P` constructs the existing `Normalization`
  record for every variable type P.”
- “The two inverse-arrow laws are proved from category, tensor, and source
  n/r/rho inverse equations.”
- “The comparison coordinates preserve signed literals; preservation along
  every arrow remains a separate obligation.”
- “Object normalization and its comparison isomorphisms do not supply the
  source functor's naturality or Boolean Coherence.”

No revised manuscript outline, replacement prose, or additional TikZ diagram
is justified by this checkpoint. Keep build evidence and review commentary
in the reports, outside the manuscript.

## Scope and limitations

This provisional editorial pass examined the actual new construction and
its source table. The Došen–Petrić comparison source was available and
cross-checked; its digest and page map are recorded separately. The entire
Knuth–Larrabee–Roberts source was unavailable for fresh verification, so this
is not a completed source-grounded writing certification. No independent
mathematical review, whole-document graphical/layout audit, new manuscript
compilation, or novelty survey was performed. Manuscript TeX/PDF integrity
was checked against the existing hashes. The mathematical audit and strict
Lean checks are separate evidence, not consequences of this prose review.
