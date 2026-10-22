# Signed-literal reduction: mathematical-writing review

The exposition identifies the proved endpoint as surjectivity of the syntactic
inclusion on normal-form hom-sets. It distinguishes that result from equality
reflection, a quotient-level reduction function, and coherence. The typed
mixed-map displays make the compound witness construction assessable.
No manuscript revision or additional diagram is needed for this checkpoint.

This is an author-side, AI-assisted review of the new construction descriptions,
correspondence table, reduction report, and current scope maps. The mathematical
manuscript is Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*,
v4, 21 October 2026. Its relevant context is §3; no whole-paper editorial or
layout judgment is made, and the manuscript is unchanged.

The governing source was consulted directly from the verified cached
Knuth–Larrabee–Roberts *Mathematical Writing* course report, with
[MIT-hosted source](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf).
SHA-256 `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
Section 1 and §§4–5 were consulted again. Printed pp.1–6 are one-based PDF
pp.3–8; printed pp.9–13 are PDF pp.11–15. The 119-page typeset course-report
copy is not claimed byte-identical to the Stanford scan or 1989 MAA edition.
All earlier access records remain unchanged. The review is source-grounded
for these passages; its format and applications are editorial judgments.

## Actual outline and contribution

| Existing sequence | Function / dependencies |
| --- | --- |
| Report, exact endpoint | States arbitrary P and the existing-arrow quantifier, then the inclusion equation. |
| Reduced signature and equations | Defines C's objects, primitive arrows, generated equality and inclusion before reduction. |
| Duality and compound witnesses | Gives object duality, both mixed map types, eta/epsilon recursion and compatibility. |
| Raw transport equality and normal endpoints | Explains constructor coverage, endpoint casts and existential representation. |
| Occurrence compatibility and conditional transfer | Keeps interpretation preservation, representation and faithfulness separate. |
| Verification and remaining obligations | Gives actual evidence and the precise missing reduced coherence proposition. |

The contribution is a syntactic reduction into C with a proved inclusion
equation. The current dependency order works; no revised outline is warranted.

## Comparison table

| Anchor | Actual difficulty / scope risk | Verified source principle or independent rationale | Applied repair / decision |
| --- | --- | --- | --- |
| Exact representation statement | “Reduction” can imply a quotient-level function or an equivalence. | §1 point 5: state theorem hypotheses within the statement. | Display the existential reduced arrow and say explicitly what equality/reflection is unproved. |
| Compound witness section | A name like medial would hide mixed source/target connectives. | §1 points 10–13: explain and motivate formulas in connected prose. | State both mixed types and the structural construction before explaining their use. |
| Source and implementation names | C, raw terms, quotient arrows and inclusion could share ambiguous notation. | §1 point 14: keep notation consistent. | Give typed Lean names and distinguish Term, Derives, Hom and inclusion. |
| Endpoint casts | Saying “normalization is identity” would suppress dependent types. | Independent typing rationale. | State normal_formula and both casted comparison identities, then transport_formula. |
| Definition placement | Existing definitions need no repeated dictionary, but new duality and casts need local explanations. | §§4–5: definition placement is contextual; define symbols near their use. | Reuse prior NormalForm/normalization definitions and introduce the new operations before the theorem. |
| Conditional transfer paragraph | A proved implication could look like a proved coherence instance. | Independent scope rationale. | Name the missing Reduced.Faithful premise and retain the prior coherence dependencies. |

## Definition-order and notation audit

Confirmed prior definitions include Formula, Literal, NormalForm and its formula
embedding, Presentation.Term/Equation/Derives/Hom, normalization, occurrenceMap,
and signed labels. The reduced Op and unit precede the new Term; derived dR
and medial precede equations that abbreviate them. Constant precedes the
side-conditioned symmetry equation. Equation and Derives precede the quotient,
category and inclusion.

Object duality and its normalization compatibility precede compound witnesses.
Mixed map endpoints are explicit, and the helpers are distinguished from the
same-connective medial. Casts and comparison identities precede representation.
The raw reduced relation precedes its well-defined quotient assignment and
conditional faithfulness proposition. These are confirmed definitions, not
missing-definition findings.

The report uses N(A) only after matching it to the existing normalizer. A
normal form and its embedded Formula are distinguished. “Include” always
refers to the covariant inclusion, while “red” denotes a choice on raw terms.
Operational composition order is explicit. Signed labels and position tags
remain different notions; no enumeration of P is introduced.

## Prioritized wording

Retain the exact scope sentence: “For every full arrow between normal-form
formulas, there exists a reduced arrow whose inclusion equals it.” Retain also:
“This does not prove that inclusion reflects equality or that red descends
to quotient arrows.” For transfer, use: “Reduced occurrence faithfulness,
if proved, implies normal-form and then global Presentation faithfulness.”

No replacement manuscript prose, new outline or diagram is warranted. The
short typed mixed-map displays and explicit quantifiers suffice for this
report's purpose. Keep reviews and verification commentary outside v4.

## Scope and checks

The complete new code and construction descriptions were examined along with
the source passages identified in the correspondence map. The governing writing
text was available locally and hash-verified; no fresh Stanford retrieval was
needed. Historical reports and access records were preserved. No whole-document
layout audit, fresh manuscript compilation, novelty survey, independent kernel
replay, or mathematical certification was performed. Existing manuscript
TeX/PDF hashes passed; Lean verification is separate evidence in the report.
