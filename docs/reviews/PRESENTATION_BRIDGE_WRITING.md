# Mathematical-writing review of the presentation bridge

The new correspondence map distinguishes generated syntactic equality,
well-defined relational interpretation, and unproved coherence. The principal
editorial requirement is to retain these distinctions when reporting the
checkpoint. No manuscript revision or new outline is warranted.

This is an author-side editorial review of the new construction descriptions,
source correspondence, statement/coverage updates, and presentation report.
The supplied manuscript is Florian Lengyel, *Maximality of the Došen–Petrić
Boolean Category*, v4, 21 October 2026. The complete TeX and existing PDF text
were consulted; the detailed comparison concerns §§2–5 and the new maps.
It is not an independent mathematical certification or a whole-document
layout review.

The governing source is Knuth, Larrabee, and Roberts,
[*Mathematical Writing*, official Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
Section 1, especially points 5 and 10–15, and the discussion of definition
placement in §§4–5 were consulted directly. Section 1's relevant discussion
is on printed pp.2–3, one-based PDF pp.4–5; §§4–5 are printed pp.9–13.
Its advice supports explicit hypotheses, connected explanations, and stable
notation. The application and report organization below are editorial
judgments, not a format prescribed by that source.

## Current outline and contribution

| Existing manuscript section | Function and prerequisites |
| --- | --- |
| 1 Introduction | Maximality question and the isolation/collapse proof route. |
| 2 Boolean proof category | Source presentation, specified operations, zeros, congruences, and the main statement. |
| 3 Occurrences and substitution | Tagged positions, coherence, signed normal forms, and substitution blocks. |
| 4 Isolating an occurrence | Selectors/coselectors and propagation to every contextual equation. |
| 5 Contextual collapse | Symmetric fold, structural collapse, and the model corollary. |
| A.1–A.3 | Profiles/fibres, finite-ordinal coordinates, shared variables and renaming. |

The question is whether an additional substitution-stable arrow equation
forces thinness in the actual Boolean presentation. The new contribution is
its typed syntactic quotient and the structural/zero bridge, with a
well-defined occurrence assignment and concrete substitution/double-negation
data. The existing conditional collapse proofs are retained.

The source map proceeds through objects and primitive grammar, derived arrows,
the full generator index, equational closure, quotient descent, and the
interpretation boundary. The presentation report then records hypotheses,
proved declarations, validation evidence, and remaining obligations. This
order follows the construction dependencies and needs no reorganization.

## Comparison table

| Anchor | Actual editorial issue or risk | Verified principle / rationale | Action |
| --- | --- | --- | --- |
| Source map, quotient paragraph | Equality of raw terms, equivalence classes, and relations must remain distinct. | Explicit typing and consistent notation; §1 points 11 and 14. | State that `Derives` generates equality, then state the one-way preservation theorem. Implemented. |
| Source map, symmetry convention | Uniform Lean indices differ from the disjunctive source convention. | Stable notation and economical indices; §1 points 14–15. | Give the source-to-Lean conversion before the table. Implemented. |
| Report, zero construction | An untyped string of composites would hide the order and role of the unit maps. | Connected explanation; §1 points 10–13. | State the typed path and explain the absorption/naturality proof in prose. Implemented. |
| Coverage milestones I–III | A successful structural bridge can be mistaken for proved coherence. | Self-contained scope; §1 point 5 and independent editorial rationale. | State separately which instances compile and which require faithfulness. Implemented. |
| Source map, 71-constructor count | `Op` packages two schemas; a raw count could be misleading. | Independent rationale: distinguish data representation from mathematical instances. | Label it as the number of Lean constructors, not equation instances. Implemented. |
| Report, substitution | Both arrow endpoints change; extra congruence closure is not automatic. | Explicit variable dependencies; §1 points 5 and 11. | Display the type of substitution and retain the separate closure obligation. Implemented. |

## Definition-order and notation audit

`Formula`, tagged positions, and formula substitution precede the new typed
arrow syntax. The `Op` object constructor and its unit are defined before
`Term.tensor`. Primitive arrows precede the derived pair, copair, initial,
terminal, right-dissociativity, medial, and zero composites. `Constant` is
defined before the side-conditioned symmetry equation. `Equation` precedes
`Derives`, the setoid, and `Hom`; the quotient category precedes its structural
instances. The occurrence assignment on raw terms precedes equation
preservation, derivation preservation, and quotient descent. These are
confirmed definitions, not missing-definition findings.

The composition convention is explicit: Lean `comp f g` applies f and then
g. The zero formula is an endomorphism; a zero from A to B still needs an
existing arrow witness. Constants have empty occurrence types, and repeated
variables have different tags. The full truth invariant uses propositional
negation, unlike the older fragment-only invariant. The two constructions
retain separate names and descriptions.

`DoubleNegation` is an explicit retract/isomorphism instance; it does not
assert a contravariant arrow-negation functor. The latter is correctly listed
as unconstructed. The occurrence map's well-definedness does not assert the
converse implication required for faithfulness. No arbitrary congruence is
called substitution closed merely because the defining congruence is closed.

## Prioritized wording

Retain these exact qualifications in the coverage and presentation report:

- “The occurrence interpretation is well defined. Faithfulness remains open.”
- “The source quotient has `Structure`, constructed `ZeroIdentity`,
  `Substitution`, and `DoubleNegation` instances; the complete
  `OccurrenceInterpretation` instance is not yet available.”
- “The next construction is normalization by the source n-r/rho comparisons,
  with both inverse equations and the occurrence correspondence.”

No replacement manuscript prose, new diagrams, or revised manuscript outline
is recommended. The short typed zero path and the existing manuscript TikZ
diagrams are adequate within this review's scope; process and verification
commentary remains outside the manuscript.

## Scope and checks

The source book's exact September 2007 revision was consulted for the
correspondence map; the PDF digest and printed/PDF page convention are
recorded there. This review addresses the written correspondence and reporting,
not an independent proof of Boolean Coherence or a novelty survey. No new
manuscript compilation or graphical layout audit was performed. The existing
TeX/PDF checksums were checked during local verification. Lean compilation
and audit results are separately recorded in the presentation report.
