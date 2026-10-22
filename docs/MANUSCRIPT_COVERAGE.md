# Coverage and next proof obligations

The WSL2 build now proves contextual collapse and a relative maximality theorem
using explicit typed inputs. It also instantiates the complete §5 interface in
a generated occurrence-relation model. This model is the structural fragment;
its identification with the actual Došen–Petrić category remains unproved.
The three project milestones therefore remain distinct and are not declared
complete. See [validation](VALIDATION.md) for the checked source and evidence.

| Milestone | Required endpoint | Current status |
| --- | --- | --- |
| I | Contextual collapse, relation calculations, and a structural/faithful-interpretation interface admitting the intended nonthin model | `ContextualCollapse.total` proved; every interface field instantiated in `GeneratedModel`, with nonthinness and an empty hom-set proved. The intended-category bridge/model check remains open. |
| II | Maximality conditional on explicit coherence, normalization, presentation, and substitution inputs | `relative_maximality` proved for a category on formulas with explicit `OccurrenceInterpretation`, `Normalization`, `SignedLabelPreservation`, `Substitution`, and `DoubleNegation` data. Their correspondence with the intended presentation remains open. |
| III | Maximality for the actual Došen–Petrić presentation with all bridges proved | Open; the actual arrow presentation and its coherence theorem have not been formalized. |

## Checked argument

`Structure` specifies products, coproducts, terminal and initial arrows, and the
typed distributor. `Congruence` specifies equivalence and compatibility with
composition, pairing, and copairing, the operations used by §5. A proof
congruence of the full presentation must restrict to these laws; the record
does not claim to specify every operation of that presentation.

`OccurrenceInterpretation` interprets original-category arrows in tagged
relations, preserves the specified operations, and is faithful. The fold,
swap, first-injection, and second-block equations are proved from the existing
relation calculations. None is a collapse field. Faithfulness is never applied
to congruence classes.

`Collapse.lean` proves the second-block congruence, injected projections,
terminal injection, inverse terminal retraction, uniqueness of existing arrows
into A ∨ top, reversed injection, fold evaluation at top, equal projections,
and totality on every existing hom-set. The reversed injection is obtained by
postcomposition with the coproduct swap. No cancellation of j_A is used.

`GeneratedModel` uses relations denoted by typed terms of the structural
fragment as its hom-sets. Category, product, coproduct, truth-constant,
zero-identity, distributor, and faithful-interpretation laws are all inhabited.
For any variable its projections are unequal; `Hom(top,bot)` is empty. Negated
formulas occur as objects, but negation functor, De Morgan, eta, and epsilon
operations are absent from this fragment. Its auxiliary `Term.Truth` treats
negated formulas as atomic for the empty-hom proof; it is not Boolean semantics
for the full presentation. No substitution action on this model is asserted.

`Isolation` constructs selectors and coselectors for signed normal forms and
proves their exact single-edge relations. A differing edge gives K for a
signed literal, under signed-label preservation. `Normalization` supplies
inverse arrows for transport to these normal forms. `Substitution` acts on
arrows and both endpoint formulas and preserves the structural operations.
`Substitution.Closed` is a separate hypothesis on the congruence. Negative
literals use p ↦ neg A followed by the explicit double-negation retract.
These results combine in `relative_maximality`; its hypotheses are not proved
for the actual presentation.

## Next concrete obligations

1. Define or import the intended Došen–Petrić arrow presentation and its typed
   operations and equations, with provenance to the book's exact revision.
2. Establish its `Structure`, `ZeroIdentity`, and `OccurrenceInterpretation`
   data, including the zero-identity formula, distributor relation, and proved
   faithfulness. This is the remaining intended-model gate for milestone I.
3. Instantiate normalization, signed-label preservation, arrow substitution,
   double negation, and restriction of every actual substitution congruence.
   Prove normalization/occurrence and substitution-coordinate correspondence;
   no kernel of a single valuation may be presumed substitution closed.
4. Instantiate `relative_maximality` through that bridge. Formalize the model
   corollary using every interpretation and nonempty variables. Appendix A's
   profile, ordinal, and renaming correspondences also remain open.

## Verification boundaries

Source screening, public import closure, and compiler-environment axiom audits
have run. Direct, private-name, and hidden-dependency axiom controls are
rejected. These are local checks. Independent Challenge/Solution statement
and shared-definition comparison, independent kernel replay, official
preflight, service verification, and publication have not run.
