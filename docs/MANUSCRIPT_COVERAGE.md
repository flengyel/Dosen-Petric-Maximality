# Coverage and next proof obligations

The conditional collapse, isolation, transport, and `relative_maximality` proofs
are unchanged. The actual September 2007 arrow presentation now has typed
syntax, generated equational equality, a quotient category, and proved
structural and constructed-zero instances. Its occurrence interpretation is
well defined. Faithfulness remains open. The three milestones remain separate.
See [the source map](PRESENTATION_CORRESPONDENCE.md),
[presentation report](PRESENTATION_BRIDGE_REPORT.md), and [validation](VALIDATION.md).

| Milestone | Required endpoint | Current status |
| --- | --- | --- |
| I | Contextual collapse, relation calculations, and the complete structural/faithful-interpretation interface for the intended nonthin category | Conditional collapse proved. The generated fragment still instantiates all §5 fields. The actual source quotient now has `Structure`, constructed `ZeroIdentity`, a well-defined operation-preserving occurrence map, distinct projections for p : P, and an empty Hom(top,bot). Its faithful-interpretation field remains open, so milestone I is not declared complete. |
| II | Maximality conditional on explicit coherence, normalization, presentation, and substitution inputs | `relative_maximality` proved. The source quotient now supplies `Substitution` and `DoubleNegation`. Coherence, normalization, signed-label preservation, and the full congruence correspondence remain open; no intended instance of the conditional theorem is claimed. |
| III | Maximality for the actual Došen–Petrić presentation with all bridges proved | Open. The syntax/category/structural bridge is constructed; Boolean Coherence and the remaining intended instances are not proved. |

## The unchanged conditional argument and fragment check

`Structure` gives products, coproducts, terminal and initial arrows, and the
typed distributor. `Congruence` gives equivalence and compatibility with
composition, pairing, and copairing, as used by §5. `OccurrenceInterpretation`
includes faithfulness in the original category. Its derived fold, swap,
first-injection, and second-block equations feed `ContextualCollapse.total`.
No quotient faithfulness or cancellation of j_A is used.

`GeneratedModel` instantiates every §5 interface field with relations denoted
by typed terms of the structural fragment. It proves distinct projections and
an empty Hom(top,bot). It establishes consistency and nonthinness of that full
§5 interface, including empty occurrence sets. It omits the full Boolean arrow
signature and is not an identification with B(P). Its fragment truth invariant
treats negation atomically; the new full-presentation invariant instead uses
propositional negation. No substitution instance for the fragment is claimed.

`Isolation` gives selectors/coselectors and exact single-edge relations for
signed normal forms. `Normalization`, signed labels, arrow substitution, and
double negation were explicit inputs of the conditional result. The latter two
now have source-quotient instances; the former two do not.

## Actual-presentation constructions

| Obligation | Declaration / status |
| --- | --- |
| Exact primitive grammar and typed endpoints | `Presentation.Term`; only composition, ∧, and ∨ are primitive arrow operations. Negation on arrows is derived in the source and unconstructed here. |
| Published defining equations | `Presentation.Equation`: 71 constructor schemas with a complete source index. `Op` packages both connectives. No relation-kernel equality is a generator; the two `(m e)` laws removed by §11.5 are omitted. |
| Generated equivalence and congruence | `Derives`, `termSetoid`; equivalence, composition, and tensor congruence. |
| Quotient category and operation descent | `Hom`, `ofTerm`, `comp`, `tensor`, `Laws`, `category`. Derived pair/copair/unit/dR/medial/zero composites are typed definitions. |
| Products, coproducts, terminality, initiality | `operations`; `DiagonalData.diag_projections` derives product eta, with coproduct laws by duality. Universal properties are not extra generators. |
| Source zero formula and law | `zeroConstruction_eq`, `zeroIdentity`; the constructed `(0ηε)` composite equals primitive zero and satisfies `(0I)`. Zero arrows between different objects still require an existing-arrow witness. |
| Occurrence equation preservation | `Term.relation`, `Term.relation_distRight`, `Equation.relation`, `Derives.relation`; every defining schema preserves the assigned relation, including empty unit cases. |
| Quotient occurrence map and operations | `occurrenceMap`, `occurrence_id`, `occurrence_comp`, `occurrence_tensor_conj`, `occurrence_tensor_disj`, projection/injection/pair/copair/top/bot/dist/zero/eta/epsilon images. Well-defined covariant assignment to relations; faithfulness open. |
| Nonthinness and empty hom-sets | `nonthin p` for p : P; `empty_hom P` for every P. These require no coherence hypothesis. |
| Whole-arrow substitution and defining-congruence closure | `Term.subst`, `Constant.subst`, `Equation.subst`, `Derives.subst`, `substitute`, `substitution`. Source `(su)` is admissible with substituted endpoints. |
| Double negation | `doubleNegation`, using `Laws.dnOut_in/out`; both inverse equations compiled without coherence. |
| Boolean Coherence / faithful interpretation | Open: `occurrenceMap f = occurrenceMap g → f = g` for every parallel pair. No complete `OccurrenceInterpretation` instance. |
| Normalization and occurrence correspondence | Open: actual inverse comparison arrows to signed normal forms, both inverse laws, and occurrence transport. |
| Signed-label preservation | Open as a proved source-quotient instance. Negative literal objects alone do not prove it. |
| Derived contravariant negation | Open: the exact source clauses, descent, functor laws, and n-r/rho naturality / eta-epsilon dinaturality. |
| Additional congruences | Open: package restriction of every full-presentation proof congruence and its separately assumed substitution closure. Do not infer closure from one valuation kernel. |
| Substitution-schema / Appendix A laws | Open: identity/composition with endpoint identifications, profiles, finite ordinals, renaming, and block-coordinate correspondence. |
| Actual maximality and every-interpretation corollary | Open; do not promote the conditional theorem. |

## Next concrete proof task

Construct the §14.1 negation normalizer using n-r/rho comparisons: for every
A, give a signed normal form N(A), arrows A → N(A) and N(A) → A, and prove
both inverse equations from the published laws. Handle double negation, both
De Morgan cases, and both constants explicitly; then prove the induced
occurrence correspondence. This is separate from the larger coherence proof,
whose source reduction runs through §§11.5,12.5 and §14.2 pp.318–321.

## Verification boundary

The strict local build, transitive axiom audit, local import closure, three
axiom-injection negative controls, and two presentation boundary controls ran
successfully for the source recorded in the report. Independent
Challenge/Solution statement/shared-definition comparison, independent kernel
replay, official preflight, service verification, publication, and an
independent source-transcription review have not run.
