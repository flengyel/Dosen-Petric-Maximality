# Manuscript v4: statements and formal scope

Source: Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*,
21 October 2026. The unchanged source is in `manuscript/`. Labels below refer
to that source rather than an independently assigned theorem numbering.

Let P be a nonempty set of variables. The target category B(P) is the free
zero-identity Boolean category of Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007 revision, §§14.2–14.3. A proof congruence is an equivalence on
each hom-set preserved by every specified arrow operation. A substitution
congruence additionally preserves every uniform formula substitution on arrow
terms and their endpoint types.

The target statement is: for every such congruence θ, if there exist objects
A,C and distinct f,g : A → C with f θ g, then for every X,Y and every
a,b : X → Y, a θ b. The existential pair and universal conclusion range over
the actual presentation. The final semantic corollary quantifies over every
interpretation of variables, not one fixed valuation.

`Category.comp f g` means first f, then g. Thus manuscript g ∘ f is
`Category.comp f g`, or `f ≫ g` after a Mathlib bridge.

| Manuscript definition or result | Formal counterpart | Exact scope or remaining input |
| --- | --- | --- |
| §2 category operations | `DosenPetric.Category`, `Presentation.Term`, `Equation`, `Derives`, `category` | The source quotient is built from the September 2007 primitive grammar and published equations; see `PRESENTATION_CORRESPONDENCE.md`. Composition and both tensors descend by generated congruence. |
| `eq:zero-identity` | `Presentation.zeroConstruction_structural`, `zeroConstruction_eq`, `zeroIdentity` | The source unit-isomorphism composite equals the manuscript pairing/copairing formula and primitive zero; the constructed zero satisfies the required law. |
| `eq:zero-law` | `DosenPetric.ZeroIdentity.law` | For all parallel f,g : A → B, `comp (zero A) f = comp g (zero B)`. |
| §2 zero arrow | `ZeroIdentity.zeroOf` | Requires f : Hom A B. No arrow is supplied to an empty hom-set. |
| §2 witness independence and absorption | `zeroOf_independent`, `commute`, `postcompose`, `precompose`, `zero_idempotent` | All categories with the explicit zero-identity law. `Presentation.zeroConstruction_eq` now proves that formula equals primitive zero in the source quotient; `Presentation.zeroIdentity` uses the construction. |
| §3 formulas and positions | `Formula`, `Formula.Occ`, `Formula.label`, `Formula.subst` | Arbitrary variable types; negation preserves positions; each connective uses Sum tags; constants have Empty positions. |
| `eq:occ-substitution` | `Formula.expand`, `contract`, `contract_expand`, `expand_contract` | For every substitution σ : P → Formula Q and formula A, mutually inverse maps between Occ(A[σ]) and Σ x : Occ(A), Occ(σ(label A x)). No nonemptiness assumption is needed. |
| §3 repeated variables | `Formula.repeated_positions_distinct` | The two positions in p ∧ p are distinct even though their labels coincide. |
| §3 relation operations | `Relations.comp`, `graph`, `sumMap`, `fstRel`, `sndRel`, `copair`, `reassoc` | Binary relations on types. These operations apply in particular to finite occurrence types. `Presentation.occurrenceMap` now descends from the source equation quotient and preserves identity, composition, and the specified operations; faithfulness remains open. |
| `eq:first-injection` | `Relations.first_injection`, `OccurrenceInterpretation.first_injection` | The relation equation is unconditional; its original-category counterpart is derived under the typed faithful-interpretation input. |
| `lem:symmetric` | `Relations.hRel_eq_fold`, `hRel_independent`, `hRel_swap`; `OccurrenceInterpretation.fold_independent`, `fold_swap` | The relation fold is calculated from operations; categorical independence and swap invariance follow by original-category faithfulness. |
| `eq:second-block` final equality | `Relations.second_block`, `OccurrenceInterpretation.second_block` | The relation equation discards the first source block; the categorical equation follows by original-category faithfulness. |
| §3 distinct projections | `Relations.projections_distinct`, `GeneratedModel.nonthin`, `Presentation.nonthin` | Every §5 interface field is instantiated in a generated structural-fragment model, with distinct categorical projections and `GeneratedModel.empty_hom`. This does not identify the fragment model with B(P). Separately, `Presentation.nonthin p` proves distinct projections in the equation-generated source quotient; `Presentation.empty_hom` proves its Hom(top,bot) empty. |
| `thm:coherence` | `OccurrenceInterpretation.faithful` is explicit input; `Reduced.normal_faithful_of_reduced/global_faithful_of_reduced` are conditional transfers | Boolean Coherence remains unproved. Reduced syntactic inclusion is now surjective on normal-form hom-sets, with occurrence compatibility. Faithfulness of Reduced.occurrenceMap is an explicit unproved premise, not an axiom or instance. GeneratedModel faithfulness remains fragment-only. |
| §14.2 source signed-literal reduction used toward §3 coherence | `Reduced.Term/Equation/Derives/Hom/category`, `inclusion`, `red_sound`, `representation` | Genuine restricted syntactic quotient on NormalForm P; 21 term/61 inherited equation schemas, atomic eta/epsilon only. Every full raw term has a reduced representative equal after inclusion to normalization transport; every full normal-form arrow is in the inclusion image. Equality reflection and quotient descent of red are not proved. |
| §14.2 contextual factorizations toward §3 coherence | `Reduced.Context`, `gConj/gDisj`, `gEta/gEpsilon`, `gEta_comp/gEpsilon_comp`; tagged context and composed occurrence laws | Unconditional equalities in Reduced.Hom for arbitrary P, all one-hole contexts and existing top-domain/bottom-codomain arrows (atomic η/ε specializations give (gη)/(gε)/(gηf)/(gεf)). Needed positive identities are directly derived from the unchanged equations. Common atomic factorization is now proved; §12.5 positive-fragment coherence remains open. |
| §14.2 common atomic factorization toward §3 coherence | `Term.Positive`, `atomicFactor`, `supportedAtomicFactor`, `commonAtomicFactor`, common support and `relations_equal` | For every arbitrary P and parallel raw pair, shared expanded endpoints/outer factors and positive raw middles with complete tagged support compile unconditionally. Exact repeated-occurrence lists are concatenated. `faithful_of_positive_coherence` is conditional on the unsupplied eta/epsilon-free PositiveCoherence P; §12.5 coherence remains open. |
| §12.5 algebra toward positive coherence | `Reduced.tensor_zero/tensor_zeroOf`, derived `Term.union/Derives.union/union`, union algebra and occurrence formulas | Unconditional for arbitrary P and existing reduced arrows; positive raw closure is explicit. Union-unit follows the direct p.291 structural proof. No new equation, empty-hom-set zero, coherence or fullness is assumed. Positive Gentzenization is now proved below; cut elimination and restricted coherence remain open. |
| Positive Gentzenization toward §12.5 coherence | `Reduced.Gentzen.G/denote/denote_positive`, `gentzenization`, `gentzenization_decode`, `gentzenization_occurrences` | G0/G1 compile for arbitrary P and every positive raw term, with atomic/constant leaves only, visible contextual cuts, actual singleton units and tagged occurrence coordinates. All 19 Positive schemas are covered. This is existential representation with cuts; Atomic-k is now proved below, while elimination and coherence remain open. |
| Atomic-k toward G2 cut elimination | `Reduced.Gentzen.G.atomization`, `atomization_cutFree`, `atomization_occurrences`; positional `atomThinL/R` and actual mixed-map consequences | Unconditional for arbitrary P and every G proof at unchanged contexts: atomized representative, equal Reduced denotation, preservation of existing CutFree and complete tagged relation equality. All sixteen schemas and four compound-thinning cases compile. Rank/blocked contractions and the rest of G2 remain open. |
| Normalization, §3 | `Presentation.normalization`; `NegationNormalization.forward_backward/backward_forward`, `forward_graph/backward_graph`, `transport_apply` | Actual source-quotient instance for every P, with signed-leaf normal forms, both inverse arrows, inverse tagged coordinates, literal/label/polarity correspondence, Empty cases, and relation transport. Recovery/injectivity reuse the existing theorems. No coherence or naturality premise. |
| Global signed-label preservation, §3 | `Presentation.Term.relation_signedLabel`, `occurrence_signedLabel`, `occurrence_literal` | Proved directly for every raw term and quotient arrow, with no nonemptiness, decidable-equality or coherence hypothesis. Complete literal equality, letter/polarity consequences, opposite-sign exclusion and normalized transport compile. The unchanged `SignedLabelPreservation` definition still takes the separately unconstructed faithful interpretation; no instance is fabricated. |
| `lem:isolation` | `Isolation.selector_edge`, `coselector_edge`, `isolate_edge`, `normalized_literal_context` | Normal-form witness equations and the normalized contextual consequence under faithful interpretation, normalization, and signed-label inputs. The full original-category witness formulation is not a separate declaration; no actual presentation is inferred. |
| `prop:all-contexts` | `ContextualCollapse.context_retract`, `all_contexts` | Typed substitution on arrows and endpoints, separate congruence closure, positive substitution, and negative substitution followed by double-negation transport. |
| `lem:collapse` | `ContextualCollapse.total` | From all K_A, the structural and faithful-interpretation data imply totality on existing arrows by §5. No faithfulness on the quotient or cancellation of j_A. |
| `thm:main` | `relative_maximality` is the conditional counterpart | The actual-presentation theorem remains open. The conditional theorem quantifies over every compatible congruence with explicit substitution closure. |
| `cor:models` | Not implemented | All interpretations; use nonempty P to choose a variable and interpret it as an arbitrary object. |
| Appendix A | Partial | Tagged block bijection is implemented. Profiles, ordinal encodings, renaming squares, and the bridge to the book's operation remain. |

The structural record fields are hypotheses of the conditional theorems.
They are not substitute definitions of the free Boolean category. Adding fields
such as “every contextual equation implies thinness” would assume the central
obligation rather than formalize its proof.

`Structure` gives the bicartesian universal equations, truth-constant arrows,
and distributor with all endpoints. `OccurrenceInterpretation` gives the
operation-level relation laws. `fold_independent`, `fold_swap`,
`first_injection`, and `second_block` derive the corresponding categorical
equations by faithfulness in the original category. The `GeneratedModel`
checks the entire §5 interface, but includes no full Boolean presentation.
`Congruence` records the compatibility needed by this argument; a bridge must
restrict each actual proof congruence to it.

`Substitution.map σ f` has type `Hom (A.subst σ) (B.subst σ)` for
`f : Hom A B`. Its per-substitution functor/operation laws are inputs;
composition and identity laws for substitution schemas themselves have not
been formalized. No closure under substitution is inferred from one
interpretation kernel. The model corollary still requires every interpretation.

## Source-presentation instances

The [source correspondence](PRESENTATION_CORRESPONDENCE.md) gives printed pages,
equation labels, constructors, and derived arrows for the exact September 2007
revision. `Presentation.operations` constructs `Structure` for the syntactic
quotient. `Presentation.zeroIdentity` uses the displayed `(0ηε)` composite;
`zeroConstruction_eq` proves equality with primitive zero. Empty hom-sets are
preserved, with `Presentation.empty_hom` for every variable type P.

`Term.subst`, `Equation.subst`, and `Derives.subst` establish whole-arrow and
endpoint substitution and its preservation of the source-generated equality.
`Presentation.substitution` instantiates the existing per-substitution
`Substitution` interface, including the constructed zero.
`Presentation.doubleNegation` instantiates `DoubleNegation` from the two n-arrows
and their inverse equations. These instances use no coherence hypothesis.
Schema identity/composition with endpoint identifications and occurrence-block
transport remain separate obligations. No arbitrary extra congruence is thereby
proved substitution closed.

`Presentation.Equation.relation`, `Derives.relation`, and `occurrenceMap` prove
well-definedness of the occurrence interpretation and the operation images.
Faithfulness remains open, so no complete `OccurrenceInterpretation` instance
or intended `relative_maximality` instance is claimed. `Presentation.normalization`
now constructs the existing normalization record with occurrence graphs and
signed coordinate correspondence. `Presentation.occurrence_signedLabel` now
proves global signed-label preservation directly, with normal-form literal
and transport consequences. Derived contravariant arrow negation/naturality,
congruence restriction, and the remaining Appendix A/model correspondences are
still open. The reduced signed-literal syntax and existential representation
bridge are now constructed, with occurrence compatibility and conditional
coherence transfer; reduced faithfulness remains open. See the
[reduction report](SIGNED_LITERAL_REDUCTION_REPORT.md),
[signed-label report](SIGNED_LABEL_REPORT.md),
[normalization report](NORMALIZATION_REPORT.md), and the historical
[presentation report](PRESENTATION_BRIDGE_REPORT.md) for exact hypotheses,
source references, commands, evidence, and review boundaries.

The [contextual factorization report](CONTEXTUAL_FACTORIZATION_REPORT.md) records
the next completed source step. The context functor descends through Derives;
its occurrence action fixes surrounding tags and acts on the distinguished hole.
The two “same pairs” comparisons use explicit Sum.inl endpoint embeddings.
Neither these identities nor the earlier representation theorem proves reduced
faithfulness. The source's common atomic factorization and complete support are now proved.
The §12.5 positive-fragment coherence input remains an obligation.

The [common atomic report](COMMON_ATOMIC_FACTORIZATION_REPORT.md) records the
shared factorization and full auxiliary-edge exclusion. Positive describes the
arrow grammar, including zero, rather than literal polarity. Its precise
PositiveCoherence premise is not an axiom or supplied instance. Neither the
factorization nor relation support alone is Boolean Coherence.

The [positive zero/union report](POSITIVE_ZERO_UNION_REPORT.md) records the proved
algebra and separate interpretation formulas. Its dependency table specifies the
then-pending Gentzenization theorem and later coherence inputs; the current G0/G1 status is recorded below.

The [Gentzenization report](POSITIVE_GENTZENIZATION_REPORT.md) records completed
G0/G1 and its historical Atomic-k continuation target. The
[Atomic-k report](POSITIVE_THINNING_ATOMIZATION_REPORT.md) now proves that exact
target, with CutFree preservation and tagged occurrence equality. Typed
ancestor tracing, clusters/rank and the remaining G2 arguments come next.
The representation is existential and supplies no quotient translation.
