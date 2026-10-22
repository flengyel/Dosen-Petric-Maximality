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
| §2 category operations | `DosenPetric.Category` | Explicit Hom, identity, composition, identity laws, associativity. No assertion that it presents B(P). |
| `eq:zero-law` | `DosenPetric.ZeroIdentity.law` | For all parallel f,g : A → B, `comp (zero A) f = comp g (zero B)`. |
| §2 zero arrow | `ZeroIdentity.zeroOf` | Requires f : Hom A B. No arrow is supplied to an empty hom-set. |
| §2 witness independence and absorption | `zeroOf_independent`, `commute`, `postcompose`, `precompose`, `zero_idempotent` | All categories with the explicit zero-identity law. The manuscript formula defining zero from η, ε, d remains to be constructed. |
| §3 formulas and positions | `Formula`, `Formula.Occ`, `Formula.label`, `Formula.subst` | Arbitrary variable types; negation preserves positions; each connective uses Sum tags; constants have Empty positions. |
| `eq:occ-substitution` | `Formula.expand`, `contract`, `contract_expand`, `expand_contract` | For every substitution σ : P → Formula Q and formula A, mutually inverse maps between Occ(A[σ]) and Σ x : Occ(A), Occ(σ(label A x)). No nonemptiness assumption is needed. |
| §3 repeated variables | `Formula.repeated_positions_distinct` | The two positions in p ∧ p are distinct even though their labels coincide. |
| §3 relation operations | `Relations.comp`, `graph`, `sumMap`, `fstRel`, `sndRel`, `copair`, `reassoc` | Binary relations on types. These operations apply in particular to finite occurrence types. No functor from B(P) has been constructed. |
| `eq:first-injection` | `Relations.first_injection`, `OccurrenceInterpretation.first_injection` | The relation equation is unconditional; its original-category counterpart is derived under the typed faithful-interpretation input. |
| `lem:symmetric` | `Relations.hRel_eq_fold`, `hRel_independent`, `hRel_swap`; `OccurrenceInterpretation.fold_independent`, `fold_swap` | The relation fold is calculated from operations; categorical independence and swap invariance follow by original-category faithfulness. |
| `eq:second-block` final equality | `Relations.second_block`, `OccurrenceInterpretation.second_block` | The relation equation discards the first source block; the categorical equation follows by original-category faithfulness. |
| §3 distinct projections | `Relations.projections_distinct`, `GeneratedModel.nonthin` | Every §5 interface field is instantiated in a generated structural-fragment model, with distinct categorical projections and `GeneratedModel.empty_hom`. This does not identify the model with B(P). |
| `thm:coherence` | `OccurrenceInterpretation.faithful` is explicit input | The actual published theorem is unproved in Lean. `GeneratedModel.interpretation` proves faithfulness for the structural fragment model only. |
| Normalization and signed-label preservation, §3 | `Normalization`, `SignedLabelPreservation`, `Normalization.recover` | Typed input data and inverse-arrow transport. The intended instances and occurrence/substitution correspondence remain open. |
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
