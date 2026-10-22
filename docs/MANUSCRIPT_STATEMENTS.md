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
| `eq:first-injection` | `Relations.first_injection` | Equality of the interpreted relations of d ∘ (1 ∧ ι₁) and ι₁. The categorical law is not inferred without a faithful interpretation. |
| `lem:symmetric` relation calculation | `Relations.hRel_eq_fold`, `hRel_independent`, `hRel_swap` | h is computed from the specified relations of sumMap, distributor, projection, and copairing. Independence of the auxiliary type and swap invariance follow. |
| `eq:second-block` final equality | `Relations.second_block` | Replacing the first copairing component by the empty relation discards the first source block. |
| §3 distinct projections | `Relations.projections_distinct` | The two relations Sum Unit Unit → Unit differ. This is not yet a nonthin instance of the complete categorical interface. |
| `thm:coherence` | Not implemented | Published faithfulness theorem; no custom axiom. |
| Normalization and signed-label preservation, §3 | Not implemented | Specify normalization isomorphisms and prove their occurrence/substitution properties. |
| `lem:isolation` | Not implemented | Select a differing relation edge and construct typed selector/coselector in the actual category or a precisely delimited interface. |
| `prop:all-contexts` | Not implemented | Positive literal substitution; negative literal substitution followed by double-negation transport. |
| `lem:collapse` | Not implemented | From all K_A derive equality of projections by the §5 argument, then thinness. |
| `thm:main` | Not implemented | Combine isolation, substitution, and contextual collapse with the checked presentation bridge. |
| `cor:models` | Not implemented | All interpretations; use nonempty P to choose a variable and interpret it as an arbitrary object. |
| Appendix A | Partial | Tagged block bijection is implemented. Profiles, ordinal encodings, renaming squares, and the bridge to the book's operation remain. |

The structural record fields are hypotheses of preliminary algebraic lemmas.
They are not substitute definitions of the free Boolean category. Adding fields
such as “every contextual equation implies thinness” would assume the central
obligation rather than formalize its proof.
