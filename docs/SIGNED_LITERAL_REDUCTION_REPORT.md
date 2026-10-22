# Signed-literal reduction report

The signed-literal syntactic reduction is proved. For every arbitrary
`P : Type u`, signed normal forms A,B, and existing full-presentation arrow
`f : Presentation.Hom A.formula B.formula`, there exists
`r : Reduced.Hom A B` such that `Reduced.inclusion r = f`.
This is hom-set surjectivity, not equality reflection or Boolean Coherence.

Starting checkpoint: `c1004b09a53f56a048c813adba053739fb0d4a97`, clean main.
SSH fetch left local and remote main equal. The completed presentation,
normalization, signed-label invariant and conditional maximality proofs were
reused. No original presentation equation, faithful-interface definition,
toolchain, dependency manifest, or manuscript v4 text/diagram/reference changed.

## Exact statements and hypotheses

`Reduced.representation` has type

```
(A B : NormalForm P) (f : Presentation.Hom A.formula B.formula) →
  ∃ r : Reduced.Hom A B, Reduced.inclusion r = f.
```

No inhabitant, decidable equality, finite enumeration, or coherence assumption
on P is required. Every quantified arrow has an existing-arrow witness.
No arrow is installed in an arbitrary empty hom-set. Composition `comp f g`
applies f before g.

The stronger raw-term endpoint is also proved. For every full term
`t : Presentation.Term P A B`,

```
Reduced.red t : Reduced.Term P (normal A) (normal B)
Reduced.includeTerm (Reduced.red t) =
  (Presentation.normalization P).transport (Presentation.ofTerm t).
```

Here normal is `Presentation.NegationNormalization.normal`, and includeTerm is
the full quotient class of the raw syntactic inclusion. The comparison equality
is in the original generated-equation Presentation quotient. It is not inferred
from occurrence relations. There is no chosen reduction function on full
quotient arrows: preservation of full derivations as reduced derivations is
not proved or needed for the existential theorem.

## Source and syntactic correspondence

Source: Došen–Petrić, *Proof-Theoretical Coherence*, September 2007 revision,
[author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed p.n is zero-based PDF page n+11, or one-based page n+12. The requested
pp.317–321 and §14.1 normalization clauses were consulted; rendered pp.317–318
were inspected. Full source files are consultation material, not redistributed.

| Source location | Actual construction / boundary |
| --- | --- |
| p.318 / one-based PDF 330, C(C) grammar | `Reduced.Term`, indexed by existing NormalForm P objects, has 21 Lean constructor schemas: positive structural families, zero endomorphisms, composition/tensors, and atomic eta/epsilon. n/r/rho and arbitrary-formula eta/epsilon are absent as constructors. |
| p.318, E(C) = E(ZIDL_top,bot) | `Reduced.Equation` has exactly the 61 inherited positive schemas, with the positive-letterless Constant condition. There are no extra atomic eta/epsilon equations, no comparison inverse schemas, and no additional (0eta-epsilon) generator. Op packages both connectives, so counts are schemas, not individual equation instances. |
| Inherited equations indexed in PRESENTATION_CORRESPONDENCE | Each reduced schema has the same name/source label as the corresponding full positive schema; exact table and checked signature metadata are retained. The two source-omitted (m e) schemas remain omitted. |
| p.318, C(C)/E(C) | `Reduced.Derives`, termSetoid, Hom and category use generated syntactic equivalence/congruence. Equality is neither a relation kernel nor equality after full inclusion. |
| pp.313–314, object normalization and inverse comparisons | Object duality, normal_formula, normal_neg_formula, casted forward/backward identities and transport_formula. No source normalization equivalence or arrow-negation functor is assumed. |
| p.317, eta/epsilon equations for connectives/constants | Recursive etaNF/epsilonNF terms built from atomic primitives and explicitly typed structural mixed composites; negative literals use symmetry. Their full compatibility is proved by the source zero-identity law and top/bottom uniqueness. |
| p.317, eta/epsilon as zero arrows | Existing toBot_unique and new zero_top/fromTop_unique; no appeal to empty interpreted relations. |
| pp.318–321, subsequent coherence proof | Not completed. The g-eta/g-epsilon factorization identities, positive-core coherence inputs, reduced faithfulness and equality reflection remain separate. |

The inclusion `Term.toFull` sends atomic eta/epsilon to the original arrows at
var p and structural terms to matching full terms. `Equation.toFull` checks
every inherited schema; `Derives.toFull` extends through equivalence and
operation congruence. Thus `inclusion` descends to Reduced.Hom and preserves
identity, composition and both tensors. This proof precedes the representation
argument and uses no interpretation or faithfulness claim.

## Duality and compound witnesses

`NormalForm.dual` flips each complete literal, swaps conjunction/disjunction,
and swaps top/bot. `dual_dual` proves involution. `form_true` proves
`form A true = (form A false).dual` for every full formula A;
`normal_neg_formula` specializes this to normal-form formulas.

The two derived mixed arrows are explicitly typed as

```
mixedDisj A B C D : (A ∨ B) ∧ (C ∨ D) → (A ∧ C) ∨ (B ∨ D)
mixedConj A B C D : (A ∧ B) ∧ (C ∨ D) → (A ∧ C) ∨ (B ∧ D).
```

They are compositions of d/dR, symmetry, associators and tensors. They are
not the same-connective medial. The displayed types provide the mixed patterns
needed by the source witness formulas. No general equality between these
chosen composites and a particular source e'-abbreviation is claimed or
needed: compatibility of the completed eta/epsilon arrows follows from the
proved uniqueness laws.

`Term.etaNF A : top → dual A ∨ A` and
`Term.epsilonNF A : A ∧ dual A → bot` recurse on normal forms. Positive
literals use the atomic primitives; negative literals use the corresponding
symmetry. Constant cases use unit maps. Conjunction/disjunction cases combine
the child witnesses through the two mixed arrows and the appropriate units.

`Compatibility.etaNF` identifies inclusion of etaNF with original eta at
A.formula followed by the normalized negation comparison tensor identity.
`Compatibility.epsilonNF` identifies inclusion of epsilonNF with identity
tensor the inverse negation comparison followed by original epsilon. All
endpoints are explicit. `negForward/negBackward` are pointwise comparison
arrows, not contravariant negation on arbitrary arrows.

`fromTop_unique` follows from zero_top, terminal uniqueness and zero_law;
toBot_unique was already proved from the dual laws. Therefore these
compatibility equations do not use faithfulness or empty-relation inference.
Arbitrary zero arrows are never introduced: primitive zero remains an
endomorphism, and all composites have explicit typed witnesses.

## Raw reduction and normal-form representation

`red_sound` covers all 31 full term-constructor schemas. Identity, composition
and tensors use normalization transport laws. Positive structural generators
use their existing naturality equations with the forward comparison arrows;
the square lemma cancels using the constructed inverses. Zero uses zero_law.
n/r/rho normalize to identities, with the reverse directions checked by the
source inverse equations. Arbitrary eta/epsilon use the compound witnesses
and parallel-arrow uniqueness, after the explicit dual-normalization casts.

`normal_formula A : normal A.formula = A` proves fixed normal-form objects.
`forward_formula/backward_formula` prove that their comparison arrows are
identities after endpoint casts. `transport_formula` then proves that a full
arrow between normal forms is unchanged by normalization transport after
the same casts.

Quotient induction on the full arrow chooses a raw representative t; cast
red(t) back to A,B, take its reduced quotient class, and use red_sound plus
transport_formula. This proves representation as stated, without proving
that red respects full equations in Reduced.Derives. Inclusion is not shown
to reflect equality.

## Occurrences and conditional transfer

The reduced raw occurrence assignment uses the existing tagged normal-form
formula positions: identity/reassociation/symmetry graphs, relation composition,
Sum tensors, copying/merging, and empty zero/atomic eta/epsilon relations.
`Term.relation_toFull` proves raw compatibility by induction. Reduced
derivations preserve this relation by the proved syntactic inclusion and
existing full relation preservation; occurrenceMap then descends to the
reduced quotient. This is well-definedness, not faithfulness.

`occurrence_inclusion r` proves the reduced relation equals the full relation
of inclusion r. `occurrence_red`, `Coordinates.red_apply`, and
`Coordinates.red_coordinates` give, for full t : A → B,

```
(red t).relation u v ↔ t.relation (fromOcc A u) (fromOcc B v)
(red t).relation (toOcc A x) (toOcc B y) ↔ t.relation x y.
```

They reuse the existing inverse coordinate, graph and composition theorems.
No occurrence tags are collapsed or enumerated. Empty sets and repeated
equal literals retain their original treatment; label agreement does not
identify positions or make every relation injective.

`Reduced.Faithful P` is a separately defined proposition, with no proof
supplied. `normal_faithful_of_reduced` uses that explicit premise and the
surjective inclusion to prove normal-form faithfulness. The global transfer
uses normalization transport/recovery and the occurrence coordinates. These
are conditional implications, not a Boolean Coherence instance or new axiom.

## Declaration index

New modules and principal public declarations:

| Module | Constructed / proved declarations |
| --- | --- |
| ReducedSyntax | Op, Term, derived pair/copair/unit/dR/medial terms. |
| ReducedEquations | Constant, 61 Equation schemas, generated Derives. |
| ReducedCategory | Term.toFull, Equation.toFull, Derives.toFull; termSetoid/Hom/ofTerm, sound/equation, quotient id/comp/tensor/category; inclusion and identity/composition/tensor laws. |
| ReducedWitnesses | NormalForm.dual/dual_dual; form_true/normal_formula/normal_neg_formula; zero_top/fromTop_unique; mixedDisj/mixedConj and etaNF/epsilonNF. |
| ReductionTransport | castHom and composition/tensor cast laws; forward_formula/backward_formula/transport_formula; square criterion and transport id/comp/tensor laws. |
| SignedLiteralReduction | includeTerm/casts, redEta/redEpsilon/red; Compatibility negForward/negBackward, etaNF/epsilonNF and eta/epsilon; red_sound and representation. |
| ReducedOccurrences | Independent Term.relation and relation_toFull; Derives.relation and quotient occurrenceMap; occurrence_inclusion/red and coordinate formulas; Faithful and both explicitly conditional transfer theorems. |

## Verification and evidence

Clean baseline verification passed at c1004b0: 26 source files and 1616 audited
project declarations. Final working-source checks finished at 2026-10-22T21:45:14.684794+00:00.
Pinned Lean 4.35.0 and dependency-free Lake manifest are unchanged; production
still imports only Init through the project modules. Initial WSL memory was
15 GiB total, about 12 GiB available, no swap. One heavy build/audit ran at a
time with LEAN_NUM_THREADS=1; old constructions were reused without cleaning.

| Command | Actual result |
| --- | --- |
| bash scripts/verify.sh | Exit 0: **33 Lean source files**, **1950 project declarations**, strict build, source screening and transitive axiom audit. |
| python3 scripts/check-audit-boundaries.py | Exit 0. Direct public, private-name and hidden external illicit-axiom controls each rejected with Lean exit 1 and the expected named dependency. Public import closure passed. |
| python3 scripts/check-presentation-boundaries.py | Exit 0. Projection equality via rfl and zero without a correctly typed existing-arrow witness each rejected with Lean exit 1 and the expected diagnostic. |
| sha256sum -c SHA256SUMS in manuscript/ | Exit 0 for unchanged v4 TeX/PDF. |
| git diff --check | Exit 0. |

Permitted axioms remain exactly propext, Quot.sound and Classical.choice.
New schema/derivation inclusion, duality, object-normalization equalities,
mixed and compound raw terms, and raw red print no axioms. Quotient category
and inclusion use Quot.sound. The raw relation compatibility prints propext;
the principal red_sound/representation, comparison/coordinate compatibility
and conditional transfer results print propext and Quot.sound. No selected
new declaration uses Classical.choice. No proof hole, custom mathematical
axiom, native_decide, new dependency, or new full-presentation equation was added.

Durable evidence is under provenance/wsl-signed-literal-reduction/; runtime
logs are under .codex-work/signed-literal-reduction/. Commands, exit statuses,
raw control logs, signatures, source inventory and reference metadata are
retained. The strict log records baseline HEAD and dirty working source;
per-file hashes identify the actual code verified. Committed-source checks,
Downloads receipts and live SSH ref equality are recorded at completion
separately to avoid a self-referential commit SHA in these reports.

| Evidence | SHA-256 |
| --- | --- |
| strict.log.txt | `f6e400198ff7ae413ab2cf42866167301a07919b2266acac98823e8d1a1c3c57` |
| audit-boundaries.log.txt | `377643b2b8fc2ff8c9b228992b82e2fd82c36bf57a7c3914aa71572ffbf89ac0` |
| presentation-boundaries.log.txt | `306041f8b1c343270cc1f8c841a6a6f6aa03451e17bb5f034cd495d3b5f49f66` |
| source-SHA256SUMS | `bfdf2ee62a3db368e5aa3d60280c9a0be498046f1f1b4f233b50439d01afb8ea` |
| evidence-SHA256SUMS | `58e34d5329d15ee46863af40f3f95c13a919cbf149f09e7084405490a9c39ed6` |
| SignedLiteralReduction.lean | `b2990993b058127c0ea9ffa4b38e7f50a79cbed322cef672300e4a773abac0a1` |
| SIGNED_LITERAL_REDUCTION_HOSTILE.md | `7fc9ff59ac2ecf8135d5f42426ab44db2a8f69be7f0e547bff47e595d75b6bca` |
| SIGNED_LITERAL_REDUCTION_WRITING.md | `c5a0fbb6a443c82c316805dcb217848d648fd62cc466f36e57f11458b745178c` |

The report hash manifest excludes itself; finalized report hashes are in
report-SHA256SUMS. All three reports are delivered to Downloads and verified
byte for byte against their retained repository copies with conflict-preserving
filenames, following AGENTS.md.

## Reviews, remaining obligations and next task

The [hostile review](reviews/SIGNED_LITERAL_REDUCTION_HOSTILE.md) audits the
actual grammar boundary, equality definition, constructor coverage, typed mixed
maps, nonsemantic compatibility, and existential/conditional scope. It found
no confirmed flaw in the stated representation endpoint. This is author-side
work, not independent peer review.
The [writing review](reviews/SIGNED_LITERAL_REDUCTION_WRITING.md) directly
consults the verified cached Knuth–Larrabee–Roberts text, SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
Historical access records and earlier reports remain unchanged. No review
commentary was inserted into the manuscript or its LaTeX comments.

The following are not proved: Reduced.Faithful P; equality reflection of
inclusion; descent of raw red under the full defining equations; Boolean
Coherence; a faithful OccurrenceInterpretation; derived contravariant arrow
negation and its laws; remaining full proof-congruence/substitution-schema
and Appendix A bridges; unconditional actual maximality and the every-model
corollary. The three coverage milestones remain separate.

The source's later coherence argument uses Distributive Dicartesian Coherence
in the contextual induction on p.319 (inherited §11.5) and Zero-Identity
Distributive Dicartesian Coherence of §12.5 at p.321. Their Lean proofs,
the one-hole contextual g-eta/g-epsilon identities (pp.318–320), and the common
atomic eta/epsilon factorization are still outstanding. No such theorem was
assumed to prove this reduction.

Next concrete proof task: define typed one-hole normal-form contexts and
the g-conjunction/g-disjunction maps of pp.318–319, then prove the g-eta/g-epsilon
factorization identities on pp.319–320 in the actual Reduced quotient. Track
the earlier positive-core coherence results wherever the source invokes them.
The eventual endpoint is Reduced.Faithful P, after which the already compiled
conditional transfer supplies full Presentation faithfulness.

No independent kernel replay, independent complete source-transcription audit,
Challenge/Solution or Comparator comparison, official preflight/service
verification, new manuscript compilation/layout audit, novelty survey,
publication, visibility change or license change was performed.
