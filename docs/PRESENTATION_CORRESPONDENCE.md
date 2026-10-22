# Published presentation correspondence

This map concerns Došen and Petrić, *Proof-Theoretical Coherence*, September
2007 revision, [author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
The downloaded PDF has SHA-256
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
All page numbers below are printed pages. The corresponding zero-based PDF
page index is the printed number plus 11 (the one-based PDF page number is the printed number plus 12).
The source PDF and extracted text are local consultation evidence, not
redistributed as repository source.

## Objects and arrow grammar

`Formula P` is the source language with variables, top, bottom, conjunction,
disjunction, and negation. `Presentation.Term P A B` is indexed by both
endpoints. `comp f g` applies f and then g, hence represents the book's
`g ∘ f`. The interpretation uses the existing `Formula.Occ`; both binary
connectives have disjoint tagged occurrence sets, constants have empty sets,
and negation preserves the underlying positions. Repeated letters retain
different position tags.

| Source anchor | Source family / operation | Lean constructor or definition | Status / convention |
| --- | --- | --- | --- |
| §§2.7–2.8; §14.2, pp.316–317 | identities and composition | `Term.id`, `Term.comp` | Primitive identity family and binary arrow operation. |
| §§2.7–2.8; §14.2, p.316 | bifunctorial ∧, ∨ on arrows | `Term.tensor .conj`, `.disj` | The only other primitive arrow operations; negation on arrows is derived in the source. |
| §4.4 and §6.2; equation lists pp.332–333 | b in both directions | `Term.assocR`, `Term.assocL` for each `Op` | `assocR` has type A ξ (B ξ C) → (A ξ B) ξ C. |
| §5.1, p.107; §6.3–6.4, p.121 | symmetries | `Term.swap` | `swap .conj A B` is c∧_(A,B); `swap .disj A B` is c∨_(B,A). |
| §9.1, pp.185–186; §9.4; §9.6, p.207 | w-k | `Term.diag`, `codiag`, `fst`, `snd`, `inl`, `inr` | Primitive families; product/coproduct universal properties are derived. |
| §4.6, p.101; §6.4 and §9.6 | δ-σ | `Term.rightOut`, `rightIn`, `leftOut`, `leftIn` | Each `Op` has its own unit, top for conjunction and bottom for disjunction. |
| §8.2 and §8.4; §14.2 | mix | `Term.mix` | Primitive family A ∧ B → A ∨ B. |
| §7.2, p.132; §7.6, p.145; §11.1, p.234 | d = dL | `Term.dist` | Primitive A ∧ (B ∨ C) → (A ∧ B) ∨ C. |
| §12.5, pp.287–288; §14.2 | 0_A | `Term.zero` | Original primitive endomorphism; no primitive arrow for every pair of objects. |
| §14.1, p.310 | n→, n← | `Term.dnOut`, `dnIn` | Primitive mutually inverse arrows. |
| §14.1, p.310 | r∧→, r∧←, r∨→, r∨← | `Term.dmConjOut`, `dmConjIn`, `dmDisjOut`, `dmDisjIn` | Primitive De Morgan comparisons. |
| §14.1, p.312 | ρ∧→, ρ∧←, ρ∨→, ρ∨← | `Term.negTopOut`, `negTopIn`, `negBotOut`, `negBotIn` | Primitive constant comparisons. |
| §14.2, p.316 | η_A, ε_A | `Term.excludedMiddle`, `contradiction` | Primitive families; no guessed naturality equations. |
| §9.1, p.187; §9.4, p.198 | pairing and copairing | `Term.pair`, `copair`; quotient `pair`, `copair` | Derived using w and tensor. |
| §9.2, p.191; §9.6, p.207 | κ to top / from bottom | `Term.toTop`, `fromBot` | Derived from δ and k; uniqueness is proved in `CartesianFromDiagonal`. |
| §7.6, p.145, `(dR c)` | right dissociativity | `Term.distRight` | Derived, expanded in equation schemas; no extra primitive constructor. |
| §9.1, p.186, c-m; dual list p.336 | medial arrows | `Term.medial` | Derived associator/symmetry composite; the disjunctive dual has permuted arguments. |
| §14.2, p.317, `(0ηε)` | zero from η, ε and d | `Term.zeroConstruction`, `zeroConstruction_eq`, `zeroIdentity` | Construction is proved equal to primitive zero in the equation quotient. |
| §14.1, pp.311,315–316; §14.2 | negation on arbitrary arrows | No arrow-negation function yet | Derived, not primitive; definition and proof of independence of representatives remain open. |

## Generating equations and closure

The source inheritance is E(B) = E(ZIDL_top,bottom) ∪ E(I^neg_top,bottom)
(p.317), with E(ZIDL) obtained by adding `(0I)` (pp.288–291).
E(DL_top,bottom) is E(DL) ∪ E(L_top,bottom) **minus** `(m e∧)` and
`(m e∨)` (§11.5, p.270). Those two equations are not generators here.
The right-d equations are retained after expanding dR by `(dR c)`; the
source explicitly permits this eliminable abbreviation (p.145).

`Equation` has 71 Lean constructors. A constructor parameterized by `Op`
represents both connective schemas, so 71 is not a count of individual
source equation instances. Each row below identifies the constructor and
its quotient theorem `Presentation.Laws.<name>`; the exact typed equation
is in `PresentationEquations.lean`. The quotient theorems allow arbitrary
classes as arrow parameters, by induction on representatives.

| Source equation / printed page | `Equation` constructor and `Laws` theorem |
| --- | --- |
| (cat 1), p.332 | `id_comp` |
| (cat 1), p.332 | `comp_id` |
| (cat 2), p.332 | `assoc` |
| (xi 1), p.332 | `tensor_id` |
| (xi 2), p.332 | `tensor_comp` |
| (bR nat), p.332 | `assocR_nat` |
| (bL nat), p.332 | `assocL_nat` |
| (b b), p.333 | `assocR_L` |
| (b b), p.333 | `assocL_R` |
| (b 5), p.89; list p.333 | `pentagon` |
| (c nat), p.333; disjunctive indices reversed | `swap_nat` |
| (c c), p.107; list p.334 | `swap_swap` |
| (b c), p.107; list p.334 | `hexagon` |
| (delta/sigma nat), pp.332–333 | `rightOut_nat` |
| (delta/sigma nat), pp.332–333 | `rightIn_nat` |
| (delta delta)/(sigma sigma), p.101 | `rightOut_In` |
| (delta delta)/(sigma sigma), p.101 | `rightIn_Out` |
| (delta/sigma nat), pp.332–333 | `leftOut_nat` |
| (delta/sigma nat), pp.332–333 | `leftIn_nat` |
| (delta delta)/(sigma sigma), p.101 | `leftOut_In` |
| (delta delta)/(sigma sigma), p.101 | `leftIn_Out` |
| (b delta sigma), p.101 | `triangle` |
| (w nat), p.333 | `diag_nat` |
| (w nat), p.333 | `codiag_nat` |
| (k1 nat), p.333 | `fst_nat` |
| (k1 nat), p.333; disjunctive indices translated | `inl_nat` |
| (k2 nat), p.333 | `snd_nat` |
| (k2 nat), p.333; disjunctive indices translated | `inr_nat` |
| (b w), p.186 | `diag_assoc` |
| (b w), dual p.186; list p.336 | `codiag_assoc` |
| (c w), p.186 | `diag_swap` |
| (c w), dual p.186; list p.336 | `codiag_swap` |
| (b c w), p.186 | `diag_tensor` |
| (b c w), dual p.186; list p.336 | `codiag_tensor` |
| (b k), p.186 | `fst_assoc` |
| (b k), dual p.186; list p.336 | `inl_assoc` |
| (c k), p.186 | `snd_swap` |
| (c k), dual p.186; list p.336 | `inr_swap` |
| (w k), p.186 | `diag_fst` |
| (w k), dual p.186; list p.336 | `inl_codiag` |
| (w k), p.186 | `diag_snd` |
| (w k), dual p.186; list p.336 | `inr_codiag` |
| (k delta), p.191 | `fst_top` |
| (k delta), dual p.191; list p.338 | `inl_bot` |
| (c bottom)/(c top), p.121, inherited by p.207 | `constant_swap` |
| (dL nat), p.333 | `dist_nat` |
| (dR nat), p.333, dR defined by p.145 | `distRight_nat` |
| (dL and), p.132 | `dist_conj` |
| (dL or), p.132 | `dist_disj` |
| (dR and), p.132 | `distRight_conj` |
| (dR or), p.132 | `distRight_disj` |
| (d b and), p.132 | `dist_b_conj` |
| (d b or), p.132 | `dist_b_disj` |
| (m nat), p.333 | `mix_nat` |
| (b m), section 8.2; list p.336 | `mix_assoc` |
| (c m), section 8.4; list p.336 | `mix_swap` |
| (w m), p.219 | `diag_mix_codiag` |
| (d k and), p.234 | `dist_snd` |
| (d k or), p.234 | `dist_inl` |
| (d m), p.234 | `dist_mix` |
| (0I), p.288, inherited p.317 | `zero_law` |
| n-r/rho isomorphism equations, pp.310,312 | `dnOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `dnOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `dmConjOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `dmConjOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `dmDisjOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `dmDisjOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `negTopOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `negTopOut_out` |
| n-r/rho isomorphism equations, pp.310,312 | `negBotOut_in` |
| n-r/rho isomorphism equations, pp.310,312 | `negBotOut_out` |

`Derives` is equivalence closure plus congruence for composition and the two
tensors, with injections of these 71 schemas. This is syntactic generated
equality. `Term.subst`, `Equation.subst`, and `Derives.subst` prove the
source substitution rule `(su)` admissible, including endpoint substitution
and the positive-letterless side condition. No relation-kernel equality is a
generator. Closure under each primitive arrow operation therefore descends
to `Hom`; derived operations are composites of descended operations.

The following source consequences are **not** inserted as generators:
`(w k k)` (p.187), terminal/initial uniqueness (pp.191,207), `(b δ)`,
`(b σ)`, `(δ σ)` (p.101), `(c δ σ)` (§5.3), `(0I ξ)` (p.288),
`(0ηε)` (p.317), arbitrary-arrow negation, and the naturality of n-r
obtained by coherence (p.316). The universal properties and `(0ηε)` are
proved here; the other consequences are not all supplied as named lemmas.
The positive-letterless condition in `Constant` means precisely the language
in the source side condition on p.121; it excludes variables and negation.

## Occurrence assignment

The assignment is the tagged-coordinate version of the source functor G to
relations (introduced in §2.7 and extended in §§14.1–14.2; η/ε are assigned
empty relations on p.317). It has the following explicit Lean realization.
The equality-preservation proof is separate from this definition.

| Constructor / derived operation | Relation in `Term.relation` or quotient declaration |
| --- | --- |
| identity, composition | `Relations.graph id`, `Relations.comp` |
| either tensor | `Relations.sumMap` on the two component relations |
| `assocR`, `assocL` | graphs of `Relations.reassoc`, `Occurrence.unassoc` |
| `swap` | graph of `Occurrence.exchange` |
| `diag`, `codiag` | `Relations.pair` / `copair` of two identity graphs |
| `fst`, `snd`; `inl`, `inr` | `Relations.fstRel`, `sndRel`; graphs of `Sum.inl`, `Sum.inr` |
| `rightOut`, `leftOut`; `rightIn`, `leftIn` | graphs of `Occurrence.dropRight`, `dropLeft`; graphs of `Sum.inl`, `Sum.inr`; unit positions are Empty |
| `mix`, n/r/rho comparisons | identity graphs on their definitionally matching position types |
| `dist`; derived `distRight` | graphs of reassociation / inverse reassociation; the latter is proved in `Term.relation_distRight` |
| primitive and constructed zero | empty relation; quotient `occurrence_zero` uses `zeroConstruction_eq` |
| η, ε | empty relations; `occurrence_excludedMiddle`, `occurrence_contradiction` |
| derived pairing/copairing | relation pairing/copairing, proved by `occurrence_pair`, `occurrence_copair` |
| derived arrows to top / from bottom | empty relations, proved by `occurrence_toTop`, `occurrence_fromBot` |

## Quotient and interpretation boundary

`Hom A B` is `Quotient (termSetoid A B)` where the setoid relation is
`Derives`, not equality of interpreted relations. `comp` and `tensor` use
`Quotient.liftOn₂` and their explicit congruence proofs. `category` proves
the category laws from `Laws`. `operations` derives the entire `Structure`
interface from the published equations, using the generic diagonal argument
in `CartesianFromDiagonal`. `zeroIdentity` uses the constructed zero.

The historical presentation report records the occurrence equations and
operation-preservation laws, keeping well-definedness distinct from
faithfulness. The normalization construction below now supplies manuscript
§3 object normal forms, both inverse comparisons, and their occurrence
correspondence. Boolean Coherence (§14.2, conclusion p.321) remains open.


## Actual normalization comparisons (current checkpoint)

`Presentation.normalization P` instantiates the existing `Normalization` record
for every `P : Type u`. It constructs the object assignment and comparison
isomorphisms on printed pp.313–314. It does not claim the complete source
functor F, its naturality, the p.314 Auxiliary Lemma, or the equivalence.
The following are derived arrows, not additional primitive operations or
new generating equations. `NN` denotes `Presentation.NegationNormalization`
and `NC` denotes `Presentation.NormalComparison` in this table.

| Source anchor / zero-based PDF page | Typed comparison and available equations | Lean construction / status |
| --- | --- | --- |
| §14.1 p.310 / 321, n displays | n→ : ¬¬A → A and reverse n←; both inverse displays | `NC.doubleNeg`, using existing `dnOut/dnIn` and `Laws.dnOut_in/out`. |
| p.310 / 321, r∧ displays | r∧→ : ¬(A∧B) → ¬A∨¬B and reverse; both inverse displays | `NC.deMorganConj`, using `Laws.dmConjOut_in/out`. |
| p.310 / 321, r∨ displays | r∨→ : ¬(A∨B) → ¬A∧¬B and reverse; both inverse displays | `NC.deMorganDisj`, using `Laws.dmDisjOut_in/out`. |
| p.312 / 323, rho displays | ρ∧→ : ¬top → bot and ρ∨→ : ¬bot → top, their reverses, both inverse displays | `NC.negTop/negBot`, using `Laws.negTopOut_in/out` and `negBotOut_in/out`. |
| p.313 / 324, F on objects | Negation only at signed variable leaves; constants retained/swapped as appropriate | `NN.form A false` normalizes A, `form A true` normalizes ¬A; structural recursion on A. |
| p.313 / 324, i_A and i_A^-1 clauses | Variable and negative variable identities; connective tensors; i_¬¬A = i_A ∘ n→; negative connective via r→ then tensor negative comparisons; inverses reverse the order | `NN.comparison`, with `NC.refl/trans/conj/disj`; arrows and inverse proofs are built simultaneously. |
| p.314 / 325, constant clauses and following identities | Constants use identities, negative constants use ρ→/ρ←; i_A^-1 ∘ i_A = 1_A and i_A ∘ i_A^-1 = 1_FA | `NN.forward/backward`, `forward_backward/backward_forward`, `Presentation.normalization`. Inverses use only existing category, tensor, and comparison equations. |
| p.314 / 325, G clauses | G negA = GA and comparison images are identity relations | `NN.toOcc/fromOcc`, inverse coordinate laws, `forward_graph/backward_graph`. In tagged coordinates tensors use Sum.map, so distinct occurrences stay distinct. |
| Manuscript §3, relation transport | Normal-form transport uses backward_A, f, forward_B | `NN.transport_relation/transport_apply/transport_coordinates`; categorical recovery/injectivity reuse the old `Normalization` lemmas. |

For each Out : X → Y and In : Y → X above, the source's unnumbered displays
are In ∘ Out = 1_X and Out ∘ In = 1_Y. The Lean equations are
`comp Out In = id X` and `comp In Out = id Y`. No extra equation labels are
invented. The inverse proofs do not compare relations to conclude equality.

`Formula.signedLabel` records the letter and parity along a tagged occurrence
path; it agrees with `NormalForm.literalAt` on normal forms. The coordinate
maps preserve this full literal in both directions. Constants have Empty
occurrences, handled by empty elimination; `NN.no_occ` covers any empty source
occurrence type, and `repeated_negative_tags` checks distinct negative repeats.
This comparison statement is not signed-label preservation along every arrow.

The n/r naturality consequences discussed on pp.311/316, rho naturality,
derived contravariant arrow negation, and the p.314 Auxiliary Lemma/equivalence
remain unproved. No such consequence has been added to `Equation` to complete
this construction. The raw occurrence preservation proof and its quotient
well-definedness were reused unchanged. Full Boolean Coherence remains open.
See [the normalization report](NORMALIZATION_REPORT.md) for exact hypotheses,
declarations, verification, evidence hashes, and both review boundaries.


## Global signed-edge invariant (current checkpoint)

`Presentation.Term.relation_signedLabel` proves the complete literal invariant
by induction on all 31 primitive constructor schemas in `Term`. The parameters
are arbitrary P, formulas A,B, term t : A → B, positions x,y, and an edge.
There is no nonemptiness, decidable-equality, or coherence premise.

| Source grammar / interpretation anchor | New proof correspondence |
| --- | --- |
| §2.7, §14.2 p.316: id, composition, both tensors | Equal position; intermediate occurrence and transitivity; matching Sum branches and child invariants. |
| b,c,w-k,delta/sigma,m,d families indexed above | Graph equalities and branch decomposition retain the signed subformula label. Unit branches are Empty; diagonals and codiagonals copy/merge without identifying tags. |
| §14.1 p.310 and G clause p.314: n/r | Both double-negation directions use `Literal.flip_flip`; all four De Morgan cases preserve the flipped child label on each branch. |
| p.312 and G clause p.314: rho | Empty occurrence endpoints; no chosen dummy coordinate. |
| §12.5 and §14.2 pp.316–317: 0,eta,epsilon | Empty assigned relations, hence no edge to check. |
| Existing generated-equation quotient | `occurrence_signedLabel` uses quotient induction and `occurrence_ofTerm`; no equation or definition of equality changes. |
| Manuscript v4 §3 signed-literal paragraph | `occurrence_literal` specializes through `signedLabel_eq_literalAt`; letter/polarity and both opposite-sign exclusions follow. |
| Existing normalizer coordinate theorems | `NegationNormalization.transport_literal/transport_literal_coordinates` use `transport_apply`, `literal_fromOcc`, and `transport_coordinates`. |

This direct invariant does not rely on the source's unconstructed signed-literal
equivalence. It proves a property of the well-defined occurrenceMap, not its
faithfulness. `diag_copies` and `codiag_merges` exhibit edges between repeated
letters and distinct tags, so neither functionality nor injectivity of each
relation follows. The unchanged `SignedLabelPreservation` definition still
requires a separately supplied faithful interpretation. See
[the signed-label report](SIGNED_LABEL_REPORT.md) and both linked reviews.
