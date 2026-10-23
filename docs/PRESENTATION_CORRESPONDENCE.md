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


## Signed-literal syntactic reduction (current checkpoint)

Source §14.2 p.318 (one-based PDF p.330) defines C with normal-form objects,
positive structural families and zero endomorphisms, plus only atomic eta_p
and epsilon_p. Reduced.Term has 21 constructor schemas. Arbitrary eta/epsilon
and n/r/rho are not reduced constructors. Equation has exactly the 61 inherited
positive ZIDL schemas; Derives is their equivalence/operation congruence closure.
Reduced.Hom is the quotient by Derives, independent of inclusion or relations.

The schema correspondence is exact by name; source anchors below are inherited
from the earlier positive equation index. Op packages both connectives. The
constant side condition excludes all literal leaves. No extra atomic eta/epsilon
or (0eta-epsilon) equation is inserted, and the two source-omitted (m e) laws
remain omitted. Equation.toFull and Derives.toFull compile for every schema.

| Source anchor | Reduced.Equation and matching Presentation.Equation |
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

| Source / result | Lean correspondence and scope |
| --- | --- |
| §14.1 pp.313–314 | NormalForm.dual/dual_dual; form_true/normal_formula/normal_neg_formula; forward_formula/backward_formula after endpoint casts, and transport_formula. |
| p.317 eta/epsilon connective and constant displays | Term.etaNF/epsilonNF use atomic primitives, symmetry for negative literals, both constant units, and the explicitly typed mixedDisj/mixedConj composites. These are not the same-connective medial. No general equality with a particular e'-abbreviation is claimed. |
| p.317 zero-arrow argument | Compatibility.etaNF/epsilonNF, using fromTop_unique/toBot_unique from actual category/zero laws, not relational faithfulness. |
| p.318 C syntax included into B | Term.toFull, Equation.toFull, Derives.toFull, inclusion and its identity/composition/tensor preservation. |
| Normalization transport on every full constructor | red and red_sound cover all 31 full constructor schemas; structural naturality, comparison inverses, zero_law and compound witnesses suffice. |
| Full normal-form hom-sets | representation proves every existing full arrow is inclusion of a reduced quotient arrow. It does not prove equality reflection or a quotient-level red function. |
| Source G on C and normalization coordinates | Independent Term.relation; relation_toFull, occurrence_inclusion, occurrence_red, Coordinates.red_apply/red_coordinates. All occurrence tags are retained. |
| Coherence transfer | normal_faithful_of_reduced/global_faithful_of_reduced are explicitly conditional on Reduced.Faithful P. No proof/axiom/instance for that premise is supplied. |

The contextual g-eta/g-epsilon maps and factorizations on pp.318–320 are now
proved below, with direct reduced derivations of their needed structural
instances. Common atomic factorization and complete support are also proved.
General Distributive Dicartesian Coherence (§11.5) remains unformalized, and
the §12.5 coherence input on p.321 is now isolated as PositiveCoherence P.
The p.314 equivalence, derived contravariant negation and its laws remain
separate obligations.
See [the reduction report](SIGNED_LITERAL_REDUCTION_REPORT.md) and both reviews.

## Contextual factorizations in the reduced syntactic category

The September 2007 source, §14.2 printed pp.318–321 (one-based PDF
pp.330–333), selects one occurrence, rather than every equal subformula.
`Reduced.Context P` records that position by a hole and left/right binary
placements, each indexed by `Reduced.Op`. Fixed formulas are arbitrary
NormalForm P objects. Thus the two placements and two Op cases give exactly
four recursive cases. `plug` replaces only the distinguished hole.

Write X = K[top], Y = K[bot], E_p = neg p ∨ pos p, and
D_q = pos q ∧ neg q. Here pos/neg denote complete signed literal leaves.
For the following tables `aR_o = assocR o`, `aL_o = assocL o`,
`c_o = swap o`, `d = dist`, and `dR = Term.distRight` (the derived arrow
of (dR c), p.145). Each semicolon means execute the left arrow first.
The source writes these paths in reverse order using ◦. Subscripts name
actual source/target summands; source disjunctive symmetry indices follow
Table 2, p.49 and are reversed relative to the Lean swap argument convention.

| Source recursion | Typed path defining `Context.gConj` |
| --- | --- |
| p.318, hole | `top ∧ B --leftOut conj B--> B` |
| p.318, C ∧ K | `(C ∧ X) ∧ B --aL_conj--> C ∧ (X ∧ B) --(id C ∧ gConj K B)--> C ∧ K[B]` |
| p.318, K ∧ C | `(X ∧ C) ∧ B --c_conj--> B ∧ (X ∧ C) --aR_conj--> (B ∧ X) ∧ C --(c_conj B X ∧ id C)--> (X ∧ B) ∧ C --(gConj K B ∧ id C)--> K[B] ∧ C` |
| p.318, C ∨ K | `(C ∨ X) ∧ B --dR C X B--> C ∨ (X ∧ B) --(id C ∨ gConj K B)--> C ∨ K[B]` |
| p.319, K ∨ C | `(X ∨ C) ∧ B --c_conj--> B ∧ (X ∨ C) --d B X C--> (B ∧ X) ∨ C --(c_conj B X ∨ id C)--> (X ∧ B) ∨ C --(gConj K B ∨ id C)--> K[B] ∨ C` |

| Source recursion, p.319 | Typed path defining `Context.gDisj` |
| --- | --- |
| hole | `B --leftIn disj B--> bot ∨ B` |
| C ∨ K | `C ∨ K[B] --(id C ∨ gDisj K B)--> C ∨ (Y ∨ B) --aR_disj--> (C ∨ Y) ∨ B` |
| K ∨ C | `K[B] ∨ C --(gDisj K B ∨ id C)--> (Y ∨ B) ∨ C --(c_disj Y B ∨ id C)--> (B ∨ Y) ∨ C --aL_disj--> B ∨ (Y ∨ C) --c_disj--> (Y ∨ C) ∨ B` |
| C ∧ K | `C ∧ K[B] --(id C ∧ gDisj K B)--> C ∧ (Y ∨ B) --d C Y B--> (C ∧ Y) ∨ B` |
| K ∧ C | `K[B] ∧ C --(gDisj K B ∧ id C)--> (Y ∨ B) ∧ C --(c_disj Y B ∧ id C)--> (B ∨ Y) ∧ C --dR B Y C--> B ∨ (Y ∧ C) --c_disj--> (Y ∧ C) ∨ B` |

**Rendered-source discrepancy.** The displayed disjunctive hole case on
printed p.319 actually reads `B ⊢ top ∨ B`. This is not merely a text-extraction
artifact: the rendered PDF was inspected. The immediately preceding general
type is `K[B] ⊢ K[bot] ∨ B`, and Table 2, printed p.49, defines
sigma-disjunction-left-in as `B ⊢ bot ∨ B`. The implementation uses this
well-typed named unit map and records the discrepancy. It does not add an
arrow of the displayed, inconsistent type. Render/source hashes are retained
in `provenance/wsl-contextual-factorization/source-consultation.json`.

All four factorizations below are now theorems of Reduced.Hom. The source
instances are obtained by h = ofTerm(eta p) or h = ofTerm(epsilon q).
The Lean theorems prove the stronger version for every existing h of the
same unit-domain/codomain type. Write r+ = rightIn conj and
r− = rightOut disj; 0 means a zero endomorphism only.

| Source equation | Exact execution-order path and compiled declaration |
| --- | --- |
| (gη), p.319 | `K[eta p] = r+ X ; (id X ∧ eta p) ; (id X ∧ 0 E_p) ; gConj K E_p`, each path X → K[E_p]. `Context.gEta`. |
| (gε), p.320 | `K[epsilon q] = gDisj K D_q ; (id Y ∨ 0 D_q) ; (id Y ∨ epsilon q) ; r− Y`, each path K[D_q] → Y. `Context.gEpsilon`. |
| (gηf), p.320, f : B → X | `f ; K[eta p] = r+ B ; (id B ∧ eta p) ; (f ∧ 0 E_p) ; gConj K E_p`, from B to K[E_p]. `Context.gEta_comp`. |
| (gεf), p.320, f : Y → C | `K[epsilon q] ; f = gDisj K D_q ; (f ∨ 0 D_q) ; (id C ∨ epsilon q) ; r− C`, from K[D_q] to C. `Context.gEpsilon_comp`. |

| Proof input / source | Actual reduced derivation |
| --- | --- |
| Table 2 p.49; (b delta sigma), (b delta), unit inverses, p.101 | `ReducedLaws` lifts only the unchanged inherited schemas to Hom. `ReducedStructure.rightIn_tensor` derives the right-unit/associator equation from pentagon, triangle, naturality and cancellation of explicit inverse arrows. `rightOut_tensor` is its inverse form; shuffle laws additionally use hexagon and symmetry. |
| (sigma dL), (delta dL), §11.5 p.270 | `dist_top` follows from `dist_snd` and product unit isomorphisms; `dist_bot` follows from `dist_inl` and coproduct unit isomorphisms. `distRight_top`, `disj_shuffle_dist_top`, and `conj_shuffle_dist_bot` expand the actual derived dR when needed. No same-connective medial is substituted. |
| p.319 induction, (0I) and zero_top = id | Reduced product/coproduct structures are constructed via existing generic DiagonalData derivations. `zero_top`, `zero_bot`, `fromTop_unique`, `toBot_unique` are derived inside Reduced, not reflected from Presentation. |
| p.319, final sentence of (gη) induction | The source invokes Distributive Dicartesian Coherence (§11.5) for the other context cases. Here all needed identities are derived directly: `gConj_nat/gDisj_nat`, `gConj_top/gDisj_bot`, then zero-based uniqueness and naturality. No general positive-core faithfulness theorem is assumed or claimed. |
| p.320, relation comparisons following (gηf)/(gεf) | `Context.Fixed`, `encode/decode`, injective disjoint embeddings, and `occurrence_map` give exact context coordinates. `gEta_comp_relation` compares input x with Sum.inl x in B ∧ E_p; `gEpsilon_comp_relation` compares output y with Sum.inl y in C ∨ D_q. No cross-type equality of relations is asserted. |
| p.321, final common-atomic factorization argument | Source explicitly invokes Zero-Identity Distributive Dicartesian Coherence (§12.5) on f1'' and f2''. Common atomic η/ε factorization and complete support are now proved below. The positive-core theorem and Reduced.Faithful remain unproved. Contextual or common factorizations alone are not coherence. |

`Context.map_derives` precedes quotient action. `mapTerm_id/mapTerm_comp`
are actual reduced derivations (Quotient.exact of equalities in the quotient
whose defining relation is Derives). They do not use inclusion reflection.
The functor at a fixed context is covariant from Reduced.category P to itself,
with object map plug and arrow map map; `map_id/map_comp` prove its laws.
No object-duality arrow operation or descent of full raw reduction is used.

## Common atomic factorization and positive middle terms

Source: September 2007 §14.2, printed pp.320–321 / one-based PDF
pp.332–333. Let E_p = neg p ∨ pos p and D_q = pos q ∧ neg q.
These are normal-form objects, not new primitive arrows. Write X_0 = A,
X_{k+1} = X_k ∧ E_{p_{k+1}}, Y_0 = B and
Y_{j+1} = Y_j ∨ D_{q_{j+1}}. All folds are left-associated. Semicolon
executes the left arrow first; the source writes the reverse order with ◦.
The source's n and m count atomic occurrences, so repeated equal labels occupy
different list positions.

| Source notation / location | Exact types and order | Lean correspondence |
| --- | --- | --- |
| p.320, eta^0 / eta^{k+1} = eta^k ∧ eta_p | eta^n : A_top^n → X_n, with eta^0 = id A; A_top^{k+1} = A_top^k ∧ top | `AtomicPorts.unitObject conj A n`, `etaTensor (.id A) ps` |
| p.320, epsilon^0 / epsilon^{j+1} = epsilon^j ∨ epsilon_q | epsilon^m : Y_m → B_bot^m, epsilon^0 = id B; B_bot^{j+1} = B_bot^j ∨ bot | `unitObject disj B m`, `epsilonTensor (.id B) qs` |
| p.320, conjunctive delta^n | A → A_top^n; insert the next top after the existing unit insertion | `unitIn A n`; `prefix_separated` proves etaPrefix = unitIn ; etaTensor |
| p.320, disjunctive delta^m | B_bot^m → B; remove the last bot before the earlier removals | `unitOut B m`; `suffix_separated` proves epsilonSuffix = epsilonTensor ; unitOut |
| pp.320–321, zero^n / zero^m | Endomorphisms X_n → X_n and Y_m → Y_m; id on the original block and a zero endomorphism at each added port | `mask conj A ps`, `mask disj B qs`, using `zeros` with identity accumulator |
| p.321, h-conjunction | X_all → X_used. At a kept occurrence tensor the accumulator with id E_p. At an absent occurrence project X_all_previous ∧ E_p → X_all_previous before the accumulator | `Selection.keep/absent`, `Selection.all/kept`, `inputPad`; positivity and `inputPad_natural` compile. Selection records positions, without comparing labels. |
| p.321, h-disjunction | Y_used → Y_all. At a kept occurrence tensor with id D_q. At an absent occurrence postcompose the accumulator with the first injection Y_all_previous → Y_all_previous ∨ D_q | `outputPad`; positivity and `outputPad_natural` compile. |
| p.321, f_i' | Initial eta/epsilon-free positive raw middle term at the term's own expanded endpoints | `AtomicFactor.middle`, with `positive`, exact eta_list/epsilon_list and quotient factorization. Generated through the earlier contextual identities. |
| p.321, f_i'' = zero^n ; h_input ; f_i' ; h_output ; zero^m (execution order) | Completed positive middle at common endpoints, including padding and both zero factors | `CommonAtomicFactor.middle₁/middle₂`. The construction uses one extraction of t₁ ∧ t₂ and positive diagonal/projection padding, described below; it does not claim a syntactic identity with a separately chosen source f_i'. `masked_support` proves that the final masks remove every auxiliary edge. |
| p.321, equal relations of completed middles | Equality of the entire relations, not just the embedded original block | `CommonAtomicFactor.relations_equal`, from support₁/support₂ and the original relation equality |
| p.321, §12.5 appeal | Faithfulness for the eta/epsilon-free, zero-identity distributive dicartesian arrow fragment | `PositiveCoherence P` is an explicitly unproved proposition. `faithful_of_positive_coherence` proves only its conditional consequence. |

**Confirmed rendered discrepancy.** The kept h-disjunction branch on printed
p.321 displays identity at `q_{k+1} ∨ neg q_{k+1}`. The epsilon primitive has
domain `q_{k+1} ∧ neg q_{k+1}`, as does the expanded port displayed immediately
above on the same page. The branch requires identity at that conjunction.
The rendered PDF was inspected at high resolution; this is not merely an
extraction artifact. `outputPad` uses the correctly typed identity at D_q,
and the discrepancy is retained here. The earlier p.319 unit typo remains
recorded in the contextual section. Neither display is added as an equation.
Source and rendering hashes are in the current source-consultation record.

The positive fragment is the inductive `Term.Positive` predicate: all 19
non-eta/epsilon constructor schemas of the existing Term grammar, recursively
closed under comp and both tensors. Zero endomorphisms remain included.
Both signs of literal and both constants remain allowed as objects. There is
no additional quotient: ambient arrow equality is the unchanged Reduced.Hom
quotient generated by Reduced.Derives and its 61 Equation schemas.

`Term.atomicView` recursively selects the first atomic syntactic occurrence,
with a positive preterm, one typed context and a remaining postterm.
AtomicSplit's eta/epsilon list equations preserve all repeated occurrences.
Its composition and both tensor clauses prove equality in Reduced, using
category and tensor laws. Each remainder replaces one contextual eta/epsilon
by the already proved g maps and zero endomorphisms. The strictly smaller
atomicCount proves termination of `atomicFactor`. Its lists are exactly the
original traversal lists, rather than deduplicated collections.

For two parallel raw terms, `commonAtomicFactor` performs one extraction on
`t₁ ∧ t₂ : A ∧ A → B ∧ B`. Thus the common lists are exactly the two traversal
lists concatenated in order. If M is that positive middle, the two unmasked
middle terms are

```
lift conj (diag A) ps ; M ; lift disj (fst B B) qs
lift conj (diag A) ps ; M ; lift disj (snd B B) qs.
```

`AtomicFactor.remap` proves that the same etaPrefix A ps and epsilonSuffix B qs
are outer factors for both, by `prefix_natural/suffix_natural`, associativity
and the proved product projection laws. This supplies common endpoints in a
single construction, not two unrelated existential factorizations. The source's
keep/absent padding maps and their factor-compatibility laws are also compiled.
No port permutation is needed in this implementation: every construction uses
the same left-associated concatenated word, including repeated positions.
Reassociation of composites uses the existing category law; `expand_append`
records the left-fold object identity. No unproved permutation or equality
reflection is invoked.

`embed conj A ps` and `embed disj B qs` are the iterated tagged first-block
injections; both are injective. `prefix_relation` is their graph and
`suffix_relation` is the converse graph at the output. `zeros_relation` and
`mask_relation` prove complete support directly from the raw relation grammar.
For each completed middle, support₁/support₂ state

```
relation middle u v ↔ ∃ x y,
  u = embedA x ∧ v = embedB y ∧ relation original x y.
```

The zero masks retain exactly the original input/output blocks, not all blocks
with matching labels. The nil folds are identity terms/maps. When an original
occurrence type is Empty, the existential support statement has no witnesses,
so the completed relation is empty; no auxiliary edge remains. These relation
proofs interpret proved syntactic equalities in the forward direction only.

The zero-tensor and union-unit algebraic steps are now proved below. The next
concrete §12.5 construction is typed positive Gentzen syntax and its
representation theorem, followed by cut elimination and restricted coherence.
PositiveCoherence P and general §11.5 coherence remain open. Contravariant
arrow negation and the other bridges remain separate.

## Positive-fragment zero and derived union algebra

Source: September 2007 §10.1, pp.219–220, §11.1 p.234, and §12.5,
pp.287–292. The target calculation on printed p.291 / one-based PDF p.303
was also checked in the rendered PDF. Semicolon executes the left arrow first.
All objects below are NormalForm P; P is arbitrary and literal signs unrestricted.

| Source label / location | Exact type, hypotheses and status in the source | Lean declaration (namespace Reduced) |
| --- | --- | --- |
| (0I), pp.287–288 | 0_A ; f = g ; 0_B for existing parallel f,g : A → B; inherited defining schema | Existing `Laws.zero_law`; new `zeroIdentity` packages it. |
| 0_(A,B) definition, p.288 | 0_A ; f : A → B requires a witness f : A → B; not a primitive arrow for every pair | `zeroOf`, `Term.zeroOf`, `ofTerm_zeroOf`. |
| p.288 two unlabelled independence consequences; (0 nat), §12.1 | Existing parallel witnesses give the same zero; a zero commutes with every existing arrow; composition absorbs witnessed zeros | `zeroOf_independent`, `zero_commute`, `zeroOf_pre`, `zeroOf_post`. |
| (00), p.288 | 0_A ; 0_A = 0_A, derived from (0I) | `zero_idempotent`, `zeroOf_zero`; `zeroOf_id` identifies the identity witness. |
| (0I ξ), p.288 | 0_A ξ 0_B = 0_(A ξ B), ξ = ∧ or ∨; a consequence, not an additional equation | `tensor_zero`, using reduced product/coproduct extensionality `conj_ext/disj_ext`. |
| (0 ξ), p.288 referring to §12.1 | For existing f : A → C and g : B → D, zeroOf f ξ zeroOf g = zeroOf (f ξ g) | `tensor_zeroOf`, from tensor composition and `tensor_zero`. Both factors are zeros. |
| Union definition, §10.1 p.220; (wm), p.219 | For parallel f,g : A → B: diag_A ; mix_(A,A) ; (f ∨ g) ; codiag_B | `Term.union` uses the equivalent diag_A ; (f ∧ g) ; mix_(B,B) ; codiag_B. `union_source` proves equality by (m nat); no primitive union constructor. |
| Generated congruence closure | Congruent f/f' and g/g' give congruent unions; positive inputs give positive union | `Derives.union` precedes quotient `union`; `Term.Positive.union`, `union_ofTerm`, `union_def`. |
| (∪ com), p.220 | Parallel f,g; consequence in ML, defining equation only in the alternative Gentzen GML system | `union_comm` derives it from diag/swap naturality, (c m) and codiag symmetry. |
| (∪ assoc), p.220 | Three parallel arrows; same source distinction | `merge_assoc`, `pair_assoc`, `union_assoc` derive it from (b m), mix naturality, and diagonal/codiagonal associativity. |
| (∪ idemp), p.220 | f ∪ f = f; consequence of (wm) in ML | `union_idem`, from diag naturality and `Laws.diag_mix_codiag`. |
| Both (∪ ◦), p.220 | h : X → A or k : B → C with parallel f,g : A → B | `union_pre` and `union_post`; `merge_nat` is the typed helper. |
| (∪0), pp.289–291 | Assumed in ZIML, but derived in ZIDL with (0I); the identity instance id_A ∪ 0_A = id_A suffices | `union_id_zero` uses the direct p.291 structural derivation, then `union_zeroOf` and `zeroOf_union` for any same-type existing witness. No (∪0) Equation is added. |
| G(f ∪ g) = Gf ∪ Gg, p.220 | Pointwise disjunction at the same tagged endpoints, independently of faithfulness | `Term.relation_union`, `occurrence_union`. |
| G0 empty, §12.5/§12.1 | Witnessed zero interprets as the empty relation; does not give equality reflection | `Term.relation_zeroOf`, `occurrence_zero`, `occurrence_zeroOf`. |

The derived union path has all intermediate types

```
A --diag--> A ∧ A --f ∧ g--> B ∧ B --mix--> B ∨ B --codiag--> B.
```

For the p.291 identity calculation, use B = A, f = id A and g = 0_A,
then expand mix by (d m), p.234. After diag and id ∧ 0, the remaining path is

```
A ∧ A --id ∧ inr--> A ∧ (A ∨ A) --d--> (A ∧ A) ∨ A
      --fst ∨ id--> A ∨ A --codiag--> A.
```

Witness independence replaces 0_A ; inr by 0_A ; inl. The middle
`(id ∧ inl) ; d` is `inl : A ∧ A → (A ∧ A) ∨ A` by (d k∨).
Injection naturality moves fst before inl. Projection naturality eliminates
the unused zero block, and diag ; fst = id, inl ; codiag = id finish.
These are reduced syntactic equalities; the alternative coherence appeal in
the source's last line is not used. No equality is inferred from relations.

Both-zero compatibility does not imply one-zero annihilation: for a literal p,
the second tagged edge survives in `0_p ∧ id_p` and `0_p ∨ id_p`.
Witnessed zeros require an existing arrow even when their relation is empty.
No hom-set bottom or semilattice typeclass is installed. The existing 21 raw
constructor schemas, 61 generating equations, and 19 positive schemas are
unchanged. The algebra actually holds for all existing Reduced arrows, so its
positive restriction requires no additional hypothesis beyond membership for
raw representatives. Positivity means eta/epsilon-free constructors, not
positive literal signs.

The direct merge/pair proofs replace only the §10.1 appeal to Lattice
Coherence for the union laws needed here. They do not replace Gentzenization,
cut elimination, restricted coherence, or the §12.5 faithfulness argument.
The historical dependency table in POSITIVE_ZERO_UNION_REPORT records the
then-open constructions. G0/G1 are now proved below; CODEX_NEXT_SESSION gives
the completed Atomic-k proof and the remaining cut-elimination dependencies. Signed-label preservation is not
fullness: no realization theorem for all signed-label-respecting relations is
assumed. Historical source discrepancies and access records are preserved.

## Typed positive Gentzen syntax and existential Gentzenization

Source: September 2007 §11.1 printed pp.238–246 (one-based PDF pp.250–258),
§11.5 pp.271–273 / PDF pp.283–285, and §12.5 pp.291–292 / PDF pp.303–304.
The pinned book hash is unchanged. The p.240 mixed composites were checked
in the rendered PDF. `Gentzen` below means `Reduced.Gentzen`; `G` is its
indexed syntax. All parameters P, signed normal forms and contexts are arbitrary.
Semicolon executes its left arrow first.

`fold o` is defined by structural recursion and `fold_as_foldr` proves equality
with List.foldr o.formula o.unit. Thus ante Γ = Γ.foldr conj top and
succ Δ = Δ.foldr disj bot, exactly the proposed objects. Empty lists have
different colours: ante [] = top, succ [] = bot. They are never identified.
Singletons are A∧top and B∨bot, with explicit right unit comparisons.

| Source / rule | Premises, conclusion and selected positions in G | Positive raw denotation / checked declaration |
| --- | --- | --- |
| p.240 identity basis; p.291 zero basis | identity l / zero l : G [lit l] [lit l], for every complete signed l | `encode (.id (.lit l))` / `encode (.zero (.lit l))`; `denote_identity/denote_zero`. No compound identity or zero leaf. |
| p.272 constant basis | topI : G [] [top]; botE : G [bot] [] | rightIn disj top : top → top∨bot; rightOut conj bot : bot∧top → bot. `denote_topI/denote_botE`. No G [] [] leaf. |
| cL, p.240 | G (Γ++X++Y++Θ) Δ → G (Γ++Y++X++Θ) Δ | Precompose `(exchange conj Γ X Y Θ).invTerm`; `denote_exchangeL`. Source swapped blocks are nonempty; the implementation also permits their explicit unital extensions. |
| cR, p.241 | G Γ (Δ++X++Y++Λ) → G Γ (Δ++Y++X++Λ) | Postcompose `exchange disj Δ X Y Λ`; `denote_exchangeR`. Lean swap arguments give execution-domain order; the book's disjunctive symmetry subscripts are reversed. |
| kL, p.241 | thinL inserts A at the selected gap Γ|Θ; source operation adds at the right | Product routing ignores just that new input. `thinLast` implements the source rightmost case with list-index transport and `thinLast_denote`. No search for all matching A. |
| kR, p.241 | thinR inserts A at Δ|Λ; the source front case is Δ=[] | Coproduct routing inserts the selected output branch; `denote_thinR`. |
| wL, p.241; y on pp.239,243 | gs=[Γ1,…,Γn], n≥2; premise repeated C gs ++ Θ, conclusion gaps gs ++ C::Θ | `copies C gs Θ` routes every selected C to the one retained position, fixes every gap/tail position, and uses product pairing. `denote_contractL`, `Route.product_get`, `product_positions`. |
| wR, pp.241,243 | Dual full separated multiple contraction. Primitive convention retains the last selected C; source retains the first | `contractRFirst` gives source order Δ ++ C::(gaps gs ++ Λ), n=1+length gs≥2. It composes the primitive with explicit block exchange and list transports; `contractRFirst_denote/count`. `denote_contractR`, `Route.coproduct_get`, `coproduct_positions` give component laws. No adjacent-contraction completeness theorem is assumed. |
| ∧L, p.242 | G (Γ++A::B::Θ) Δ → G (Γ++(A∧B)::Θ) Δ; principal pair selected by prefix/suffix | Precompose the prefix lift of assocL conj A B (ante Θ); `Rules.conjLeft`, `denote_conjL`. Θ=[] is the source's last-pair convention. |
| ∨R, p.242 | G Γ (Δ++A::B::Λ) → G Γ (Δ++(A∨B)::Λ) | Postcompose the prefix lift of assocR disj A B (succ Λ); `Rules.disjRight`, `denote_disjR`. Δ=[] is the source front-pair case, with its A/B names matched to position order. |
| ∧R, p.242 | f : Γ |- A,Δ; then g : Θ |- B,Λ; conclusion Γ++Θ |- A∧B,Δ++Λ | Input append inverse; f∧g; `mixedDisj A (succ Δ) B (succ Λ)` (source e'-disjunction indices A,B,succΔ,succΛ); output residue append. `Rules.conjRight`, `denote_conjR`, `sourceDisj_expansion`. Premise and residual order are preserved. |
| ∨L, p.242 | f : A,Γ |- Δ; then g : B,Θ |- Λ; conclusion A∨B,Γ++Θ |- Δ++Λ | Split residual input; swap principal sum to right; `Rules.sourceConj (ante Γ) (ante Θ) A B`; swap each product branch to principal-first order; f∨g; output append. `denote_disjL`. This is the source rule after explicit principal/premise-order comparisons, not an implicit reassociation. |
| mix, p.241 | f : Γ |- Δ; then g : Θ |- Λ; conclusion Θ++Γ |- Λ++Δ | Input append inverse; g∧f; mix_(succΛ,succΔ); output append. `Rules.mix`, `denote_mix`; order agrees with the displayed source. |
| contextual cut, p.241 | Head rule: f : Γ |- C,Δ, g : C,Θ |- Λ; result Θ++Γ |- Λ++Δ | Input append inverse; id_(anteΘ)∧f; d_(anteΘ,C,succΔ); ((swap_(anteΘ,C);g)∨id_(succΔ)); output append. `Rules.cut`, `denote_cut`. The distinguished occurrence is the head C in each premise. |
| full displayed cut, p.241 | f : Γ3 |- Δ2++[C]++Δ1; g : Γ1++[C]++Γ2 |- Δ3; result (Γ1++Γ2)++Γ3 |- Δ3++(Δ2++Δ1) | `cutAt` moves those selected C occurrences to the heads by block exchange, then cuts; `cutAt_denote/count`. List reassociation is transport of indices, not formula associativity. Extra equal C formulas remain fixed. |

The conjunction mixed comparison is transcribed directly from the rendered
p.240 definition. For X,Y,A,B its execution-order path is

```
(X∧Y)∧(A∨B) --id∧swap--> (X∧Y)∧(B∨A)
 --assocL--> X∧(Y∧(B∨A)) --id∧d--> X∧((Y∧B)∨A)
 --id∧swap--> X∧(A∨(Y∧B)) --d--> (X∧A)∨(Y∧B).
```

The old ReducedWitnesses.mixedConj is a separately typed witness composite;
no general equality with this source e' was available or used. It remains
unchanged. `sourceConj` supplies the actual source expression. The existing
mixedDisj does match the source e'-disjunction: `sourceDisj_expansion` proves
its expanded p.240 steps by tensor/category laws. Neither is same-connective
medial, and no new generator or equation identifies them.

`Iso` contains positive raw forward/backward terms with proved inverse laws.
`append`, `under` and `exchange` construct those comparisons from actual
associators, symmetries and units. `termTransport/reindex` transport only equal
list indices; their denote/count laws are proved by equality elimination.
`At` selects a whole-formula position by here/there. Route and copies preserve
fixed positions even when they contain the same C or repeated equal literals.
Their product/coproduct component laws and extensionality follow from the
already derived reduced universal properties, replacing a coherence appeal.

For actual singleton calculations, `appendNil_to`, `single_split/single_join`,
`append_insert/remove`, `mixedDisj_bot`, `disjInput_out/value` and `cut_pure`
prove the needed unit specializations. `cut_single` is composition after both
unit comparisons. No specialized d or mixed composite is merely declared an
identity. Empty residual contexts are top/bottom objects, never a shared ∅.
`G.no_empty` maps a putative G [] [] by denotation and inclusion to the proved
impossible full Hom(top,bot); it uses no faithfulness.

The source Gentzenization proof invokes associativity/symmetry coherence on
pp.245–246. Here `DiagonalData.assocR_fst/snd/assocR_pair/assocL_pair` derive
precise product formulas from the existing laws and the proved unit equation;
coproduct formulas use the opposite category. These provide the required
instances without assuming any earlier coherence theorem. The zero extension
uses `zeroNF_value`, both-zero tensor compatibility and zero_top/zero_bot.

`positive_represented` inducts on all 19 Positive schemas; the coverage table
in POSITIVE_GENTZENIZATION_REPORT identifies each branch. `gentzenization`
proves the requested singleton equation, and `gentzenization_decode` gives the
exact original-endpoint equation. These are existential results with cuts.
No canonical representative, cut elimination, Gentzen quotient, equation
preservation for a chosen translation or function on quotient arrows is claimed.

`G.relation` is the raw denotation relation; `occurrence_denote` connects it to
Reduced.occurrenceMap. `singletonOcc/singletonFrom` are inverse tagged maps
between each original occurrence type and its singleton fold. Their inverses
eliminate Empty unit branches. `gentzenization_occurrences` proves exact
pointwise relation agreement in those coordinates. Relations never prove
syntactic equality. Signed-label preservation is not fullness or faithfulness.

`cutCount`, `CutFree`, `Topmost` and `Atomized` are implemented analysis
interfaces. Atomic-k atomization, including denotation equality and preservation
of existing CutFree, is now proved as recorded below. The cluster/rank prerequisite
is also proved below. Blocked-contraction transformations, cut elimination,
restricted mix coherence, PositiveCoherence and Reduced.Faithful
remain open. No source citation supplies
those missing proofs, and no coherence premise is added to Gentzenization.

## Positive thinning atomization (Atomic-k)


The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
Its SHA-256 is
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12 (one-based). Formulas on printed pp.247 and
271 were inspected in rendering; render hashes/locations are recorded in
`source-consultation.json`. The source PDF stays in the ignored reference cache.

| Source location | Source role and exact scope used | Lean construction / replacement for source proof appeals |
| --- | --- | --- |
| §11.1 p.234, mixed structural equations; p.240 mixed-map definitions | The actual e′∧ has type `(X∧Y)∧(A∨B) → (X∧A)∨(Y∧B)`. e′∨ has type `(A∨X)∧(B∨Y) → (A∧B)∨(X∨Y)`. | Existing `Rules.sourceConj X Y A B` and `Term.mixedDisj A X B Y`; `sourceConj_nat`, `mixedDisj_nat` derive naturality of these composites. |
| §11.1 pp.241–243, exchange and separated multiple contraction | Exchange specifies prefix, two blocks, tail; contraction selects copies by the intervening gaps. Empty gaps and repeated equal formulas are legal. | Existing constructors are unchanged. New exchange components, `copies_index` and `Rewire.duplicate` derive block contractions from them. |
| §11.2 pp.246–247, Atomic-k; first compound-k rewrite | Left conjunction thinning becomes two sequential thinnings followed by conjunction-left; the dual handles right disjunction. | `conjLeft_head`, `disjRight_head`, `conj_thin_head`, `disj_thin_head`, `headThinL/R_denote`. Association is a proved arrow comparison. |
| §11.2 p.247, disjunctive compound-k rewrite; use of contraction and (m e∧) | Branch over A and B, then contract both duplicated surrounding contexts. The source invokes earlier coherence in its calculation. | `sourceConj_fst`, `branchL_core`, `branchL_denote`; proved using existing structural equations, constant specializations and union idempotence. |
| §11.2 p.247, dual compound-k case; §11.5 pp.270–271, omitted mixed equations | Right conjunction thinning requires the mixed arrow actually used by `Rules.conjRight`, and contraction on both sides. | `mixedDisj_inr`, `branchR_core`, `branchR_denote`; actual mixedDisj, injection naturality and `diag_mix_codiag`. |
| §11.5 pp.272–273, Atomic-k with constants | Atomic formulas include top/bottom; thinning by bottom on the left and top on the right is retained. The two empty folds have different colours. | `headThinL/R` retain actual primitive thinning at lit/top/bot; no constant-based replacement proof or empty-sequent leaf. |
| §12.5 pp.291–292, zero extension | Atomic zero leaves are among the bases; later zero cut-elimination cases are separate. | `atomize (.zero l) = .zero l`; existing atomic zero bases remain unchanged. Later zero reduction cases remain open. |

Neither omitted `(m e)` schema was added to `Reduced.Equation`. The results
below are sufficient projected/injected consequences, **not a claim to prove
both complete omitted schemas**. No new source discrepancy was confirmed in
this checkpoint; earlier correspondence entries and access records are retained.

## Categorical calculations before proof transformation

`sourceConj_fst X Y A B` proves, for all four normal forms:

```text
sourceConj X Y A B ; (fst X A ∨ fst Y B)
  = fst (X∧Y) (A∨B) ; mix X Y.
```

Both sides have type `(X∧Y)∧(A∨B) → X∨Y`. The left path goes through
`(X∧A)∨(Y∧B)`; the right through `X∧Y`. Its proof expands the actual
source-defined composite only in small structural lemmas, uses the existing
d-k/d-m laws and naturality, proves the top specialization, and maps A/B to
top. The specialization uses the established zero-derived top-domain
uniqueness. It does not use an interpretation to reflect equality.

The required dual calculation is `mixedDisj_inr A B X Y`:

```text
(inr A X ∧ inr B Y) ; mixedDisj A X B Y
  = mix X Y ; inr (A∧B) (X∨Y).
```

Both sides have type `X∧Y → (A∧B)∨(X∨Y)`. The left intermediate object is
`(A∨X)∧(B∨Y)`. The proof establishes the bottom specialization, its typed
unit inverse, and naturality along `fromBot A` and `fromBot B`. Initiality
and existing zero-derived bottom-codomain uniqueness justify the specialization.
There is no cancellation without an inverse and no appeal to full-Presentation
uniqueness. Both calculations are inside Reduced.Hom.

For `f : Hom X Y`, the branching left calculation has the complete path:

```text
(A∨B)∧X → (A∨B)∧(X∧X) → (X∧X)∧(A∨B)
 → (X∧A)∨(X∧B) → X∨X → Y∨Y → Y.
```

The arrows are `id ∧ diag`, swap, sourceConj, the two first projections,
`f∨f`, and codiag. `branchL_core` proves that this equals `snd ; f`.
After `sourceConj_fst`, its remaining duplicated-f expression is `f ∪ f`,
which equals f by the already proved syntactic union idempotence.

The branching right path is:

```text
X → X∧X → (A∨Y)∧(B∨Y) → (A∧B)∨(Y∨Y) → (A∧B)∨Y.
```

Its arrows are diag, `(f;inr A Y) ∧ (f;inr B Y)`, actual mixedDisj, and
`id ∨ codiag`. `branchR_core` proves equality to `f ; inr (A∧B) Y`.
The proof uses `mixedDisj_inr` and the existing diagonal–mix–codiagonal law.
No same-connective medial or older `ReducedWitnesses.mixedConj` is substituted.


The exact public endpoint is `Reduced.Gentzen.G.atomization`; its CutFree and
complete occurrence variants are `atomization_cutFree/atomization_occurrences`.
`headThinL/R` recurse on formulas and use no cuts. `atomThinL/R` move the
selected formula to an arbitrary gap by proved positional exchange. Rewire
scripts expand to existing exchange/contraction/reindex macros; all duplicated
context blocks are contracted with index and component proofs. The global
transformation covers all sixteen unchanged Gentzen schemas. It does not
give a decreasing rank, cut elimination, quotient translation or coherence.
See [the Atomic-k report](POSITIVE_THINNING_ATOMIZATION_REPORT.md), including
its four compound cases, constructor coverage, exact hypotheses and evidence.

## Typed whole-formula ancestors, finite clusters and cut rank

The September 2007 source and source hashes are unchanged. Printed pp.248–249
were inspected in rendering for this construction. The source's cluster
traces whole-formula positions and counts every node. Our existing positional
G rules use explicit context gaps and branch tags; their exact order appears
in the constructor table below.

| Source location | Definition / repository correspondence | Proved declaration |
| --- | --- | --- |
| §11.2 p.247, leaf formulae | Atomic identity leaves both sides. Thinning and logical introduction terminate at the selected principal whole formula. The source's rightmost/leftmost conventions are translated to the explicit list gaps of existing G, rather than matched by formula value. | `G.sourceArity`, `Leaf`; classification/count correctness and principal-leaf lemmas. |
| §11.2 pp.247–248, lower/upper contraction formulae | Lower position is `At.shift (gaps gs) (At.here C Θ)`; upper copies occur after each selected gap in `repeated C gs ++ Θ`. Fixed equal formulas in gaps are not selected copies. | `G.LowerContraction`, `selectedCopies`, `selectedCopies_length/nodup`, `contraction_predecessorsL/R`. |
| §11.2 p.248, parametric sequences | Each fixed position has one upper position in the designated premise, with the same side and whole formula. | `Premise.parent`, `G.predecessors_correct`, `sourceArity_correct`, `parametric_unique`. |
| §11.2 pp.248–249, finite cluster | Root is the selected conclusion position; leaves stop; contractions branch to all selected upper copies; parametric nodes have one successor. Node labels identify proof occurrences. | `TraceNode`, `ProofAddress`, `G.cluster_root`, `cluster_correct`, `cluster_address`, `TraceNode.cluster_children`. |
| §11.2 p.249, ρ | Total number of nodes, including the root and every branch; not longest-path length. | `G.rho_node_list`, `rho_eq`, `rho_one_iff_leaf`, `rho_child_lt`. |
| §11.2 p.249, contraction ranks | Apply ρ to the lower contraction position, for arbitrary proofs. | `contractionRankL/R`, `contractionRankL_eq/R_eq` give 1 plus the sum over every selected copy. |
| §11.2 p.249, left/right cut formulas and ranks | For `f : G P Γ (C::Δ)`, left cut formula is the right-side head of f; for `g : G P (C::Θ) Λ`, right cut formula is the left-side head of g. Sum their ranks. No Topmost premise is required. | `leftCutRank/rightCutRank/cutRank`, `cutRank_ge_two`, `cutRank_two_iff_leaves`. |
| §11.2 pp.249–250, tied contractions | A branching lower contraction node belongs to the chosen cut-formula cluster, on its specified side. | `TiedRight/TiedLeft`, both `tied*_iff_branching` theorems. Blocked forms and rewrites remain open. |
| §11.5 pp.272–273, constants | topI has a genuine target top position and botE a genuine source bot position; these are leaves although their literal-occurrence types are empty. Empty context colours remain distinct. | `topI_rank`, `botE_rank`; unchanged G/denotation/no_empty. |
| §12.5 pp.291–292, atomic zero extension | Both positions of an atomic zero basis term are leaves; later zero cut rewrites are not part of this construction. | `zero_leaf/zero_rank`; old zero grammar/equations unchanged. |

| Existing G schema | Selected conclusion positions and predecessor routing | Source arity |
| --- | --- | --- |
| identity | Both singleton literal positions are leaves. | 0 |
| zero | Both singleton literal positions are leaves. | 0 |
| topI | Only the target top position exists; it is a leaf. | 0 |
| botE | Only the source bot position exists; it is a leaf. | 0 |
| exchangeL | Source routed by inverse positional block exchange; target fixed. Parent map is the existing swapBlocks. | 1 |
| exchangeR | Target routed by inverse positional block exchange; source fixed. | 1 |
| thinL | Source principal at index Γ.length is a leaf; other positions invert existing Route.thin. | 0 or 1 |
| thinR | Target principal at index Δ.length is a leaf; other positions invert existing Route.thin. | 0 or 1 |
| contractL | Source at index (gaps gs).length branches to selectedCopies; fixed source/target positions have one predecessor. | gs.length or 1 |
| contractR | Dual target selection and every upper copy; fixed positions have one predecessor. | gs.length or 1 |
| conjL | Inserted whole A∧B at the source gap is a leaf. Upper A and B are not ancestors of it; fixed positions retain prefix/tail coordinates. | 0 or 1 |
| disjR | Inserted whole A∨B at the target gap is a leaf; fixed positions retain prefix/tail coordinates. | 0 or 1 |
| conjR | Source Γ++Θ routes to f/g respectively. Target head A∧B is a leaf; residual Δ++Λ routes to the appropriate premise, after its upper principal head. | 0 or 1 |
| disjL | Source head A∨B is a leaf; residual Γ++Θ routes to f/g after their principal heads. Target Δ++Λ routes directly to f/g. | 0 or 1 |
| mix | Conclusion is Θ++Γ and Λ++Δ: first blocks belong to g (branch 1), second to f (branch 0). | 1 |
| cut | Same conclusion order as mix. Surviving source Θ is in g after consumed C; Γ is in f. Surviving target Λ is in g; Δ is in f after consumed C. Neither consumed C is a conclusion position. | 1 |

`Premise.parent` is specified independently from inverse-fiber enumeration.
`predecessors_correct` proves local equivalence; `sourceArity_correct` connects
an independent rule/index classification to computed count. All source
classes are exhaustive and disjoint. Selected contraction copies have exact
count and are distinct positions even when labels agree.

`cluster_correct/cluster_children/cluster_address` give finite reachability,
immediate edges and valid proof-occurrence labels, with side and formula fixed
in TraceNode P s C. `rho_node_list` counts all explicit tree nodes;
`contractionRankL_eq/R_eq` sum all selected upper ranks. `cutRank_ge_two` and
`cutRank_two_iff_leaves` need no Topmost or atomization premise. Reindexing,
cut-free/atomized label propagation and tied-site characterization compile.
G.proofSize is the separate termination count, not rho or cutCount.

The cluster/rank prerequisite within G2 is complete. The two opposite-side
W1 thinning instances are now proved below. Source blocked patterns (p.250),
other W1 cases, W2–W6, Blocked-w, cut elimination and the positive coherence
inputs remain open. No relational reflection,
quotient rank or general transformation decrease is inferred by the cluster
construction alone. The local W1 rank decreases are proved separately below. See
[the report](GENTZEN_CLUSTER_RANK_REPORT.md) for exact hypotheses and evidence.

## Opposite-side thinning instances of W1

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.249–253, 272–273 and
291–292 were consulted; p.251 was also inspected in rendering. The verified
cache and access artifacts are recorded in source-consultation.json.
Historical source-access records are unchanged; no new discrepancy was confirmed.

| Source location | Typed correspondence and exact scope | Lean declarations / proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ = kR | Left contraction after right thinning equals right thinning after left contraction, on the unchanged antecedent copy positions. | `W1.oldL/innerL/newL`, `denoteL`; actual pre/postcomposition and `Reduced.Laws.assoc`. No Semilattice Coherence input. |
| §11.2 p.252, right analogue of Reducibility, applied to p.251 W1 | Right contraction after left thinning equals left thinning after right contraction. | `oldR/innerR/newR`, `denoteR`; separate checked associativity proof, no arrow-negation operation. |
| §11.2 pp.248–249, parametric clusters and rank; pp.251–252, rank condition | Opposite-side thinning has exactly one predecessor at the same At position. Contraction sums every selected upper copy. | `G.predecessors_thinR_left/thinL_right`, `rho_thinR_left/thinL_right`; existing `contractionRankL_eq/R_eq` and `selectedCopies_length`; `contraction_lossL/R`, `endpoint_lossL/R`. |
| §11.5 pp.272–273, constant basis and retained thinnings | Constants remain legitimate selected whole formulas. Left bot and right top thinning are retained operations, not replaced by special constant proofs. | Generic commutations allow all C,D; `emptyP_constantsL/R` at Empty. No literal-occurrence inhabitant is needed. |
| §12.5 pp.291–292, atomic zero basis and extension | Premise f is arbitrary and may contain atomic zero or cuts. These two calculations need no zero-specific rewrite or new zero. | Generic denotation/rank results depend only on constructors and categorical associativity/predecessor laws. Atomic-zero leaf and all existing zero laws are unchanged. |

These are derived local instances. They are not new defining equations,
the full W1 family, or a proof of the source's coherence appeal.

Both pairs preserve CutFree/Atomized equivalently, cutCount exactly and the
complete tagged relation. Let n = gs.length ≥ 2. contraction_lossL/R give
Rold = Rnew + n; endpoint_rankL/R give rho(new,x) = Rnew + 1;
endpoint_lossL/R give rho(old,x) + 1 = rho(new,x) + n. Both strict
inequalities compile for arbitrary P and arbitrary premises, including cuts.
Rank is syntactic and does not descend through reduced denotation. The
unchanged-endpoint relation comparison is a consequence of denotation equality.
See [the report](GENTZEN_W1_THINNING_REPORT.md) for full signatures, paths,
boundary examples and verification. No all-site replacement result is claimed.

## Opposite-side exchange instances of W1

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted;
p.251 was also inspected in rendering. The constant/zero extensions on
pp.272–273 and 291–292 were checked against the existing treatment.
Source-consultation.json records caches, hashes and access artifacts.
Historical source-access records are preserved; no new source discrepancy
was confirmed for these instances.

| Source location | Typed correspondence / scope | Lean declaration and actual proof input |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = cR | wL cR f = cR wL f; right exchange swaps the specified X,Y blocks and leaves antecedent contraction positions unchanged. | `W1.Exchange.oldL/innerL/newL`, `denoteL`; actual G.denote, ofTerm_comp, Reduced.Laws.assoc. |
| §11.2 p.252, right analogue of Reducibility | wR cL f = cL wR f; left exchange swaps X,Y and leaves succedent contraction positions unchanged. | `oldR/innerR/newR`, `denoteR`; separate checked associativity proof in the opposite direction. |
| §11.2 p.248, parametric sequences and predecessor definition | On the side opposite exchange, the exact typed At has one predecessor in the unique premise; no formula-label search. | `G.predecessors_exchangeR_left/exchangeL_right` from existing Premise.parent and TraceRoute.fiber_identity. |
| §11.2 p.249, rho and contraction rank; pp.251–252, rank requirement | Count all cluster nodes. Every selected upper copy contributes an exchange node. | `G.rho_exchangeR_left/exchangeL_right`; existing contractionRankL_eq/R_eq, selectedCopies_length and sum_map_one_add; `contraction_lossL/R`, `endpoint_lossL/R`, strict inequalities. |
| §11.5 pp.272–273, constants | Constants have whole-formula positions even with no literal occurrences. Empty folds are top/bot and remain differently coloured. | `emptyP_constantsL/R` use actual G Empty constant premises. Both-empty exchange still adds a node via rho equations. |
| §12.5 pp.291–292, atomic zero extension | Atomic zero leaves and arbitrary premises, including cuts, are allowed. No special zero law is needed for these two associativity calculations. | Generic results impose no restriction on f; atomic-zero constructor/zero equations are unchanged. No unwitnessed zero is added. |

The source invokes Semilattice Coherence for the larger W1 family. These two
local denotation equations are derived directly; the coherence theorem is
neither assumed nor claimed as a result. Binary context folds remain explicit,
with the actual exchange comparison arrows rather than strictified equality.

Both pairs preserve cutCount exactly, CutFree/Atomized equivalently and the
complete tagged relation. Unlike thinning, exchange adds no AtomicFormula
condition. With n = gs.length ≥ 2, contraction_lossL/R prove Rold=Rnew+n,
endpoint_rankL/R prove rho(new,x)=Rnew+1, and endpoint_lossL/R prove
rho(old,x)+1=rho(new,x)+n, with both strict inequalities. These rank facts
come from syntax and hold for empty blocks, never from denotation equality.
Other W1 cases and all-site replacement/reducibility remain open. See
[the exchange report](GENTZEN_W1_EXCHANGE_REPORT.md) for exact signatures,
intermediate types, checked examples and evidence.

## Opposite-side contraction instance of W1

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n corresponds to PDF page n+12, one-based. Printed pp.248–253 were
consulted, with p.251 also inspected in rendering. Constant and atomic-zero
extensions on pp.272–273 and 291–292 were checked against the existing
syntax. Access artifacts/hashes are retained; historical access records are
unchanged. No new source discrepancy was confirmed.

| Source location | Precisely used construction / condition | Lean correspondence / proof |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = wR | Move a left contraction through an opposite-side right contraction: wL wR f = wR wL f, with independent selected-copy lists. | `W1.Contraction.innerL/innerR/outerL/outerR`; `denote` uses actual pre/postcomposition and Reduced.Laws.assoc, not Semilattice Coherence. |
| §11.2 p.252, right-directed analogue of Reducibility | The same equality is used in reverse when targeting the right contraction. | `denote_reverse` is symmetry of denote; separate `right_directed_balance/decrease` prove the targeted right rank claim. No duplicate pair or arrow-negation construction. |
| §11.2 p.248, parametric sequences / clusters | A contraction has one proof premise. A position on its opposite side has one predecessor; its own lower contraction position branches to all selected upper copies. | `G.predecessors_contractR_left/contractL_right`, `rho_contractR_left/contractL_right`; existing parent/fiber and complete contraction-sum APIs. |
| §11.2 p.249, contraction rank; pp.251–252, directed rank requirement | Count all ancestry nodes, independently for the n selected left copies and m selected right copies. | `outerL_left/outerR_left/outerL_right/outerR_right`, inner-rank inequalities, two directed balances/decreases and named other-side increases. |
| §11.2 p.253, multiset-ordering argument for Blocked-w | Later elimination concerns contractions tied to a chosen cut and all affected sites; the displayed two-rank sum is not a supplied decreasing measure. | Only `endpointSum_balance` and equality for equal arities are proved. No all-site replacement, multiset measure, Reducibility or Blocked-w result is claimed. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants have whole-formula positions; atomic-zero bases are permitted and thinnings retained. | Arbitrary C,D/f in the theorem, actual constantTop/constantBot at Empty P, unchanged zero grammar and witnessed-zero policy. No new zero-specific equation is needed. |

The source's broader Semilattice Coherence appeal is not a Lean proof input.
These local instances follow from existing categorical equations and typed
ancestry. Context folds remain binary and explicitly typed; no strictification
or relation-kernel quotient is introduced.

With final selected positions x,y and inner ranks L,R, the exact table is:
outerL(left,x)=L+n; outerR(left,x)=L+1; outerL(right,y)=R+1;
outerR(right,y)=R+m. The left-directed move lowers left and raises right;
the reverse targets right and raises left. Both have equal Reduced denotation,
count/predicate preservation and complete tagged-relation equality.
endpointSum_balance gives S(outerL)+m=S(outerR)+n, with equality at n=m;
this is not a decreasing measure or unrestricted terminating rewrite system.
No arbitrary-context/all-site decrease is inferred. See
[the contraction report](GENTZEN_W1_CONTRACTION_REPORT.md) for exact signatures,
selected-copy proofs, examples, commands and evidence.

## Opposite-side unary logical instances of W1

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also in rendering. Constant/zero extensions on pp.272–273 and 291–292
were checked against the retained syntax. Source-consultation.json records
verified caches and access artifacts; historical access records remain intact.
No new source discrepancy was confirmed.

| Source location | Exact local use / types | Lean correspondence and actual proof input |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = ∨R | Left contraction commutes with unary right disjunction introduction at the specified gap. Both have source gaps gs ++ C::Θ and target Δ ++ (A∨B)::Λ. | `W1.Logical.oldL/innerL/newL`, `denoteL`; actual G.denote uses copies.product then f then Rules.disjRight.toTerm. Reduced associativity only. |
| §11.2 p.252, right analogue | Right contraction commutes with unary left conjunction introduction. Both have source Γ ++ (A∧B)::Θ and target gaps gs ++ C::Λ. | `oldR/innerR/newR`, `denoteR`; Rules.conjLeft.toTerm precedes f and copies.coproduct follows; reverse associativity. |
| §11.2 p.248, parametric clusters | Every unchanged-side position has one predecessor at the exact same typed At. | `G.predecessors_disjR_left/conjL_right`, `rho_disjR_left/conjL_right` from actual parent/fiber definitions. |
| §11.2 pp.247–249, logical leaf / all-node rank | Introduced whole formula is a leaf; tracing stops, without descending into premise A/B. An outer opposite-side contraction adds one node. | Principal Leaf proofs from sourceArity/index; sourceArity_correct proves empty predecessor lists; rho_leaf proves rank 1; `oldL/oldR_principal_rank` prove 2 and `newL/newR_principal_rank` prove 1. |
| §11.2 pp.249, 251–252, contraction rank and directed requirement | Sum every selected upper copy; each crosses one unary logical proof node. | Existing contractionRankL_eq/R_eq, selectedCopies_length and sum_map_one_add give exact contraction loss n and whole selected-endpoint loss n−1. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants remain whole formulas even when literal-occurrence types are empty; atomic zero leaves remain admitted. | Actual G Empty constant examples; arbitrary premises, including cuts/zero, in generic proofs. No new zero or coherence law is needed. |

The source's Semilattice Coherence appeal is not assumed. These are two
opposite-side unary logical instances only. Binary disjL/conjR, same-side
parametric W1 cases and all-site reducibility remain separate. The existing
syntactic quotient and non-strict binary context folds are unchanged.

Both directions prove Rold=Rnew+n, rho(new,x)=Rnew+1 and
rho(old,x)+1=rho(new,x)+n, with strict inequalities for n≥2. The introduced
principal has empty predecessors and rank 1 at the logical root; old/new
principal ranks are 2/1. Count, CutFree/Atomized and complete tagged relations
are preserved with no atomicity condition. These finish the specified
opposite-side unary W1 families (thinning, exchange, contraction, unary
logical introduction) and their duals. Same-side parametric W1 and binary
logical/reducibility cases remain separate/open. See
[the logical report](GENTZEN_W1_LOGICAL_REPORT.md) for signatures, paths,
fixed equal positions, next-task conditions and verification evidence.
