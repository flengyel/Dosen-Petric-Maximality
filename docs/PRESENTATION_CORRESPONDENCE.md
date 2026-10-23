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

The next concrete §12.5 work is `PositiveCoherence P`. Initial algebraic steps
are the zero-tensor law (0I xi), p.288, and the union-unit law, pp.290–291,
followed by the required positive Gentzenization/cut-elimination and coherence
argument. Neither that coherence premise nor general §11.5 coherence is
proved here. Contravariant arrow negation and the other bridges remain separate.
