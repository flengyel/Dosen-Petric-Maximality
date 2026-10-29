# Actual source maximality and derived negation

The actual equation-generated source category now satisfies maximality for full
proof congruences closed under uniform endosubstitution. The declarations are
`Presentation.maximality`, `congruence_dichotomy` and `raw_maximality`, for arbitrary
variable type P. This includes the manuscript's nonempty-P statement. The full
paper is still being formalized: its short q_A/e_A proof, model corollary,
remaining substitution-coordinate claims and other appendix claims are separate
obligations. The existing symmetric-fold route is preserved.

## Source category and reduction

`Reduced.reduceHom` is an actual quotient map, not a field supplied to a theorem.
Its well-definedness follows from the proved Reduced faithfulness and the
existing occurrence calculation for every raw source term. Composition, identities
and both tensors are preserved. The inclusion functor and reduction functor have
the specified object maps. `normalizationNaturalIso` proves the source-side
natural isomorphism with identity; `reduction_inclusion` proves the reverse
recovery with explicit normal-form endpoint casts. `recoverHom` is inverse to
reduction on each original typed hom-set. Empty hom-sets are retained.

## Derived negation

`Reduced.Term.dual` reflects the complete reduced grammar contravariantly.
Composition reverses, tensors exchange, associators exchange directions, ports
exchange projections and injections, distributor becomes the actual right
distributor, and eta/epsilon exchange. Literal signs flip without merging tags.
`Term.dual_relation` proves the converse relation in exact dual coordinates.
Proved faithfulness then supplies quotient descent, `dualFunctor`, and
`dualHom_involutive` with explicit casts. No general duality of Gentzen proofs
is assumed or used.

`Presentation.negate` transports this construction through actual source
normalization. Identity and reversed composition laws give `negationFunctor`.
Both directions of double-negation and both De Morgan naturality equations are
proved. `doubleNegationNaturalIso` packages the natural double-negation comparison;
De Morgan inverse equations and constant comparison inverse equations remain the
existing actual source laws. Their endpoints and directions agree with §14.1,
printed pp.310–314 of the September 2007 source. `occurrence_negate` proves that
this arrow operation is exactly converse at original occurrence tags.

The source operation also has explicit raw syntax. `forwardTerm` and
`backwardTerm` use only the existing primitive grammar and denote precisely the
original normalization comparisons. `Term.negate`, `negateTerm_denotes` and
`negate_derives` give a raw construction compatible with generated equality.
Compatibility of derived negation with whole-arrow uniform substitution is a
remaining operation-law obligation; it is not silently inferred from object
substitution or from one interpretation's kernel.

## Congruence correspondence and maximality

`ProofCongruence` is an equivalence relation on existing quotient hom-sets closed
under composition, both tensors and actual derived negation. Every other
primitive constructor has no arrow argument. Pairing and copairing closure are
derived from these fields. `RawProofCongruence` is the corresponding typed raw
relation, includes every published defining equation and has the same operation
closure. Uniform endosubstitution closure is specified separately on both sides.

`of_derives` proves inclusion of generated equality. `toQuotient` and `toRaw`
construct the two relations; `raw_quotient_rel` and `quotient_raw_rel` prove both
pointwise inverse correspondences. Both closure-transfer theorems are proved.
The `fragment` restriction and `fragment_closed` instantiate the existing
relative theorem. Actual occurrence interpretation, normalization, signed labels,
substitution and double negation supply every other input. No mathematical input
is an uninstantiated record or an axiom, and no quotient coherence is assumed.

`maximality` concludes totality only on already existing hom-sets. The dichotomy
is equality versus that total relation; it does not create arrows. `raw_maximality`
uses inequality modulo the original generated equality, not raw syntactic
inequality. These are actual-presentation instances of the retained symmetric-
fold proof. The distinct three milestones do not constitute the complete-paper
certificate; the different short proof and all remaining correspondence claims
still have to be proved.

## Verification and delivery

The frozen source is checked with pinned Lean 4.35.0 and Init/core dependencies.
`bash scripts/verify.sh`, every public check file, full transitive axiom/source
closure, both boundary suites and all focused rejection controls are required.
The new controls reject an omitted substitution-closure hypothesis, omitted
involution casts, covariant composition and a repeated-tag port crossing. Failed
development attempts are retained separately from expected rejection controls.
Exact counts, commands, exits and hashes are in
`provenance/wsl-full-source-bridges/FINAL_VERIFICATION.json`; the source archive
is read back and compared with committed bytes before delivery.

The reports and changed records are retained under docs/ and docs/reviews/ and
delivered from committed bytes to Downloads, preserving differing files. Exact
paths and hashes are in DELIVERY_REGISTER.json and DELIVERY_RECEIPT.json in that
provenance directory. The original stash and all nine manuscript blobs are
preserved; no new manuscript defect was found. These reviews and checks are local
author-side work. Independent replay, Comparator, official/service verification
and publication have not been performed.
