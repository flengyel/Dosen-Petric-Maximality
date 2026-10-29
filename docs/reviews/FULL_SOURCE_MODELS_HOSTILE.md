# Local hostile review: complete-source models

Scope: the twelve new model modules and their correspondence to v7 §5
`cor:models`, against the actual source quotient. This is an author-side review,
not an independent replay or external referee report. Whole-paper status: unknown
until the separately recorded Appendix A/action/scope duties are completed.

## (A) Kill-shots / hard blockers

No confirmed blocker in the model corollary. The key tests are whether the model
is the full primitive presentation, whether the universal family is nonvacuous,
and whether all native target arrows enter the conclusion. `Primitives.evaluate`
covers the full raw grammar; `canonicalInterpretation` constructs an interpretation
at every valuation; `model_corollary` uses native pairing and both native beta laws.

## (B) Major weaknesses

1. **unproved; high; evidence: structural_argument.** Anchor:
   `SemanticUniversalAgreement.lean`, `congruence`, “.of_closed_fragment”. A direct
   claim of negation closure from functoriality alone would leave a gap because
   negation is a derived raw macro. Resolution: `PresentationFragmentMaximality.lean`,
   `fragment_dichotomy` and `ProofCongruence.of_closed_fragment` prove the additional
   closure from the previously established fragment maximality. No model axiom
   supplies it. Downstream: applying actual full maximality is justified.
   Repairability: resolved in source, no pending assumption.
2. **unsupported_generalization; high; evidence: structural_argument.** Anchor:
   `SemanticModelCorollary.lean`, `model_corollary`, “∀ {Y Z : X} (a b : C.Hom Y Z)”.
   An image-only collapse would not establish this conclusion. Resolution: the
   constant valuation reaches each object, and native `S.pair a b` with
   `M.bicartesian.pair_fst/pair_snd` covers arbitrary arrows. No surjectivity field.
   Downstream: the printed preorder conclusion is exact. Repairability: resolved.

## (C) Minor issues

**ambiguous; medium; evidence: structural_argument.** Anchor:
`SemanticBicartesian.lean`, `Model`, “SatisfiesTheory”. These are axioms defining a
model of the full source theory, not an uninstantiated theorem interface that
repeats the corollary. `evaluate_derives` proves generated soundness and
`Source.model` instantiates every field. The report explicitly distinguishes
model axioms from proved bridges. Resolved; preserve this explanation.

## (D) Cross-section consistency failures

No new mathematical inconsistency confirmed. Source-derived negation is not
misdescribed as an additional native primitive. Universal agreement is taken over
all full interpretations, and `iff_valuations` proves its equivalence with all
canonical valuations. Both tensors, all 31 constructor families, signs, repeated
tags, constants and existing-arrow zeros remain present. Original coherence is
used only in the intended category. Nonempty P is explicit and used to choose p;
source-model instantiation itself supports Empty. Full-paper coverage still marks
Appendix A/action laws and FP-SCOPE-20261029 as unfinished.

## (E) Acceptance conditions, non-negotiable

1. Strict pinned build and transitive axiom/source audit must pass.
2. All 34 public check files and boundary audits must pass.
3. All 66 expected rejections must be confirmed, including the five model controls.
4. Exact source archive, committed-byte comparison and conflict-preserving verified
   Downloads delivery must be retained.
5. Preserve both main proof routes, prior evidence, manuscript versions and stash.
6. Continue remaining full-paper duties; do not certify the paper from this corollary.

The immutable final evidence records the status of conditions 1–5; condition 6
continues under the existing contract.

## (F) Not checked / uncertainty log

Independent kernel replay: unavailable/not performed. Comparator, official
preflight, service verification and publication: not performed. The construction
is core Lean with no new dependency. Standard target models with a separately
chosen native contravariant negation functor are treated through their complete
primitive signature; no unproved claim equating an arbitrary additional functor
with source negation is needed or made. Complete external-model classification
and the remaining Appendix A are outside this milestone.

Strongest confirmed issue: none left in the checked corollary. Strongest suspected
failure mode was omitted full negation closure; the explicit fragment-dichotomy
proof resolves it. Recommendation: accept this model milestone if its recorded
local checks pass; continue the full-paper work. Whole-paper status remains open.
