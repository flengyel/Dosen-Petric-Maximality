# Complete-source model corollary

The model corollary in v7 §5 (`cor:models`) now has a proof for the actual
equation-generated presentation. `PresentationSemantics.model_corollary`
concludes that every existing target hom-set is subsingleton. It requires a
nonempty source variable type and agreement of two distinct source arrows at
every valuation. Target objects, target arrows and source variables have
independent universes. The intended source model is fully instantiated,
including its nonthin Nat instance and its empty Hom(top,bot).

The public construction is in twelve modules, including `SemanticSignature.lean` through
`SemanticModelCorollary.lean` and `PresentationFragmentMaximality.lean`.
Exact declaration paths and line numbers are in
`provenance/wsl-full-source-models/DECLARATION_ANCHORS.tsv`.

| Claim | Actual declaration | Correspondence |
| --- | --- | --- |
| Full primitive source semantics | Objects, Primitives, formula, Primitives.evaluate | Every one of the 31 raw constructor families; both tensors and all comparison, unit, zero and logical arrows. |
| Equational model and quotient functor | SatisfiesTheory, evaluate_derives/evaluateHom/evaluationFunctor | Model axioms quantify over the actual generating Equation relation; preservation of Derives and quotient descent are proved. |
| Full structure-preserving interpretation | Interpretation, canonicalInterpretation | Object identifications and every primitive preservation law; identities/composition from Functor. Heterogeneous equality retains endpoint identifications. |
| Substitution composition | Interpretation.precompose | Constructed from the proved whole-arrow substitution functor, for independent source variable universes. |
| Free evaluation correspondence | object_evaluation/raw_evaluation/hom_evaluation | Every full interpretation agrees with evaluation at its variable assignment; exhaustive raw constructor induction and quotient descent. |
| Actual model witness | Source.equations/bicartesian/model | Every model input is instantiated by actual source operations and proved source equations, at every valuation. |
| Universal agreement | Agreement.fragment/fragment_closed/congruence/closed/iff_valuations | Whole interpretation family, not a fixed kernel; full congruence and equivalence with all canonical valuations. |
| Model corollary | model_corollary/model_corollary_interpretations | Actual maximality makes agreement total; equal target projections and product beta laws equate arbitrary native arrows. |

`Model` specifies the complete primitive presentation, genuine bicartesian
universal properties for all native target arrows, and the zero-identity law.
It assumes neither coherence, thinness, quotient soundness, substitution closure,
nor surjectivity of a source functor. The equation axioms are the ordinary
model definition; `evaluate_derives` proves their closure. `Source.model P R`
instantiates all of them in the intended category for arbitrary source and
interpretation variable universes. No native arrow negation is added as a new
primitive: the existing source negation is interpreted by its proved raw macro.

For clarity, the full congruence argument uses a strengthened consequence of
already completed work. `fragment_maximality` instantiates the original isolation
and collapse argument with any uniformly substitution-closed bicartesian fragment
congruence. `fragment_dichotomy` proves that such a relation is equality or total.
`ProofCongruence.of_closed_fragment` then proves tensor and derived-negation
compatibility in those two cases. This is a proved closure theorem, independent
of model semantics, not a hypothesis that the desired universal agreement is a
full congruence. Its fragment substitution closure is proved by precomposing each
full interpretation with substitution. The construction never assumes that one
interpretation's kernel is substitution closed.

For an arbitrary target object Z, a constant valuation sends a chosen source
variable p to Z. Canonical evaluation sends the actual source projections at p
to the native target projections Z∧Z→Z. Total universal agreement equates these.
Composing the native pair of any a,b:Y→Z with the equal projections and applying
both product beta laws gives a=b. No target-arrow existence is introduced.
Nonempty P is used exactly to choose p. Empty target hom-sets remain valid.

Verification and provenance are retained in
`provenance/wsl-full-source-models/FINAL_VERIFICATION.json`, `COMMANDS.json`,
`CHECKED_SOURCES.sha256`, `CHECKED_SOURCES.tar.gz` and the control records.
Required checks comprise pinned strict build/full transitive axiom and source
closure, all public files, boundary controls and 66 expected rejections, including
five new model-specific controls. Development failures remain recorded separately;
they are not counted as successful negative controls. The source archive is read
back and compared with committed bytes before delivery. All nine manuscript
blobs and the existing stash remain preserved.

The [hostile review](reviews/FULL_SOURCE_MODELS_HOSTILE.md) and
[writing review](reviews/FULL_SOURCE_MODELS_WRITING.md) are local author-side
reviews of the actual argument. Independent replay, Comparator, official/service
verification and publication have not been performed. Delivery paths and hashes
are in `provenance/wsl-full-source-models/DELIVERY_REGISTER.json`.

Full-paper completion remains open: general arrow-substitution action transports,
Appendix A profiles/gamma/chi/ordinal/renaming/example constructions and the
recorded final manuscript scope refresh. Both maximality routes and every
completed reduction, coherence and correspondence result are retained.
