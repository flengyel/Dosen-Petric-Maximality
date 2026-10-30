# Palomar registration package: mathematical and correspondence audit

Local AI-assisted author-side audit, 30 October 2026. Genre: an independent
formal statement/proof package, its raw/quotient correspondence, and release
metadata. Axes: correctness, statement fidelity, self-containedness and local
reproducibility. This is a HostileRefereeGPT audit of authorized author material,
not external human peer review or a Palomar service verdict.

## (A) Kill-shots / hard blockers

No confirmed mathematical hard blocker remains in the selected five-statement
package. The unmodified public Comparator matches the selected types and their
required definition closure; Lean, NanoDa and authenticated con-ron accept the
complete selected proof export. The separate expanded audit covers 360 concrete
presentation declarations, including their relevant values and constructors.

The concrete release/license decision and official full preflight are pending.
Those prevent service intake; they are administrative stage boundaries, not a
counterexample to the mathematics. No registration or service acceptance is
asserted by this package.

## (B) Major weaknesses

**Resolved correspondence risk — primitive versus full congruence.** Anchor:
`PalomarDefinitions.lean`, `PrimitiveCongruence`, and
`PalomarCorrespondence.lean`, `fragment`, `full`, `negate_admissible`,
`ofFull_full_rel`, `full_ofFull_rel`. Claim: the compact primitive interface
represents the intended closed proof-congruence relations on the actual
quotient. Failure mode tested: `unsupported_generalization` / `unproved`.
Evidence: `derivation`. `of_derives` makes the raw relation well defined on
quotient representatives; the tensor/diagonal and codiagonal constructions give
pairing/copairing closure. Uniform substitution descends. Restriction and extension
are pointwise inverse; totality and distinctness correspond. Derived negation
is admissible for closed primitive congruences by the proved fragment dichotomy.
Downstream impact: the compact selected theorem implies the intended full
quotient formulation. Severity before these proofs would have been major;
current status resolved, with compiled proofs. No equality of chosen structure
records is claimed.

**Resolved proof-route risk — a second collapse proof.** Anchor:
`PalomarMaximality.lean`, `short_maximality`, especially
`ShortProof.total R.fragment allK`; `DEFINITION_AUDIT_RESULT.json`, short-proof
closure. Failure mode tested: `inconsistent_use` / `unproved`. Evidence:
`derivation` plus `structural_argument`. The proof obtains the actual normalized
literal context, propagates its contextual equation by uniform substitution and
double negation, and calls `Presentation.ShortProof.total`. The closure contains
the particular q/e arrows and their identities. It excludes the selected fold
maximality, `relative_maximality`, fragment maximality/dichotomy and the full
closed-fragment extension. A separate check also excludes
`ContextualCollapse.total`. Downstream impact: the two selected statements have
the same type with the required distinct collapse arguments. Potential severity
major; current status resolved. Shared normalization/isolation inputs are
explicit and fully instantiated.

**Resolved independent-statement risk — concrete closure.** Anchor:
`Challenge.lean`, `Formula.subst`, `Constant`, `Equation.constant_swap`,
`Term.subst`, and `CANONICAL_CHALLENGE.json`. Failure mode tested:
`missing_definition` / `irreproducible`. Evidence: `structural_argument` and
verified comparison. The Challenge imports core only, has concrete syntax,
equations, derivability and substitution, and has holes only at the five theorem
proofs. `Constant` has top/bottom/conjunction/disjunction constructors and no
negation constructor. All 31 raw term constructor families and both tensor
choices remain present. Including original `Formula.Occ` preserves the actual
compiler-generated substitution closure. No relative coherence/normalization
field or supplied maximality property replaces an input. Potential severity
major; current status resolved.

## (C) Minor issues

**Intentional printed-theorem specialization.** Anchor:
`PalomarMaximality.lean`, the three `[Nonempty P]` binders;
`formalization.yaml`, `fidelity.divergences`. Failure mode: `unused_hypothesis`.
Evidence: `derivation`. These public hypotheses are retained to match manuscript
Theorem 2.1, although the instantiated production maximality result is stronger.
They do not weaken the printed theorem. Downstream impact: readers must not
interpret the retained hypothesis as a new necessity result. Severity minor;
resolved by the explicit metadata and correspondence account. The identity
witness takes `p` explicitly; the empty-hom theorem has no such hypothesis.

**Finite presentation length.** Anchor: all 562 lines/23,920 bytes of
`Challenge.lean`. Failure mode tested: `ambiguous` / `irreproducible`. Evidence:
`structural_argument`. The file exceeds the 300-line auditability warning but
remains below 1,000 lines/100 KiB. The length comes from the actual finite
presentation, not hidden parameter interfaces. The grammar and equation schemas
remain readable, with definition order and source anchors. Severity minor;
no reduction in mathematical content is warranted merely to avoid the warning.

## (D) Cross-section consistency failures

No unresolved inconsistency was found in the checked scope. The following
claim/type/law/test correspondences were checked:

| Claim | Typed data and law | Evidence/status |
| --- | --- | --- |
| Actual source arrows | `Term P A B`; `comp f g` first applies `f : A→B`, then `g : B→C`. | Constructor endpoints, source excerpts and complete definition comparison pass. |
| Generated equality | `Derives f g` corresponds to `ofTerm f = ofTerm g`. | `raw_distinct_iff`, quotient soundness and exactness compile. |
| Raw relation descent | For each `A,B`, `R.Rel` factors through the quotient map on both arguments. | `quotientRel_ofTerm`, symmetry/transitivity and `of_derives` compile. |
| Closed congruence correspondence | Raw restriction and full quotient extension preserve relations, substitution closure and totality. | Pointwise inverse lemmas and `negate_admissible` compile; no unproved operation-compatibility field remains. |
| Negation versus constants | Formulas and raw arrows include negation operations; positive `Constant` does not include negation. | Concrete grammar/side conditions preserved and altered-generator control rejected. |
| Existing arrows versus totality | `Total` relates every existing parallel pair; it does not provide an inhabitant of an empty hom-set. | The two-object one-way-arrow test leaves the reverse hom-set empty. The actual `no_top_to_bot` theorem compiles and is independently replayed. |
| Nonthinness | At a supplied `p`, identity is not derivably equal to primitive zero. | Actual `identity_ne_primitive_zero` and quotient soundness; no global zero-morphism structure. |
| Repeated/empty positions | `Formula.Occ` uses tagged sums and `Empty`; formula negation preserves positions. | Original definition included verbatim; no injective-label or nonempty-occurrence assumption introduced. |
| Metadata scope | Five selected declarations versus the complete-paper development. | Alignment table and preserved complete claim map agree; source-based provenance and AI roles are explicit. |
| Verification scope | Local package/comparison/kernels versus official preflight/service/registration. | Separate machine/human stage records; no local acceptance is reported as a service result. |

The new package has no new model, functor, adjunction or naturality claim beyond
the actual raw/quotient operations described above. Existing categorical
constructions remain in the preserved full-paper source.

## (E) Acceptance conditions, non-negotiable

1. Preserve the actual Formula/Op/Term/Constant/Equation/Derives/substitution
   closure and all side conditions. Endpoint: exact public Comparator and
   expanded definition audit pass. Satisfied. Failure rejects the selected-source
   fidelity claim.
2. Prove raw/full quotient relation correspondence, derived negation for closed
   relations, distinctness and totality. Endpoint: production correspondence
   lemmas and strict axiom audit pass. Satisfied. Failure rejects translation to
   the intended congruence theorem.
3. Preserve the actual q/e proof as a separate collapse route. Endpoint: the
   actual proof source and complete dependency audit pass. Satisfied. Failure
   requires dropping the claimed second proof.
4. Compile the statement independently and prove Solution without Challenge-hole
   dependency. Endpoint: core-only canonical compilation, source closure audit,
   permitted-axiom audit, Lean and NanoDa acceptance. Satisfied; con-ron also
   accepts. Failure rejects the verified local candidate claim.
5. Reject all focused malformed packages for their intended cause. Endpoint:
   six actual rejections, with successful fixture compilation/export where
   applicable and official import-policy results. Satisfied. Unrelated parser or
   missing-module errors are insufficient.
6. Preserve source and manuscript evidence while satisfying whole-tree policy
   and truthful metadata. Endpoint: 1,870 compiler-parsed headers, no forbidden
   artifacts/dependencies, 11 unchanged manuscript files, official metadata
   loader/schema/taxonomy pass. Satisfied. Failure blocks release readiness.
7. Keep publication and registry assertions conditional on their actual stages.
   Endpoint: explicit private status and proposed license; official full
   preflight and service/editorial/registration marked pending. Satisfied for
   this local candidate. A service-success claim must be dropped until those
   separate results exist.

## (F) Not checked / uncertainty log

The complete new Challenge, three wrapper/correspondence modules, mathematical
account, metadata, selected proof dependencies and reported local evidence were
reviewed. This audit does not claim to have reread every retained historical
fixture or every existing production proof by hand. The complete-paper endpoint
and prior cloud reviews are preserved; the independent replay claim applies to
the selected closure, not every unselected appendix/model theorem separately.

The extended all-declaration comparison alpha-renames bound universe parameter
names in two generated declarations; all arities, orders and expression uses
remain compared. The public Comparator uses unmodified exports. Compiler-generated
partial evaluation helpers are included in that additional audit but are absent
from the exact public-configuration kernel export. This is the official selected
export closure, not a pruned proof dependency graph.

No new exhaustive novelty search, human peer review, official reusable full
preflight, service verification, editorial decision or registry entry was
performed. Publication/license approval, final immutable commit evidence and
committed-byte delivery are separately recorded workflow matters; this audit
does not invent them from a build log.

Strongest confirmed blocker to registration: the concrete public release/license
decision and official full preflight are pending. Strongest suspected unconfirmed
mathematical blocker: none identified in the checked package. Most important
unperformed check: the official full workflow and eventual service review of the
immutable public source. A registration recommendation depends on that unavailable
material. Final recommendation: **unknown for registration**; the seven local
mathematical/correspondence acceptance conditions above are satisfied.
