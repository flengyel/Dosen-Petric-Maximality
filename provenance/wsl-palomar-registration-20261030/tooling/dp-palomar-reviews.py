hostile=r'''# Palomar registration package: mathematical and correspondence audit

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
'''
writing=r'''# Palomar registration package: mathematical-writing review

The selected mathematics is explicit and the raw/quotient relation is explained
before the result table. The new account distinguishes the two collapse proofs
and the intended full congruence relation without changing manuscript v8. The
public description separates the selected family from the retained complete
formalization and local verification from later service stages.

This is a local AI-assisted author-side review under the Mathematical Writing
skill, not external human peer review or a Palomar editorial decision. Scope:
the complete new Challenge, three new production modules, the correspondence
account, root metadata, current README and registration reports. The unchanged
manuscript is preserved rather than claimed as a newly rewritten document.

The governing source consulted was Donald E. Knuth, Tracy Larrabee and Paul M.
Roberts, [Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
The complete cached PDF has SHA-256
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
Section 1, especially points 5 and 10–17, and the contextual discussions in
Sections 4–5 were consulted. Locations below refer to printed sections/pages,
not invented PDF line numbers. The report format and economy/process-separation
requirements are the skill's supplementary editorial method; they are not
attributed to the book.

## Current outline and functions

1. Challenge introduction: actual presentation and composition convention.
2. Formula and occurrence/substitution definitions: objects, tagged positions
   and the operation on formulas.
3. Op and Term: actual typed primitive grammar and derived term macros.
4. Constant, Equation and Derives: positive constant side condition, generating
   schemas and generated equality.
5. Whole-arrow substitution and PrimitiveCongruence/Closed/Total: the precise
   relations and endosubstitution action.
6. Five formal theorem statements: the two maximality routes, dichotomy,
   nonzero identity and empty hom-set.
7. `PALOMAR_STATEMENT_CORRESPONDENCE.md`: definitions, descent/restriction and
   pointwise inverses, then the five-result table and its scope.
8. `formalization.yaml`: mathematical description, source attribution,
   classification, scope, AI role disclosure, fidelity and declaration alignment.
9. Separate registration report/status/reviews: verification, provenance,
   diagnostics, release decision and delivery; these are outside the manuscript.

The central result identifies every closed primitive congruence with generated
equality or hom-wise totality on the actual arrow grammar. The two structural
witnesses explain the nonthin/empty-hom setting. Quotient descent, substitution
closure, source isolation and collapse are the relevant prerequisites. The
existing organization preserves this dependency order; no alternative outline
is warranted.

## Comparison and repairs

| Anchor | Actual issue or check | Verified principle or independent rationale | Action/result |
| --- | --- | --- | --- |
| Challenge's five theorem types | Every hypothesis must remain visible in the declaration's complete type. | KLR §1 point 5, printed p.2, recommends self-contained theorem statements. | Universe/type parameters, closedness, nonderivability and relation hypotheses are explicit; exact comparison passes. |
| Correspondence account, opening and descent section | Raw syntax, generated equality and quotient equality must remain distinct. | KLR §1 points 10–11, printed p.2: connected exposition and complementary descriptions. | Define the grammar/equality first, then state the quotient relation and its proof. Preserve the separate pointwise relation correspondences. |
| Whole-arrow substitution and `Closed` | A reader must know that term and endpoint formulas are substituted together. | KLR §1 points 14–15 and §5, printed p.12, on notation and nearby definitions. | `σ : P→Formula P` and the typed `Term.subst` action precede `Closed`; prose explains both endpoint formulas. |
| Composition in Challenge/statement account | Operational order differs from manuscript composition notation. | Independent typing/notation rationale, supported by KLR §1 notation guidance. | Retain “composition applies its first argument first” and the explicit `f:A→B`, `g:B→C` explanation. Constructor endpoints and source correspondence agree. |
| Metadata's nonempty-variable hypothesis | The public wrapper retains a hypothesis unused by the stronger production theorem. | Independent fidelity rationale; no general ban on unused hypotheses is attributed to KLR. | Explain intentional specialization to printed Theorem 2.1. The identity witness and empty-hom theorem state their distinct hypotheses. |
| `PalomarCorrespondence.full` docstring | An early draft narrated the checking sequence and a later proof. | Supplementary skill requirement: keep process commentary outside mathematical prose. | Replace with the mathematical statement that a closed primitive congruence extends to a full proof congruence while preserving its relation. Proof-route reporting stays in the separate report. |
| Challenge introduction | An early draft appended reassurance that all definitions were concrete. | Supplementary economy rule, independent of a quoted KLR rule. | Remove the redundant sentence; the actual definitions express the content directly. |
| Metadata classification | The proposal's MSC list differed from the manuscript. | Independent bibliographic consistency rationale. | Use the manuscript's `03G30`, `03F07`, `18A32`; official taxonomy validation passes. No manuscript change. |
| README/status versus retained historical reports | New local kernel results must not retroactively change old checkpoint claims. | Independent temporal/provenance consistency rationale. | Add a dated current registration section; retain historical reports and the preceding continuation unchanged in history. |
| Whole new account | Tables should serve genuinely parallel comparisons; prose should explain inferences. | KLR §1 points 10–13, printed pp.2–3. | Keep the five-result table; explain descent and inverse relation laws in connected paragraphs. No gratuitous diagram was added. |

## Definition order, notation and economy

`Formula P`, `Term P A B`, composition, `Equation`, and `Derives` precede the
primitive congruence. Substitution on formulas and whole arrows precedes
`Closed`. `Total` quantifies over existing parallel terms, so it cannot be read
as asserting existence of arrows in empty hom-sets. The quotient account states
the map `ofTerm` and both source/target types before using distinctness. The
relation-level inverse claims are distinguished from equality of structure data.

The meaning of `Constant` remains the inherited positive letterless grammar;
formula negation and derived arrow negation are introduced in their respective
roles. Tagged sums preserve repeated occurrences, and `Empty` is retained at
top/bottom. No labels, endpoint types, quantifiers or converse directions were
removed for brevity. The five complete formal types also remain the authoritative
unambiguous statement of each selected result.

Section 4 of KLR, printed p.9, explicitly allows context-sensitive placement of
some definitions; Section 5, printed p.12, advises defining symbols before or
near their use. These were applied with judgment, not as a demand for a separate
dictionary before every familiar categorical term. The account introduces the
paper-specific raw relation and closure precisely where needed.

A continuous prose pass of the new mathematical account and docstrings retained
paragraphs that define objects, explain descent, prove a correspondence or
state its scope. Redundant reassurance and checking-process narration were
removed as recorded above. Verification histories and delivery details remain
in process reports, not the manuscript or theorem prose. The excerpted source
anchors and the positive-constant distinction remain because they identify
which generating presentation is formalized.

## Priority and verification scope

The required local repairs above are applied. No further manuscript revision is
justified by an exhibited defect in this packaging work. No replacement theorem
wording or alternative outline is needed after the corrections. Preserve the
complete finite presentation even though the Challenge exceeds the 300-line
warning: compressing its equations into opaque interfaces would make the
mathematics harder to inspect.

The exact Challenge and production wrappers compile; public Comparator,
extended type/value audit, proof-route checks, Lean, NanoDa and authenticated
con-ron pass. These checks substantiate formal fidelity, not a claim of human
mathematical certification. No TeX rebuild or PDF visual reinspection is claimed
for this stage: all 11 manuscript files are byte-identical, and the new reviewed
material is Lean/Markdown/YAML. Prior full-paper cloud reviews remain separately
attributed. Official full preflight, service editorial outcome and exhaustive
novelty assessment remain unperformed.
'''
(rc/'docs/reviews/PALOMAR_REGISTRATION_REVIEW.md').write_text(hostile)
(rc/'docs/reviews/PALOMAR_REGISTRATION_WRITING.md').write_text(writing)
print('Mathematical/correspondence audit and source-grounded writing review finalized')
