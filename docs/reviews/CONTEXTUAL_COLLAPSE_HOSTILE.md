# (A) Kill-shots / hard blockers

This is an author-side automated self-audit of manuscript v4 §§4–5, the new
Lean argument, and its correspondence map, not independent human peer review.
The genre is a conditional formalization checkpoint. Correctness, typing,
self-containedness, reproducibility, and scope were examined.

Anchor: manuscript §2, Theorem 2.1, printed p.2, claiming maximality of B(P);
`relative_maximality`; coverage milestones I–III. A completion claim for that
actual presentation is **unproved**. Evidence: **absence_in_text** and
**structural_argument**: the theorem quantifies over an arbitrary category on
formulas with supplied interface data; no actual B(P) arrow presentation or
instance of its published coherence theorem occurs in the source. The
`GeneratedModel.Term` constructors omit negation functor, De Morgan, eta, and
epsilon operations. This blocks actual-presentation completion, with fatal
severity for that claim. Repair requires the typed presentation and proved
bridges. The current checkpoint does not make the completion claim.

The earlier report's absent conditional collapse/isolation obligations are
resolved within the explicit interface: `ContextualCollapse.total`,
`Isolation.normalized_literal_context`, `ContextualCollapse.all_contexts`,
and `relative_maximality` now compile. This is evidence for the limited
conditional claims, not grounds for downgrading the remaining bridge blocker.

# (B) Major weaknesses

Anchor: coverage I, “intended nonthin model”; `GeneratedModel.interpretation`,
`nonthin`, `empty_hom`. The full §5 record is now instantiated with categorical
nonthinness and an empty hom-set. Claiming this as the actual intended model
would be **unsupported_generalization**. Evidence: **structural_argument**:
arrows are denotable relations of a smaller typed syntax; the full Boolean
operations and presentation identification are absent. Severity: major for
milestone I completion, repairable by the intended bridge. The old
relation-projections-only defect is repaired by the complete fragment instance;
the intended-model gate remains open.

Anchor: `relative_maximality` hypotheses `N`, `labels`, `U`, `D`, and `closed`;
manuscript §3 and Proposition 4.2, printed pp.3–5. These are explicit typed
inputs, not proved instances for B(P). Treating them as proved published
bridges would be **unproved**. Evidence: **absence_in_text**: no construction
of those instances for the actual presentation. Severity: major for milestone
II intended correspondence; repairable by the listed constructions. No
substitution stability is inferred from one valuation kernel. The entire
relative-maximality interface has not been jointly instantiated in a nonthin
model; the generated §5 fragment instance alone does not settle that question.

Anchor: historical literature comparison, unresolved index coverage. An
unqualified priority claim would remain **unsupported_novelty**. Evidence:
**absence_in_text** of a comprehensive current comparison. This review makes
no novelty finding and does not downgrade that earlier limitation.

# (C) Minor issues

Anchor: `Structure`, `Substitution`, and `DoubleNegation`. Some specified laws
are stronger than those actually used in the final proof: initial uniqueness,
several substitution preservation fields, and the second double-negation
inverse are not needed by every step. Failure mode: **unused_hypothesis** at
individual lemma level, evidence **derivation** by inspecting proof bodies.
Severity: minor; these remain appropriate typed structural inputs rather than
assumptions of the desired conclusion. No repair is required to the statements.

Anchor: `GeneratedModel.Term.Truth`. Negation is treated atomically in this
fragment-only invariant. Confusing it with Boolean semantics would be
**ambiguous**. Evidence: **derivation**, `Truth (.neg A) = True`. Severity:
minor for naming/explanation; the coverage map now states its limited purpose.

# (D) Cross-section consistency failures

No confirmed mismatch within the newly stated conditional scope was found.
The checked correspondence is:

| Claim | Typed data / derivation | Test or boundary |
| --- | --- | --- |
| §5 fold, first injection, second block | Arrows have the manuscript endpoints; their original-category relation images are calculated, then faithfulness is applied. | All occurrence types, including Empty, are quantified. |
| §5 quotient argument | Equivalence on each Hom; composition, pairing, and copairing compatibility. Terminal retraction is checked at both injections; coproduct eta yields equality modulo Q. | No quotient faithfulness or cancellation of j_A. Explicit quotient objects are unnecessary for the congruence proof. |
| Equal projections imply totality | Precompose with `pair f g : Hom X (A ∧ A)` and use both projection equations. | Quantifies only over existing parallel f,g; no Hom inhabitation is invented. |
| §4 isolation | `selector : Hom (l ∧ bot) A`, `coselector : Hom B (l ∨ top)` with exact edge formulas. Signed-label preservation types the shared literal. | Sum tags preserve repeated positions; constants have no selectable positions; both Literal constructors are included. |
| Normalization | Original-category arrows A → normal(A) and back with inverse equations; `recover` proves injective transport. | No relation faithfulness on the quotient. |
| Uniform substitution | `map σ f : Hom (A.subst σ) (B.subst σ)`, with per-substitution identity/composition and operation laws; Q closure is separate. | Schema composition laws and actual syntax correspondence are still open. |
| Negative literal | p ↦ neg A, then product/coproduct transport using into/out and into_out. | `context_retract` proves the square and transports zeros by absorption. |
| Nonthin §5 model | Typed generated syntax; denotable relations; category and all structural laws. | Distinct projections for any p; `Hom(top,bot)` empty. |

The generic one-way two-object category cannot itself instantiate a formula
bicartesian interface with all these operations. It is not a counterexample.
The relevant partiality check is the proved empty Hom in the complete fragment
model. Composition remains operational: comp f g means first f, then g.

# (E) Acceptance conditions, non-negotiable

1. Conditional checkpoint: strict build and transitive axiom audit must pass
   for the recorded source. Failure rejects a checked-checkpoint claim.
2. Audit coverage: public/private axioms and hidden dependencies must fail the
   focused controls. Failure rejects the audit-evidence claim.
3. Milestone I completion: instantiate the whole interface in the intended
   category or prove its bridge. The fragment instance alone is insufficient;
   failure rejects milestone I completion.
4. Intended relative-maximality correspondence: construct normalization,
   signed-label, double-negation, arrow-substitution, and congruence restriction
   instances. Failure rejects a claim about the actual presentation.
5. Actual maximality: formalize the presentation and coherence with exact
   source correspondence. Failure rejects milestone III completion.
6. Submission: independent statement/shared-definition, dependency/source
   closure, immutable-source, and kernel checks must run under current policy.
   Failure rejects Palomar-readiness or acceptance claims.

# (F) Not checked / uncertainty log

The full book presentation and coherence proof, normalization correspondence,
full arrow-substitution action, model corollary, Appendix A's remaining bridges,
independent kernels, and comprehensive literature/novelty were not verified.
No new manuscript render or graphical layout audit was performed. The v4
source and PDF checksums match. The existing review has been retained.

A negative control exposed a private-name gap in the old namespace audit. The
filter was corrected using Lean's own `privateToUserName`. All three final
controls reject; strict verification checks 645 declarations. This remains a
compiler-environment audit, not independent replay.

Strongest confirmed blocker: missing actual-presentation and intended-model
bridge. Strongest suspected unconfirmed blocker: unknown; no new mathematical
counterexample is asserted. Most important unchecked item: the complete
presentation/coherence correspondence. The scope judgment does not depend on
unavailable material, but theorem III cannot be certified without that
material being formalized. Final recommendation for a completed
actual-presentation formalization claim: **reject**. No confirmed counterexample
to the narrower compiled conditional theorems was found.
