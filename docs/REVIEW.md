# Review of the preliminary formalization

This is an author-side automated audit of the initial Lean modules and their
manuscript correspondence map. It is not independent peer review or a review
of a completed maximality formalization. The manuscript v4 is preserved.

## Mathematical-writing review

The manuscript's existing outline is: introduction (question and proof route);
Boolean proof category (structure, congruences, main theorem); occurrences and
substitution (coherence input and coordinates); isolating an occurrence
(selectors and transport); contextual collapse (fold, quotient argument, main
theorem and model corollary); Appendix A (profiles, ordinal coordinates, shared
variables). This order is retained.

The governing source consulted is Knuth–Larrabee–Roberts,
[*Mathematical Writing*, Stanford report CS-TR-88-1193](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1. Point 5 supports stating hypotheses with a theorem; points 10–11 support
connected explanation and defining variables; points 14–15 address consistent
notation and economical indices. These principles are applied to the map,
not presented as a proof of mathematical correctness.

| Anchor | Issue checked | Action |
| --- | --- | --- |
| `MANUSCRIPT_STATEMENTS.md`, target paragraph | Quantifier order and distinction between hom-set relations and substitution congruences | State the existential distinct pair and universal conclusion explicitly. |
| §2 zero law / `Category.lean` | Right-to-left manuscript composition versus operational Lean arguments | Record `comp f g` = g ∘ f; retain an existing-arrow witness. |
| §3 / `Formula.lean` | Repeated labels must not identify positions; empty constants remain empty | Use Sum tags and Empty; prove both inverse laws without a nonempty-variable assumption. |
| `lem:symmetric` / `Relations.lean` | Relation equality is not yet categorical equality | Label the formal results as relation calculations and retain the missing faithful-functor bridge. |
| `MANUSCRIPT_COVERAGE.md` | Avoid confusing preparatory lemmas with contextual collapse | Mark all three substantive milestones open. |

The actual formula constructors precede positions, labels, substitution, block
coordinates, and inverse-map theorems. Relation operations precede their
calculation lemmas. The category and zero-identity structures precede zero-arrow
definitions. No manuscript revision or new layout verification was performed.

## (A) Kill-shots / hard blockers

No confirmed blocker to the narrowly stated preliminary results was found.
There is a confirmed blocker to claiming a completed maximality formalization:
`MANUSCRIPT_COVERAGE.md` lists contextual collapse and the actual presentation
bridge as open. Failure mode: unproved. Evidence: absence in the source tree
of those constructions or theorems. Severity: fatal for a completion claim,
not for this preparatory checkpoint. Repair: prove the listed obligations.

## (B) Major weaknesses

Anchor: `Relations.projections_distinct` and the scope-map row for §3.
The result distinguishes two relations; it does not instantiate the complete
structural/faithful-interpretation interface in a nonthin category. Failure
mode if used for that stronger purpose: unsupported_generalization. Evidence:
structural argument—the current declaration only mentions relation functions.
Severity: major for milestone I. Repair: construct the complete interface and
its intended nonthin model or prove the presentation bridge. The current map
already states this limit.

Anchor: `LITERATURE_REVIEW.md`, unresolved coverage. The public search is not
exhaustive. Failure mode of an unqualified priority claim: unsupported_novelty.
Evidence: documented unchecked citation/index coverage. Severity: major for a
priority claim. Repair: finish the comparison or retain the bounded search claim.

## (C) Minor issues

The project uses a small explicit Category record rather than Mathlib's
category class. This is a defined interface choice, not an error. Before adding
Mathlib results, prove a typed bridge and preserve the composition convention.

## (D) Cross-section consistency failures

None confirmed within the preliminary map. `ZeroIdentity.law` has the
manuscript's endpoint types. Both conjunction and disjunction use disjoint
unions of positions. `hRel` is defined from the specified distributor relation,
not postulated to be the fold. Coherence is not applied to any quotient.

## (E) Acceptance conditions, non-negotiable

1. Preliminary checkpoint: strict Lean build and the axiom audit must pass for
   the recorded code. Failure prevents a checked-checkpoint claim.
2. Milestone I: contextual collapse and the complete nonthin-model/interface
   check must be supplied. Failure prevents claiming contextual collapse.
3. Milestone II: isolation and substitution must retain explicit normalization,
   coherence, and presentation inputs. Failure prevents relative maximality.
4. Milestone III: the actual presentation and all bridges must be proved.
   Failure prevents unconditional formalization of the manuscript's target.
5. Submission: implement the independent statement, dependency, source-closure,
   and kernel checks under the current Palomar contract. Failure prevents a
   Palomar-ready claim.

## (F) Not checked / uncertainty log

The entire Boolean Coherence proof, the full Došen–Petrić arrow presentation,
quotient construction, independent kernels, and a comprehensive novelty search
have not been formalized or verified in this checkpoint. The manuscript PDF
was not changed or re-rendered. There is no new whole-manuscript certification.

Strongest confirmed blocker: the substantive collapse and maximality
obligations remain unproved. Strongest suspected unconfirmed blocker: unknown;
no additional counterexample is asserted. Most important unchecked item: the
full presentation/faithful-interpretation bridge. The scope judgment does not
depend on unavailable material. Final recommendation for a claim of completed
maximality formalization: reject. The preliminary checkpoint is assessed only
within its stated scope and recorded compilation evidence.
