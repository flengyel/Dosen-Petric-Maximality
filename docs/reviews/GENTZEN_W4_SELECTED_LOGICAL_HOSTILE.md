# Author-side hostile review: W4 terminal selected logical introduction

## (A) Kill-shots / hard blockers

This AI-assisted author-side audit covers all seven new modules, exact public
types, proofs and examples, source W4 correspondence, report and current maps.
It is not independent peer review or certification. No fatal blocker is
confirmed for the two stated terminal W4 instances.

| Anchor / claim tested | Failure mode tested / evidence | Result |
| --- | --- | --- |
| Data and terminal_left/right | ill_typed, unproved / derivation | Data stores only original A,B,gs,Θ with operation parameter. Contexts, arities and actual blocks are derived. Public inputs require n≥2 and an existing proof at the exact F, with no desired square/rank equality as hypothesis. |
| extend, lastSource/Target, old/newL/R | ill_typed, misuse_of_prior_work / derivation | The new inner contraction extends its fixed tail through [A,B]. Actual logical nodes use exact terminal contexts. The last block is genuinely two-copy, with gaps [gaps gs,Θ]. W2 reuse is positional, not substitution of a thinning constructor for introduction. |
| partial_square, consumed_a/b, principal fibers | false, unsupported_generalization / derivation | Both whole-formula component slots are consumed. Both principal ancestry fibers are empty. The partial map retains surviving tags and never supplies total A/B→C ancestry. |
| categorical_square, product/coproduct_square, denoteL/R | misuse_of_prior_work, ill_typed / derivation | Surviving components and both consumed fst/snd components are proved separately. Product paths are ante K→ante F, coproduct paths succ F→succ K. Actual Reduced component laws give equality; no Semilattice Coherence, inclusion/occurrence reflection or arrow negation. |
| selected_transport/survives, retained/fixed fibers | false, ambiguous / derivation | Ordered inner n-member image plus logical principal equals old n+1 selection. Last selection is exactly [k,q]. Original partial retained fibers contain n members; actual full contraction fibers contain n+1 and two. Every other final position has complete singleton fibers and a computed common original. |
| contraction_loss, old/new_endpoint, endpoint_balance/tie, fixed_increases | false, inconsistent_use / derivation and toy_test | Old outer rank LC+n+1 compares to new inner LC. Final new rank is LC+3: n=2 ties and n≥3 decreases. Other fixed same-side ranks increase from 2+rho to 3+rho. The source comparison is not silently replaced by universal endpoint strictness. |

No counterexample to the scoped result was established. Actual ties and fixed
increases refute stronger decreasing-measure claims which the report excludes.

## (B) Major weaknesses

No unresolved major defect is confirmed within scope.

1. Anchor: report “Exact proved endpoint and hypotheses” and terminal_left/right.
   Failure modes unused_hypothesis and unproved; evidence exact public types,
   constructor definitions and derivation. Arbitrary P,A,B, lists and existing
   cut-containing f are permitted. No atomicity, freshness, equal-label
   exclusion, nonempty P, DecidableEq or coherence hypothesis is hidden.
   Both endpoint types are actual G P K Δ / G P Γ K. Derived reassociations
   describe inputs, rather than assume the desired Reduced equality.
2. Anchor: examples selections, outer/last_map, old/new_partial_map and
   both_consumed. Failure modes false and inconsistent_use; evidence toy_test
   and structural_argument. Inner [1,3], outer [1,3,6], last [2,5] have
   different domains. Both original partial maps on six equal C labels are
   [some 0,some 4,some 1,some 4,some 2,some 3]. A=B positions 6 and 7
   are still distinct and both consumed. Final fixed 0 has original 0.
   Repeated labels do not erase tags or make a consumed component a C parent.
3. Anchor: source p.250 blocked pattern and report rank table.
   Failure mode unsupported_generalization; evidence actual last constructors
   and complete rank sums. The final binary contraction has the displayed
   local (w ∧ 1) shape, or its right dual. No general Blocked-w predicate,
   cut-tied all-site replacement, global termination, Reducibility, cut
   elimination or quotient-rank invariance is supplied. Those remain proofs
   to construct, not consequences of recognizing a local shape.

No novelty or whole-manuscript correctness judgment is made.

## (C) Minor issues

Anchor: retained failed elaborations. Failure modes ill_typed and unproved;
evidence diagnostics and final successful builds. Semireducible field aliases,
function-composition unfolding, arithmetic association, Option-map reductions
and scalar sum exposure needed explicit typed comparisons. Dependent elimination
at a compound principal label failed; a generic formula-typed parent lemma
resolves it before specializing to that label. This does not add a disequality
or weaken the target. No heartbeat limit or source equation was changed.
Final example build passes in 14.161s. Severity: repaired implementation
details, with no remaining mathematical impact established.

Anchor: report “Exact ranks and preservation”. Failure mode ambiguous;
evidence structural_argument. Contraction and endpoint comparisons appear as
separate table rows. Both Atomized predicates equal f.Atomized, with actual
compound examples. W2's asymmetric atomicity restriction is not imported.
No further mathematical repair is needed for these distinctions.

## (D) Cross-section consistency failures

The report, current maps, correspondence, validation, README and continuation
identify W4 terminal introduction and its right dual separately from W1/W2/W3.
The next W5 single-premise mix task explicitly uses G.mix f g with g's contexts
first and leaves both-premise and other-placement cases open.

Every older module/interface is byte-preserved. Empty P constants provide
actual premises with empty literal-occurrence sets. Signed examples contain
actual cuts and keep cutCount=1. Existing-arrow premises prevent invented
empty-hom-set arrows or zeros. The two-object one-arrow test requires no
reverse arrow or inverse for f: only actual structural isomorphisms and
derived component laws are used. No new model/equivalence is asserted.

Composition is left-first. The disjunction proof uses the opposite product
category for existing structural coproduct maps, not contravariant negation.
Relation equality is derived after Reduced equality. Manuscript v5, preserved
v4, diagrams, references and historical reviews remain unchanged. Three
milestones and conditional maximality transfers remain distinct. Unfinished
published-coherence reconstruction is not reported as a manuscript defect.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding scoped completion claim:

1. Original inputs, exact actual-constructor outputs and derived endpoint/
   arity laws, on both sides: met.
2. Partial ancestry consuming both slots, complete ordered selected survival/
   transport and distinct principal/retained tags: met.
3. Full principal, retained and fixed fibers, with common original positions:
   met, with original and intermediate domains kept separate.
4. Both consumed component equations and surviving square before correctly
   variant Reduced equalities, without coherence/reflection: met.
5. Full selected sums, n+1 contraction loss, endpoint balance/tie/strictness
   and other fixed increases: met.
6. Counts, CutFree/Atomized equivalences, full relations and inhabited
   Empty/compound/equal-label/two-three-copy/signed-cut examples: met.
7. Pinned Init-only closure, no older-interface changes, 192 source files /
   7,543 audited declarations and five expected rejections: met.
8. Retained reports/evidence and separate committed-source/ref/Downloads
   comparisons: reports prepared; final receipts record procedural completion.

## (F) Not checked / uncertainty log

Pinned source §11.2 printed pp.248–253, rendered p.251 W4 and p.252's
right analogue were directly consulted. Exact public types, 134 selected
axiom prints, complete local import/transitive audit, baseline/final checks
and failed attempts are retained under
provenance/wsl-gentzen-w4-selected-logical/. Only propext, Quot.sound and
Classical.choice are permitted; no choice-free result is claimed.

Independent source transcription/kernel replay, Challenge/Solution/Comparator,
official preflight/service, fresh manuscript layout/compilation, independent
peer review and novelty assessment did not run. General elimination, coherence
and unconditional maximality remain open. No unavailable review is reported done.

Strongest confirmed blocker: none for the scoped W4 instances.
Strongest suspected unconfirmed blocker: none established within scope.
Most important unchecked item: independent full source/kernel validation.
Dependence on unavailable material: none for this author-side audit.
Final recommendation: unknown for independent certification; scoped construction
and local verification conditions above are met.
