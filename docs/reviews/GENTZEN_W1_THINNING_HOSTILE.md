# Author-side hostile review: opposite-side W1 thinning

## (A) Kill-shots / hard blockers

Scope: the four new Lean modules, exact theorem statements, complete W1
thinning report and new correspondence/current status records. This is an
AI-assisted author-side audit, not independent peer review or certification.
No fatal blocker was confirmed for these two concrete commutations.

| Anchor / actual claim | Failure mode tested; evidence | Finding and downstream scope |
| --- | --- | --- |
| GentzenThinningCommutation, denoteL/R | ill_typed, unproved; derivation | Expand actual G.denote, use ofTerm_comp and existing Laws.assoc (opposite orientations). Both three-arrow paths have the displayed four endpoints. No coherence or interpretation premise. |
| GentzenOppositeThinningRank, predecessors_thinR_left/thinL_right and rho_* | false, inconsistent_use; derivation | The parent map on the opposite side is identity on the exact At. fiber_identity gives exactly one predecessor, then rho_eq adds one node. No label matching or denotation invariance. |
| GentzenThinningCommutationRank, contraction_lossL/R | false, unproved; derivation | Existing contraction sums enumerate selectedCopies, map each summand to 1+rho, use the proved sum lemma and exact length gs.length. No contraction copy is discarded or gap formula included by matching its value. |
| Same module, endpoint_rank/loss/decreasesL/R | ambiguous, unsupported_generalization; structural_argument | Inner contraction loses n; outer selected endpoint retains a thinning root and loses n−1. Addition equations and hn ≥ 2 prove strictness. No quotient rank or all-site replacement theorem is asserted. |
| Commutation, atomizedL/R and newL/R_atomized | unused_hypothesis, unproved; exact definitions | Equivalence is unconditional for arbitrary D: both predicates are AtomicFormula D ∧ f.Atomized. The forward constructors from f.Atomized explicitly require AtomicFormula D. Equality/rank statements do not. |
| Commutation, relationL/R | misuse_of_prior_work; derivation | congrArg occurrenceMap applies to a previously proved Reduced equality. It does not reflect relation/inclusion equality and cannot supply coherence. |

No counterexample is asserted. The source W1 appeal to Semilattice Coherence
is not imported as an assumption; only these associativity instances are proved.

## (B) Major weaknesses

No unresolved major defect was found in the scoped claim. Two potential
scope errors were specifically tested and excluded:

1. Anchor: report “Exact rank equations” and endpoint_lossL/R. Failure mode
   ambiguous; evidence derivation. Calling both decreases n would be false:
   new whole proof has its own thinning node. The report uses the explicit
   equation `rho old + 1 = rho new + n`, distinguishing contraction rank
   from selected endpoint rank. Applied clarification; no theorem weakened.
2. Anchor: report “Proof predicates” and with_cutL/R. Failure mode
   unused_hypothesis / unsupported_generalization; evidence structural_argument.
   Equality and rank proofs accept any f, including cuts. Exact cutCount
   preservation follows from these two unary constructors and is local to
   these commutations. Atomic-k duplication supplies no analogous global
   inequality. The actual examples have cutCount 1. No remaining hidden premise.

A future all-site reducibility theorem requires a typed replacement operation
and control of every tied contraction affected by replacement. This is an
explicit open obligation, not a defect of the narrower local endpoint.

## (C) Minor issues

Anchor: first verification attempt / pre-module-renaming logs. Failure mode
irreproducible; evidence exact exit/diagnostic. The existing closure parser
accepts letters-only module components and ignored W1 filenames. Applied
repair: rename only the new modules; preserve the failed check and rerun all
required checks. No audit rule was relaxed and no Lean theorem changed.

Anchor: three_copy_endpoint_lossL/R. Failure mode ambiguous; evidence checked
At.index_injective argument. The displayed selected position is the second
copy after the fixed C gap, not the first equal formula. The explicit
position equality is proved before arithmetic. Formula equality is not used
as a selection procedure.

## (D) Cross-section consistency failures

Current correspondence, statement, coverage, validation and continuation now
mark exactly the two opposite-side thinning W1 instances complete. They keep
other W1 cases, W2–W6, Reducibility, Blocked-w, arbitrary proof-context
replacement, cut elimination and coherence open. The next task is a typed
opposite-side exchange instance. Historical reports/access records remain
unchanged, including their then-current continuation targets.

All older DosenPetric modules and frozen interfaces are byte-identical. The
manuscript is unchanged. There is no new generating equation, raw/Gentzen
constructor, arbitrary zero, typeclass coherence premise, relation-kernel
quotient, equality reflection after inclusion, or arrow-negation operation.
The Empty-P constants, both signs, repeated labels and cut premise have
checked instantiations. No blocked-pattern definitions were added.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding scoped completion claim:

1. Both precisely typed old/inner/new pairs and unconditional Reduced
   denotation equalities compile: **met**.
2. Opposite-side predecessor singleton and rank equations retain exact At
   positions for arbitrary formulas: **met**.
3. Complete selected-copy sums prove loss n at the contraction and n−1 at
   the whole endpoint, with both strict inequalities: **met**.
4. CutFree/Atomized equivalences, exact cutCount equality and complete
   relation equality follow in the correct direction: **met**.
5. Three selected copies plus a fixed equal gap, empty contexts, constants
   at Empty P, C=D and cut-containing premises are checked: **met**.
6. Syntax/equations/predicates/ranks/manuscript/toolchain are preserved,
   without unproved coherence or all-W1 promotion: **met**.
7. Final strict build/audit, five negative rejections, import closure,
   manuscript checksums and whitespace pass with retained evidence: **met**,
   109 sources / 4,794 audited declarations.
8. Three finalized reports and exact source/evidence inventories are retained:
   **met**. Commit/ref and Downloads receipts are subsequent operational checks.

## (F) Not checked / uncertainty log

Baseline and all final required commands have complete logs, exits, elapsed
times and hashes in provenance/wsl-gentzen-w1-thinning/. The first closure
failure is retained. Earlier direct exploratory target builds have recorded
tool outcomes but no separate full timing/transcript; later example attempts
have both. All builds/audits were sequential. Only propext, Quot.sound and
Classical.choice occur among permitted dependencies; 34 selected prints
are retained. No choice-free claim is made.

The pinned source was read directly, including rendered p.251. The writing
review consults the available verified cache. No independent kernel replay,
exhaustive independent source audit, Challenge/Solution or Comparator,
official preflight/service acceptance, fresh manuscript compilation/layout
review, independent certification or novelty assessment ran.

Strongest confirmed blocker: none for these two W1 instances; the full
Reducibility endpoint still lacks other rewrites and all-site replacement
control. Strongest suspected unconfirmed blocker: none established within
scope. Most important unchecked item: independent full source/kernel
validation. Dependence on unavailable material: none for this author-side
conclusion. Final recommendation: **unknown** for independent certification;
the scoped author-side acceptance conditions above are met.
