# Author-side hostile review: W2 terminal selected thinning

## (A) Kill-shots / hard blockers

This AI-assisted author-side audit covers all six new modules, their actual
public types, proofs and examples, the W2 source correspondence, report and
current maps. It is not independent peer review or certification. No fatal
blocker is confirmed for the two stated terminal W2 instances.

| Anchor / claim tested | Failure mode tested / evidence | Result |
| --- | --- | --- |
| SelectedThinning.Data and terminal_left/right | unproved, ill_typed / derivation | Data stores only C,gs,Θ. All contexts, bounds, casts, routes, positions and desired laws are constructed. Public endpoints quantify over original inputs and an existing proof, with n≥2. |
| copyIndex_old/last and Data.square | false, unsupported_generalization / derivation | The old-position identity has the actual source-length bound. The inserted last position has a separate calculation; it is not passed to the bounded old lemma. Every typed original position satisfies the square. |
| selected_transport, outer_retained_fiber and composite retained fibers | false, ambiguous / derivation | The complete ordered outer selection is the embedded n originals followed by the new leaf. The full outer fiber has n+1 members; either composite from original F has only n. The thinning leaf has no original predecessor. |
| original, outer_fixed_fiber/other_fibers, product_square/coproduct_square | misuse_of_prior_work, ill_typed / derivation | Every other final position has a computed unique common original and complete singleton fibers. Product equality is ante K→ante F; coproduct equality is succ F→succ K. Universal component laws precede Reduced equality; no coherence or occurrence reflection is used. |
| selected_sumL/R, contraction_lossL/R, endpoint_lossL/R | inconsistent_use, unproved / derivation | Count n embedded thinning nodes plus the rank-one new leaf. Old outer rank is LC+n+1, new retained rank LC+1. Thus contraction loss n+1 and endpoint loss n are distinct. An empty-block exchange still contributes a node. |
| old/new_atomizedL/R and compound examples | false, unsupported_generalization / derivation and counterexample | Old Atomized iff AtomicFormula C and f.Atomized; new iff f.Atomized. Concrete atomized compound premises give new Atomized and not old. Only the forward implication is unconditional. No atomicity hypothesis is smuggled into equality/rank. |

No counterexample to the scoped claim was established. The compound examples
refute a stronger predicate equivalence which the result explicitly does not
claim; they do not refute W2 denotation equality.

## (B) Major weaknesses

No unresolved major defect is confirmed within scope. The following potential
scope changes were tested and excluded:

1. Anchor: report “Exact proved endpoint and hypotheses” and concrete
   terminal_left/right. Failure modes unused_hypothesis and unproved;
   evidence exact type queries and actual constructor definitions. Arbitrary
   P,C, gaps/tail and existing cut-containing premises are allowed. Only n≥2
   is imposed. No freshness, DecidableEq, nonempty P, CutFree, Atomized,
   faithful interpretation or selected-square hypothesis is hidden. Endpoint
   reassociations are derived, not supplied as desired denotation equalities.
2. Anchor: tagged examples and complete fibers. Failure modes false and
   inconsistent_use; evidence toy_test and derivation. With six original
   formulas all labelled C, old selection [1,3,6] includes the new seventh
   position, while original selection [1,3] does not. Both composite maps
   are [0,4,1,4,2,3]. Fixed final positions 0 and 2 have originals 0 and 4.
   Labels never replace tags, and the old/new source domains are not conflated.
3. Anchor: fixed_old/newL/R and report rank table. Failure mode
   unsupported_generalization; evidence structural_argument. Every other
   final same-side position has rank 2+rho(f,a) on both proofs, at its proved
   common original. These are actual local syntax ranks. No arbitrary-address
   replacement, cut-tied all-site theorem, quotient rank, global termination,
   Reducibility or Blocked-w follows merely from this table.

No novelty or whole-manuscript correctness claim is reviewed. The strongest
established conclusion is exactly these two local terminal selected-thinning
transformations and their positional, rank and preservation laws.

## (C) Minor issues

Anchor: retained exploratory logs. Failure modes ill_typed and unproved;
evidence diagnostics and successful final compilation. Endpoint aliases,
opaque scalar sums and numerical normalization required explicit typed
equalities and intermediate lemmas. The first literal example used an existing
five-copy premise at a required four-copy endpoint; it was repaired by using
the existing four-copy cut premise, preserving both the required type and
the actual cut. No target or heartbeat limit was weakened. Final examples
compile in 14.533s; final required checks followed the last proof edit.
Severity: repaired implementation details, with no remaining mathematical
impact established.

Anchor: report “Complete positional calculation”. Failure mode ambiguous;
evidence structural_argument. The report gives full outer and original
composite fibers separately, with their different lengths. No additional
mathematical repair is needed for this distinction.

## (D) Cross-section consistency failures

The report, statement/coverage maps, correspondence, validation, README and
continuation identify terminal W2 separately from fixed-parametric W1 and
shared-selected W3. W4 terminal selected logical introduction is the next
concrete task. Its proposed n=2 final-endpoint tie is explicitly separated
from the strict W2 endpoint decrease; it is not described as proved now.

Every older DosenPetric module and frozen syntax/equation/denotation/predicate/
predecessor/rank interface is byte-preserved. No empty hom-set is filled,
arbitrary-endpoint zero supplied or variable inhabitant chosen. Empty P
constants give actual left/right premises, including whole-formula positions
with empty literal-occurrence sets. Signed examples include actual cuts.
Existing-arrow premises are retained, so the two-object one-arrow test
requires no reverse arrow or inverse; no new model equivalence is claimed.

Composition is left-first. The original Reduced category supplies the
component equations, and tagged relation equality is derived afterward.
Manuscript v5, preserved v4, diagrams, references and historical reviews are
unchanged. The three milestone boundaries and conditional maximality transfers
remain distinct. An unfinished published-coherence reconstruction is not
reported as a manuscript defect.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding scoped completion claim:

1. Original-data inputs and actual-constructor outputs at G P K Δ / G P Γ K,
   with every context cast and n+1 bound proved: met.
2. Concrete bounded old-position square and separate inserted/retained facts,
   including equal-labelled positional exclusions: met.
3. Complete ordered n+1 selected family, full outer versus original composite
   fibers, and unique fixed originals: met.
4. Correctly variant component equations and both Reduced equalities without
   coherence or reflection: met.
5. Full selected sums, exact contraction/endpoint losses n+1/n, strictness,
   empty-exchange contribution and unchanged other fixed ranks: met.
6. Counts, CutFree, exact asymmetric Atomized laws, tagged relations and
   inhabited constant/compound/two-three-copy/signed-cut boundaries: met.
7. Pinned Init-only closure, unchanged older interfaces, 185 source files /
   7,299 audited declarations and five expected control rejections: met.
8. Retained reports/evidence and separate committed-source/ref/Downloads
   comparisons: reports prepared; final receipts record procedural completion.

## (F) Not checked / uncertainty log

Pinned source §11.2 printed pp.248–253, rendered p.251 W2/W4 and the right
analogue on p.252 were directly consulted. Exact public types, 137 selected
axiom prints, complete import/transitive audit, baseline/final checks and
failed attempts are retained under
`provenance/wsl-gentzen-w2-selected-thinning/`. Only propext, Quot.sound and
Classical.choice are permitted; no choice-free claim is made.

Independent source transcription/kernel replay, Challenge/Solution/Comparator,
official preflight/service verification, fresh manuscript layout/compilation,
independent peer review and novelty assessment did not run. General elimination,
coherence and unconditional maximality remain open. No unavailable review is
reported as completed.

Strongest confirmed blocker: none for the scoped W2 instances.
Strongest suspected unconfirmed blocker: none established within scope.
Most important unchecked item: independent full source/kernel validation.
Dependence on unavailable material: none for this author-side audit.
Final recommendation: unknown for independent certification; the scoped
construction and local verification conditions above are met.
