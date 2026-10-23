# Author-side hostile review: fixed-gap disjoint contractions

## (A) Kill-shots / hard blockers

This AI-assisted author-side audit covers the ten new modules, their actual
public statements, source correspondence, report and current records. It is
not independent peer review or certification. No fatal blocker was confirmed
for the two specified fixed-gap commutations.

| Anchor / claim tested | Failure mode / evidence | Finding and scope |
| --- | --- | --- |
| Disjoint.Data upperC0/lowerC0/upperC1/lowerC1/upperE0/lowerE0/upperE1/lowerE1; countC/countE0/countE1 | ill_typed, unproved / derivation | All eight list equalities and three count equalities are constructed. Actual G/At/Route casts use them. Data stores only original input lists/formulas; no desired conclusion is a field. |
| copy_splice_square, Data.square/product_square/coproduct_square | unproved, misuse_of_prior_work / derivation | All-position square is proved recursively, including selected/fixed positions. Correct p/q variance and universal components give Reduced equality before associativity is used. No occurrence/inclusion reflection or coherence input. |
| selectedC/E_transport; four lengths | false, unproved / derivation | Complete ordered lists, not membership-only transport, retain every selected tag and multiplicity. Order/injectivity is restricted to the particular excluded/fixed selected lists; no global monotonicity or injectivity. |
| selected_disjoint, selectedC0_gap_exclusion, selectedC/E_singleton, xC/xE_fiber | inconsistent_use, false / derivation | C copies are outside the designated gap; E copies are inside it. Complete same-side singleton fibers follow from fixedCopyAt/fiber_copies_fixed. Images avoid the other retained index even C=E. No opposite-side lemma is substituted. |
| xE_index/xC_index/retained_order; original_agree/other_fiber | false, unproved / derivation | Retained E precedes retained C by the exact requested equations. Every other final position has a unique common original position through both actual routes, with complete singleton composite fibers. |
| Four rank entries per side; oldC_contraction/newE_contraction; balances and strictness | inconsistent_use, unsupported_generalization / derivation | Independent n,m count all selected copies. Old→new lowers C by n−1 and raises E by m−1. Corresponding contraction-subterm additions are n/m. No principal-leaf or all-site claim. |
| sum_balanceL/R and emptyP_sum_increases | false, unsupported_generalization / derivation, toy_test | S(old)+m=S(new)+n; equal arity equality and actual n=2,m=3 sum increase compile. Thus the displayed sum is not offered as a decreasing elimination measure. |

No counterexample to the scoped endpoint is asserted. The unequal-arity
example excludes a possible overstatement about a generally decreasing sum.

## (B) Major weaknesses

No unresolved major defect was confirmed within scope. The following
potentially fatal changes of meaning were checked and excluded:

1. Anchor: Report “Exact proved endpoint” and fixedGap_left/right. Claim as
   written: two concrete constructions under arbitrary input data and two
   independent arity bounds. Failure mode unused_hypothesis / unproved;
   evidence exact public types and derivation. LeftLaws/RightLaws are outputs;
   their conclusions are never assumed to construct the pair. Bounds type
   actual constructors. Generic ContractionBlock helpers are derived wrappers,
   not an enlargement of G or Reduced. Downstream scope is precisely the two
   interior-gap results; no missing hypothesis was found.
2. Anchor: equal_label_indices/equal_label_fixed_tag and selected transport.
   Failure mode false / inconsistent_use; evidence derivation. With C=E=T,
   selected indices C0=[0,5], E0=[2,3,4], fixed original index 1 remain distinct.
   C1=[0,3], E1=[1,2,3], final fixed/E/C=0/1/2 and both maps
   [2,0,1,1,1,2] are checked against the actual typed routes. An actual Empty P
   constant specialization inhabits the premise. Labels do not select positions.
3. Anchor: report “Exact ranks” and next task. Failure mode
   unsupported_generalization; evidence structural_argument. These are local
   syntax ranks, not invariants of Reduced arrows. No arbitrary-address
   replacement, all-site rank decrease, multiset elimination proof, W3,
   Reducibility or Blocked-w construction is supplied or claimed. Those would
   require new proofs; they do not follow from the local rank table.

The stronger selected injectivity helpers require membership of only the
second argument, because its image has a fixed singleton fiber. This is a
proved strengthening, not a global injectivity assertion.

## (C) Minor issues

Anchor: retained exploratory logs and corrected code. Failure mode ill_typed /
unproved; evidence compiler diagnostics. Splice/Nat subtraction normalization,
unused/non-progress simp, list associativity, semireducible coordinate records,
explicit arity binding, rank-sum aliases and At/Place equality rewriting caused
failed elaborations. They were repaired with explicit equalities/abbreviations
and typed equality composition, preserving every target/interface/equation.
A combined coordinate test hit the default 200000-heartbeat limit (68-second
Lean run). It was replaced by small selected-index and route-index lemmas;
limits were not raised. A List.mem_map argument placement was corrected.
Commands, original diagnostics, exits and elapsed times are retained. Final
required verification passed after all proof changes. Severity is repaired
implementation/verification detail, with no remaining mathematical impact.

Anchor: report rank and sum explanation. Failure mode ambiguous; evidence
structural_argument. Applied wording distinguishes contraction-subterm changes,
targeted endpoint loss and untargeted endpoint increase. Both arities and the
orientation are defined before the table; the concrete sum increase is stated.

## (D) Cross-section consistency failures

Current correspondence, statement/coverage maps, validation, README and
continuation identify exactly the two fixed-interior-gap same-side contraction
commutations and their conditional future use. They do not mark all W1 or W3
complete. Terminal-tail, interleaved/shared-selected cases and remaining
exchange configurations are separate. The next task has explicit terminal
endpoints and positional conditions; it does not assume that the old interior
retained ordering carries over.

Every older DosenPetric source, grammar/equation, Positive/G/Rewire, analysis
predicate, predecessor and rank definition is byte-preserved. Lean 4.35.0,
Init-only dependencies, manuscript v4 and historical reports/access records
are unchanged. No new arbitrary-endpoint zero, empty-sequent proof, coherence
assumption, interpretation-kernel quotient or arrow-negation principle enters.
Count/predicates retain the premise once; occurrence equality is a consequence
of Reduced equality. No current-record conflict was confirmed within scope.
The three milestones and existing conditional coherence/maximality transfers
remain distinct.

An intervening SSH-origin commit, 2d240b2aa578b84277f59524d9f8819a41273a0d,
added manuscript v5 while retaining v4, with no Lean-source change. Verified
checkpoint work was preserved in local stash dedfd8fc8cd49930e9a162d5be585215b062a43c;
main fast-forwarded, then the work was reapplied. The README conflict was
resolved by retaining both the upstream v5/literature/review links and the new
proof-stage links. The statement map retained its upstream v5 header and the
new proof row. All other upstream changed/new files, including AGENTS, both
manuscript versions, checksums and v5 reports/evidence, were verified byte-for-
byte against that commit. No manuscript prose was edited by this checkpoint.
All required checks were repeated on the integrated tree; their new results
are the final verification record. The backup stash is retained locally.

A later non-force push of the proved checkpoint f75bfb2399106f7570e75953354b1d0965769e29
was rejected because SSH origin advanced again. The manuscript-only commits
7ddaebb23da983f14cc04ad9e24d070e171f1aa6 and cfa37604e539dc85d854959b20aca752d06774ce
were inspected and retained by clean merge c80d71f46e01afce4828c4d207e1c320533298ec.
They update v5 literature comparisons/bibliography and its PDF/checksums, with
no Lean-source change. All twenty changed/new upstream files were checked
byte-for-byte against cfa3760; v4 and this checkpoint's proof bytes remain
unchanged. Verification was repeated on this combined tree. This checkpoint
does not re-certify the unrelated literature review or compile its manuscript.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding completion claim:

1. Two actual contraction pairs with exact common K endpoints and all eight
   context equalities/counts/casts, with arbitrary P and premises: met.
2. All-position copies/copies square and both correctly variant Reduced
   categorical squares before denotation equality: met.
3. Complete ordered selected transports, lengths n/n/m/m, concrete separation,
   restricted order/injectivity and genuine same-side singleton fibers: met.
4. Distinct retained indices/images, both selected-family final images and
   complete unique inverse through either composite for every other position: met.
5. Four rank entries for each side, both directed balances/strictness,
   contraction-subterm comparisons, sum balance/equal arity, other 2+rho: met.
6. Actual unequal 2/3 sum increase, exact requested equal-label test, independent
   3/2 compounds, empty/nonempty contexts, inhabited Empty constants and signed
   cuts; count/predicate/full tagged relations: met.
7. Frozen interfaces, no circular coherence, all required sequential checks,
   162 files / 6,310 audited declarations and five expected rejections: met.
8. Reports/evidence retained and delivery/ref/source checks kept distinct:
   met for report/evidence preparation; final commit/ref/Downloads receipts
   record the remaining procedural checks separately.

## (F) Not checked / uncertainty log

Evidence: provenance/wsl-gentzen-w1-disjoint-contraction/. Every project
declaration is transitively axiom-audited; 95 selected prints are retained.
Only propext, Quot.sound and Classical.choice are permitted; no choice-free
claim. The pinned manuscript text/rendered p.251 and hash-verified governing
KLR cache were directly consulted. No new source discrepancy is asserted.

No independent kernel/source replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
independent peer review or novelty assessment ran. No Palomar preparation,
submission, publication, license or visibility action occurred. Unformalized
published results are obligations, not demonstrated manuscript defects.

Strongest confirmed blocker: none for these two fixed-gap instances.
Strongest suspected unconfirmed blocker: none established within scope.
Most important unchecked item: independent full source/kernel validation.
Dependence on unavailable material: none for this author-side result.
Final recommendation: unknown for independent certification; the scoped
construction and verification conditions above are met.
