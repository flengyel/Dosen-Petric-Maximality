# Author-side hostile review: terminal-tail disjoint contractions

## (A) Kill-shots / hard blockers

This AI-assisted author-side audit covers all nine new modules, the exact
public types and proofs, examples, source correspondence, checkpoint report
and current records. It is not independent peer review. No fatal blocker is
confirmed for the two specified terminal-tail instances.

| Anchor and claim tested | Failure mode tested / evidence | Finding |
| --- | --- | --- |
| TerminalContraction.Data and upper/lowerC0/C1/E0/E1; countE0/E1 | ill_typed, unproved / derivation | Data contains only original formulas/lists. All eight list identities and arity identifications are proved and used by actual G/At/Route casts. The generic frame stores endpoint identifications, not desired routing or rank conclusions. |
| copy_splice_tail; Data.square/product_square/coproduct_square | unproved, misuse_of_prior_work / derivation | A recursive numerical identity proves the all-position square, including selected and fixed coordinates. Universal components prove the product and coproduct equalities at the correct variance. Associativity is used only afterward. |
| selectedC_before, selectedE_inside and intermediate versions; selected_separated | false, inconsistent_use / derivation | C-selected indices precede the terminal E region. The proof uses positions, not labels, and requires no C≠E. |
| selectedC/E_transport, lengths, parametric, singleton and xC/xE_fiber | false, unproved / derivation | Both complete ordered lists and their n/n/m/m lengths are retained. Singleton fibers through the other same-side contraction are complete; no opposite-side lemma or membership-only surrogate is used. |
| xC_index/xE_index/retained_order; original_agree/other_fiber | false, unsupported_generalization / derivation | The terminal retained order is xC<xE, opposite to the interior case. Every other final coordinate has the same unique original position and singleton fiber through either complete route. |
| terminalTail_left/right, terminalDenoteL/R and generic denoteL/R | ill_typed, unproved / derivation | Concrete output types are G P K Δ and G P Γ K, respectively. Actual contractL/R and reindex implement both orders. Reduced equality uses the categorical square, not occurrence or inclusion reflection. |

No counterexample to these scoped claims was found. Each tested failure above
is excluded by an inspected derivation, not by an assumption restating the result.

## (B) Major weaknesses

No unresolved major defect is confirmed within scope. Three potential changes
of meaning were specifically tested:

1. Anchor: report “Exact proved endpoint and hypotheses”; public endpoint
   types in GentzenTerminalContractionInstances. Claim: arbitrary P, C,E and
   contexts with independent n,m≥2 and an existing premise. Failure modes
   unused_hypothesis and unproved; evidence exact public types and derivation.
   Bounds type the actual constructors. No atomicity, cut-freeness, equal
   arity, decidable equality or coherence is hidden. Generic square/separation
   hypotheses are discharged by concrete terminal theorems. No missing
   hypothesis was established; downstream scope remains the two local cases.
2. Anchor: terminalRankTableL/R, terminal_oldC_contractionL/R,
   terminal_newE_contractionL/R and terminal_sum_balanceL/R. Claim:
   old=(LC+n,LE+1), new=(LC+1,LE+m). Failure mode unsupported_generalization;
   evidence complete selected rank sums and fixed singleton contributions.
   Old→new decreases C by n−1 and increases E by m−1. Other same-side ranks
   remain 2+rho at their common original coordinate. The sum is not asserted
   to decrease, and ranks are not treated as Reduced-arrow invariants.
3. Anchor: report “Inhabited examples”; Terminal.twoThree, fixed_original,
   compound_left/right, emptyP_sum_increases and both_signs_actual_cuts.
   Failure modes false and unproved; evidence derivation and toy_test.
   Exact C=E source indices [0,1]/[3,4,5], final retained indices 0/2 and
   both composite maps [0,0,1,2,2,2] compile. The fixed equal-labelled index
   2 maps to 1. Actual Empty P constants inhabit the premises, including the
   2/3 sum increase. Independent 3/2 compounds and signed cut-containing
   premises are concrete, not universal statements over impossible inputs.

These are checks of correctness, self-containedness and correspondence.
No novelty or whole-manuscript claim is evaluated. No repair or extra
mathematical hypothesis is required by the inspected scoped statements.

## (C) Minor issues

Anchor: report opening, endpoint transports and rank discussion. Failure mode
ambiguous; evidence structural_argument. The report defines F/FE/FC/K and the
operational order before the denotation and rank equations, specifies Route.get
variance, and distinguishes contraction-subterm ranks from endpoint ranks.
This prevents reading a targeted decrease as a general decreasing measure.

Anchor: retained exploratory diagnostics. Failure modes ill_typed and unproved;
evidence compiler diagnostics followed by successful compilation. Explicit
inclusion of proof-only variables, placement of include/document comments,
transport argument grouping, arithmetic normalization, exact sum aliases,
typed At/Place congruence and removal of unsupported pp.width repaired failed
attempts. No statement, equation or heartbeat budget was weakened. The final
proof bytes match the previously recorded successful source inventory, and
fresh required checks also pass. Severity: repaired implementation detail;
no remaining mathematical impact is established.

## (D) Cross-section consistency failures

The report, statement/coverage maps, source correspondence, validation, README
and continuation identify exactly the two terminal-tail W1 cases. W3 and
disjoint interleaved configurations remain separate. Earlier fixed-gap proofs
are not rewritten; the new generic interface has four rfl comparisons with
their old/new constructions. Terminal xC<xE is not confused with interior xE<xC.

Reduced syntax/equations, Positive/G/Rewire, denotations, positions, predecessors,
rank definitions and proof predicates remain byte-preserved. Equality is in
the syntactic Reduced quotient. Product maps go ante K→ante F and coproduct
maps go succ F→succ K; no contravariant arrow-negation construction is invoked.
An arbitrary existing f is required, so no empty hom-set is filled and no zero
arrow without a witness is introduced. The familiar two-object one-arrow
test is addressed structurally: no inverse of f, reversed f, or arrow between
arbitrary endpoints is used. This is not a claimed new categorical model.

Manuscript v4/v5, diagrams, references and historical reviews are unchanged.
Source §11.2 p.251 W1 and p.252's right analogue are distinguished from p.251
W3. The source citation does not replace a Lean proof. The unsupplied
coherence inputs and conditional maximality transfers retain their scope.
No remaining cross-record conflict was confirmed after updating current records.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding local completion claim:

1. Concrete left/right pairs at the exact common K, all eight context
   equalities and actual constructors/casts: met in Data and Instances.
2. Concrete all-position square and correctly variant categorical squares,
   without coherence or equality reflection: met in Routing and Frame.
3. Ordered selected transports, n/n/m/m lengths, C=E separation and complete
   same-side singleton fibers: met in Routing and FrameFibers.
4. Terminal retained order xC<xE and unique common originals/complete fibers
   for every other final position: met in Data and FrameFibers.
5. Both full rank tables, subterm balances, independently directed strict
   comparisons, exact sum balance and unchanged other fixed ranks: met.
6. Counts, CutFree/Atomized equivalences and complete tagged relations,
   inhabited boundary examples and actual unequal-arity sum increase: met.
7. Frozen interfaces, pinned Init-only toolchain, complete import/transitive
   axiom checks and all five expected negative-control rejections: met,
   171 files and 6,705 audited declarations.
8. Retained reports/evidence and separate committed-source/ref/Downloads
   comparisons: reports prepared; final delivery receipts record completion.

## (F) Not checked / uncertainty log

The pinned September 2007 source, printed pp.248–253 and rendered p.251,
and the hash-verified KLR writing source were directly consulted. Exact
source hashes, public types, 122 selected axiom prints and initial/resumed
verification are retained under
`provenance/wsl-gentzen-w1-terminal-tail-contraction/`. All project declarations
are transitively audited; only propext, Quot.sound and Classical.choice are
permitted. This is not a choice-free result.

No independent source transcription/kernel replay, Challenge/Solution/Comparator,
official preflight/service verification, manuscript recompilation/layout review,
independent peer review or novelty assessment ran. General W1/W2–W6,
all-site replacement, Reducibility, Blocked-w, cut elimination, coherence and
unconditional maximality remain open. The report does not diagnose a manuscript
defect from an unfinished formal reconstruction.

Strongest confirmed blocker: none for these two terminal-tail instances.
Strongest suspected unconfirmed blocker: none established within scope.
Most important unchecked item: independent full source/kernel validation.
Dependence on unavailable material: none for this author-side audit.
Final recommendation: unknown for independent certification; the inspected
scoped construction and local verification conditions are met.
