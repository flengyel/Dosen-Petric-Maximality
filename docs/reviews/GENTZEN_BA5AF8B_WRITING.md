# Writing review of the Blocked-w checkpoint and successor instruction

The report distinguishes the proved Blocked-w theorem from the failed
post-atomization construction. The next instruction should specify one witness
with all required properties and explain why its route realization avoids
compound thinning. No manuscript change is justified by this source/evidence review.

This is an author-side review using
[mathematical-writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59).
Scope: the ba5af8bc2c1f3ec7c218d54b840fb1df5d24d61c report, both local reviews,
new proof statements/comments, current records, and the successor instruction.
It is not a fresh whole-manuscript review or mathematical certification.

## Governing source and existing outline

Consulted Knuth, Larrabee and Roberts, Mathematical Writing, §1, points 5,
10–14 and 26, using the [MIT-hosted copy](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf),
printed pp.2–3 and 5. The retained §4 excerpt, printed p.9, was also read for
its context-sensitive treatment of definition placement. The source advice
supports self-contained statements, connected explanation, definitions at
first use and consistent notation. The report format and prohibition on
editorial-process text in manuscripts are project/skill requirements, not
rules attributed to those authors.

GENTZEN_BLOCKED_W_REPORT.md has the following existing outline:

1. Opening result: Blocked-w and the remaining atomization obligation.
2. Baseline and exact endpoint: preserved source, typed arguments, equality and
   both universal tied-contraction clauses.
3. Dependency and occurrence correspondence: containing shapes, address
   correspondence, enumeration, rank replacement and well-founded induction.
4. Atomization obstruction and next exact obligation: the concrete negative
   example, the simultaneous target and later dependencies.
5. Boundary examples and verification: finite occurrence examples, command
   receipts and the limits of the local evidence.
6. Retention and delivery: artifact paths and post-commit verification records.

The main theorem is blocked_w; complete local Reducibility, complete site
correspondence and finite descent are its prerequisites. The organization
reflects that dependency order. No revised report outline is needed.

The successor instruction follows the remaining proof dependency: exact
simultaneous target; route realization with atomic omissions; support transport
through the selected fiber; all input producers with a joint witness; invariant
preservation during finite descent; later full-paper work; verification/delivery.

## Findings and concrete actions

| Anchor | Issue | Source principle or editorial rationale | Action |
| --- | --- | --- | --- |
| Report, exact endpoint and atomization section | Blocked and atomized representatives exist separately; this does not identify a common witness | KLR §1 point 5, self-contained statements; independent quantifier audit | State Topmost, Atomized, equality and AllBlocked together for the same f',g'. |
| Continuation, proposed economical route | “Omitted output slot” can obscure the direction of Route K F | Independent typing audit; KLR §1 point 14 | Define get from At F A to At K A and give the product/coproduct arrow types before the support condition. |
| Successor, support condition | Equal labels must not replace equal occurrences | KLR §1 point 11, explaining variables at use; independent occurrence convention | Quantify over a : At K A and absence of a preimage of that a. |
| Successor, strengthened reduction and descent | Independent existential witnesses cannot be combined without a proof | Independent mathematical scope audit | Require one h for CutFree, Atomized, equality and the entire descendant bound; reuse that h in the rank decomposition. |
| Current AGENTS, correction summary, validation title | Some current wording still points to completed Reducibility/Blocked-w obligations | Cross-document consistency rationale | Update current scope to simultaneous atomization/blockedness and preserve historical snapshots. |
| GentzenFiniteOccurrences.lean:100 | A literal plus joins two sentences in a comment | Local typographic rationale | Remove the stray plus during the next implementation pass; no theorem changes. |

## Definition order and notation

AllBlockedL/R are defined in GentzenBlockedNormalization.lean before the
normalization theorems. Their arguments determine the cut formula and entry
position. AtomicFormula already includes literals and both constants; the
successor states that convention explicitly before using its support condition.
Route K F, StructuralProgram P K F, their positional action, and both categorical
arrow types precede the recursion. The selected and residual contexts are
typed before the preimage equivalence is proposed.

The instruction introduces the old selected rank r, outside list O, inside
list I and List.Perm notation before the replacement law. The fixed finite
support bound belongs to the post-atomization descent; no rank comparison with
the initial unatomized proof is asserted. Existing terms Atomized, AllBlocked,
Topmost, Reduced equality and whole-formula ancestry keep their established
meanings. The proposal is identified as unproved in Lean.

The negative atomizer example is substantive mathematics and remains visible.
It is not expanded into a claim that simultaneous representatives fail to
exist, that the source book is wrong, or that the maximality manuscript needs
revision. Historical novelty and occurrence-substitution decisions remain settled.

## Priority and review scope

Use the exact simultaneous statement and joint replacement witness in the
successor instruction. Keep the report's existing mathematical distinction.
The current status corrections are documentation repairs; all thirteen new
proof modules and all manuscripts are preserved by this review pass.

The complete new instruction and both successor reviews were read as connected
prose, including their displayed statements and technical qualifications. No
manuscript source was edited or newly reviewed in full, and no rendered TeX
document or new Lean build was produced. Source and archived-evidence checks
are specified in GENTZEN_BA5AF8B_REVIEW.md. Reviews, verification scope and
workflow remain outside the mathematical manuscript and its source comments.

Retain this review in docs/reviews and deliver its committed bytes to Downloads
along with the new instruction and mathematical review. Those three new local
copies are pending; the six reported ba5af8b deliveries are not being repeated.
