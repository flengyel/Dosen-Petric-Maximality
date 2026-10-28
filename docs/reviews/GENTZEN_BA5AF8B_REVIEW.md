# Completed-run review of ba5af8b

## (A) Kill-shots / hard blockers

The inspected source and retained local verification support the reported
Blocked-w endpoint. No confirmed defect in that endpoint was found. This is an
author-side audit using [HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe),
not independent peer review or a new kernel replay. The reviewed commit is
ba5af8bc2c1f3ec7c218d54b840fb1df5d24d61c, whose parent is the successor-instruction
commit 85a16cdc077e8a3c4deedd3b7a521361e1e54e54.

**Preservation by the existing atomizer is false.** Anchor:
GentzenAtomizationBlockedBoundary.lean:12, before; :38, new_tied;
:45, new_unblocked; :54, atomize_not_blocked; :58, cutFree_equal_atomized.
The tested implication is that AllBlockedL is preserved by G.atomize on
cut-free inputs. Failure mode: false. Evidence: counterexample. The displayed
proof has type G Empty [top, disj top bot] [top] and no left contractions.
After atomization, the occurrence at [0,0,0,0] is tied to the first antecedent
top and has a left contraction above native disjL. Its immediate-premise kind
is excluded by BlockedL.premise_kind. Equality, cut-freeness and atomization
remain true. Severity: fatal for this preservation claim, not for Blocked-w
or the existence of clean cuts. Repairability: construct compatible witnesses
by another procedure; retain the counterexample unchanged.

This distinguishes a refuted construction from the unproved simultaneous
existence theorem. Neither gives a counterexample to the manuscript's maximality
result. The source comparison is Došen–Petrić, September 2007, §11.2, printed
p.253, using the retained SOURCE_P248_P253.txt: the Blocked-w statement precedes
the paragraph requiring both atomization and blockedness for a clean cut.

## (B) Major weaknesses

**Simultaneous clean-cut normalization remains unproved.** Anchors:
GENTZEN_BLOCKED_W_REPORT.md, “Atomization obstruction and next exact obligation”;
GentzenBlockedNormalization.lean:79 and :89. Claim as written: the completed
theorems give Topmost, Reduced equality and AllBlocked on both sides; they do
not assert Atomized. Failure mode: unproved for the next theorem, not a false
statement of the completed theorem. Evidence: absence_in_text in the exact
public signatures and the explicit negative example above. Downstream impact:
the proposed clean-cut route to elimination and coherence still needs a joint
construction. Severity: major for the unfinished formalization. Repairability:
the new instruction specifies atomization first, followed by blocked reduction
whose single replacement witness preserves Atomized and the full descendant bound.

The proposed economical route realization is not certified by this review.
Its finite recursion has a precise invariant: every position omitted by a
Route K F has an AtomicFormula label. The missing proof obligations include
transport of that invariant through selected-fiber removal, realization by
existing structural rules, and integration into all input producers. They are
proof targets in CODEX_AFTER_BA5AF8B_CLEAN_CUTS.txt, not new production assumptions.

## (C) Minor issues

**Several current status phrases lagged behind the exported theorem.** Anchors
at the reviewed commit: AGENTS.md, “from full Reducibility toward Blocked-w”;
MANUSCRIPT_CORRECTIONS.md, “Proof obligations are tracked separately,” which
still listed containing transport and Blocked-w as unfinished; VALIDATION.md,
title “Current full Reducibility validation.” Failure mode: inconsistent_use.
Evidence: citation to blocked_w and replace_lower alongside these phrases.
Severity: minor documentation inconsistency; repairable without a proof change.
The successor documentation updates these current statements and preserves
historical sections with their original scope.

GentzenFiniteOccurrences.lean:100 has a stray plus in its documentation comment,
between “records.” and “Only”. This is optional local prose cleanup in the next
implementation pass, with no mathematical effect. No Lean source is changed
by this review.

## (D) Cross-section consistency failures

No additional mathematical inconsistency was confirmed in the reviewed scope.
The following checks bear on the central inference, rather than declaration counts.

| Claim | Typed construction or law inspected | Result |
| --- | --- | --- |
| Containing blockedness | BlockedL/R.replace_lower, GentzenBlockedReplacement.lean:223 and :233; arbitrary local formula D, proper address, actual same-side lower contraction, arbitrary replacement at the same sequent | All fourteen envelopes are reconstructed. Fixed logical/exchange nodes are excluded by the lower-contraction premise. |
| Complete address correspondence | ProofAddress.compare/split_prefix; ReducibleL/R.blocked_containing, outside_iff and new_site | Actual dependent occurrences are used. The new-site split includes the inserted root; strict containing tied contractions remain blocked. |
| Full outside eligibility | GentzenOutsideEligibility.lean, both outside_iff proofs | Common containing ancestors use the blocked-shape theorem; other ancestors use forward/inverse outside transport. Unchanged local proof values alone are not substituted for this argument. |
| Finite enumeration | ProofOccurrence, occurrence_eq_of_path, EligibleEnumeration.key_spec, keys_nodup and keys_path_unique | Distinct paths with equal subproof values remain distinct. The unique lower position justifies one key per eligible occurrence; mapping keys to ranks retains equal-rank multiplicity. |
| Exact rank replacement | GentzenRankReplacement.lean:74 and :157 | Old ranks permute to r::O, new ranks to I++O, every inside entry below r; outside_keys uses both directions of correspondence. |
| Well-foundedness | FiniteRankDescent.lean:53, :70, :98 and :103 | One finite support bound is fixed during accessibility; higher counts agree and a pivot count decreases. Fixed-length product lexicographic order is used. |
| Terminal condition | GentzenUnblockedAncestor.lean, exists_reducible_left/right | Strong induction on path length finds an eligible unblocked ancestor. Absence of eligible sites therefore implies AllBlocked. |
| Both normalized premises | GentzenBlockedNormalization.lean:79 and :89 | Per-premise equalities imply cut equality. Each AllBlocked predicate depends only on its own premise and cut-entry position, allowing successive normalization. |
| Public statement | Checks/BlockedW.lean and the archived public-type log | Arbitrary P, original formula and contexts, Topmost, Reduced equality, and both complete tied-contraction clauses; no atomization or coherence assumption. |
| New boundary example | GentzenAtomizationBlockedBoundary.lean:58 | One package proves all positive properties and failure of blockedness for the same atomized proof. |

The category is the existing Reduced quotient. Denotations are arrows from
ante Gamma to succ Delta. Category.comp applies its first argument first;
the coproduct-side structural category is opposite. The proof uses categorical
equations, not faithfulness of an interpreted relation. Existing-arrow witnesses
for zeros and potentially empty hom-sets are retained. No new categorical
interface or functor is introduced by this checkpoint.

The successor's route condition is positional. In particular, using one of two
equal-labelled compound positions does not make the other position used. For
the proposed stronger reduction, Atomized, equality and all descendant bounds
must belong to one replacement witness. The existing rank_replacement proof
must consequently accept that chosen witness, instead of choosing another
unrestricted witness and appending an unsupported Atomized claim.

## (E) Acceptance conditions, non-negotiable

1. Preserve the public Blocked-w, containing-shape and unrestricted Reducibility
   signatures and their dependency closure. Endpoint drift would invalidate
   the corresponding completed-result claim.
2. Prove the economical-program support condition for actual input rules and
   residual positions, or prove another concrete compatibility route. A helper
   conditional on an unsupplied support witness does not discharge clean cuts.
3. Prove the joint atomized replacement theorem on both sides, with every actual
   rebuilt eligible descendant quantified; instantiate every input family.
   Failure leaves the proposed normalization route incomplete.
4. Use the same witnesses in rank replacement and invariant-preserving descent;
   export actual same-sequent simultaneous representatives. Failure leaves
   simultaneous clean-cut normalization open.
5. Retain the negative atomizer example and verify the new positive theorem on
   a topmost cut with G.topI and its before proof. Keep later elimination,
   coherence, actual-presentation and appendix claims open until separately proved.
6. Verify changed final sources, public types, dependency closure, five controls,
   manuscript hashes and checked/committed bytes, and deliver the required
   reports. Failure limits the respective verification or delivery claim.

These are conditions on the implementation and evidence. They do not impose
a fresh author approval checkpoint or request a manuscript revision.

## (F) Not checked / uncertainty log

Read all thirteen newly added public modules, the new exact-signature check,
the report and both local reviews, current instructions/maps/corrections, and
the relevant existing routing, atomization, replacement and dispatch code.
The source changes at this checkpoint add those modules and extend the public
import and axiom-check files; existing production definitions and manuscripts
are not edited by the commit.

The 428-entry source inventory was inspected. Thirty-three retrieved source
files, including all fourteen newly added Lean files and both modified Lean
files, were independently compared with their inventory SHA-256 and committed
Git blob hashes. Seven final archived logs were checked against both compressed
and decompressed digests: strict, both control scripts, both public-type checks,
manuscript hashes and whitespace. The logs record 412 screened sources, 10,906
audited project declarations and five expected rejections. The public log gives
the complete Blocked-w type and its permitted foundational dependencies.

This review did not download and rehash all 428 files, rebuild Lean, replay a
second kernel, run Comparator, or use a Palomar service. Full inventory identity,
local/origin/live SSH agreement, stash preservation and the six Downloads
deliveries are the author's/local run's reported outcomes; WSL state and those
destinations are not independently accessible here. No whole-manuscript
correctness or novelty reassessment, TeX build, or publication action was made.

The new instruction and these two successor reviews are retained in the
repository; their three new Downloads copies await local Codex's byte-verified,
conflict-preserving delivery. Previously reported deliveries remain recorded
as complete. No unchanged-baseline rebuild is requested.

Strongest confirmed blocker: the existing atomizer fails the needed preservation
claim. Strongest suspected unconfirmed blocker: none established against clean-cut
existence; the proposed route-support and atomized-producer proofs remain open.
Most important unchecked result: the joint atomized/blocked construction.
The source-level findings use available evidence; independent kernel and local
delivery certification depend on checks not performed here. Final recommendation:
unknown for whole-paper certification; the inspected evidence supports retaining
the completed local Blocked-w result.
