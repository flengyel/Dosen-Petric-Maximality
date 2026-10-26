# Author-side review after full Reducibility

Reviewed checkpoint: `5b8a1996cab3f53e8c771dbd6126274236b1db4a`, after the
author supplied the completed local run. This review uses the
[HostileRefereeGPT instructions](skill://plugin_867af61c251c819194f29c5c462eafbe/instructions/SKILL.md).
It is a focused author-side source/evidence review and successor proof plan,
not an independent kernel replay, peer review or whole-manuscript verdict.

The inspected public exports have the advertised unchanged `ReducesL/R`
endpoints. The retained local verification evidence supports continuing from
full Reducibility. No confirmed defect in those endpoints was found in this
inspection. The next task is containing-blockedness preservation, followed by
complete eligible-site correspondence and multiset descent.

## (A) Kill-shots / hard blockers

**Global normalization is still unproved.** Anchor:
`GentzenReductionStatements.lean:13`, `GentzenReducibleOccurrences.lean:90`,
`GentzenOutsidePaths.lean`, and the current report's dependency table.
Claim inspected: all eligible descendants *inside* a repair have smaller rank;
incomparable proof occurrences retain their values, paths and cluster ancestry.
Failure mode: **unproved**, if these results alone are invoked as Blocked-w.
Evidence: **derivation** from the exact predicates. `ReducibleL/R` also requires
every proper containing tied contraction to be blocked, and the containing
proof values can change. Severity: blocking for a global termination theorem,
not a refutation of full local Reducibility. Repair: prove the two containing
shape theorems, partition all rebuilt addresses, and establish the exact
multiset replacement relation before performing induction.

There is no confirmed kill-shot against the completed local result. Cut
elimination, coherence, actual-presentation maximality and full-paper completion
must retain their recorded open status.

## (B) Major weaknesses

**B1. Preserving an outside cluster does not preserve full eligibility by
itself.** Anchors: `outside_cluster` and
`GentzenReducibleOccurrences.lean:95`, whose containing clause ends
`b.ProperContains a → BlockedL v` (right analogue at line 117).
Claim under examination: unchanged outside proof and
ancestry should leave the outside rank multiset unchanged. Failure mode:
**unproved**. Evidence: **structural_argument**; the new predicate can
quantify over a rebuilt common ancestor of the outside site and the repaired
site. Severity: major for descent. Repair: prove the blocked shape theorem
for arbitrary same-sequent replacements at proper lower-contraction sites,
then prove eligibility equivalence outside and exclude new eligible strict
ancestors. Track actual dependent addresses in both directions.

**B2. A local rank bound is not a natural-number decrease of the whole proof.**
Anchor: the final universal clauses of `ReducesL/R` in
`GentzenReductionStatements.lean:16` and line 23, and source §11.2, p.253.
Claim to establish: one repair strictly decreases a well-founded measure.
Failure mode: **unsupported_generalization** if maximum rank, rank sum or proof
size is assumed to decrease. Evidence: **derivation**; the conclusion permits
finitely many smaller replacement ranks, with no cardinality bound. Severity:
major. Repair: prove `R_old = O + {r}` and `R_new = O + I`, retaining
multiplicities and proving every member of `I` smaller than `r`. Prove
well-founded multiset descent. The instruction supplies a possible proof by
fixed-length multiplicity vectors; that proposal is not a checked Lean result.

**B3. Clean-cut normalization needs an additional atomization argument.**
Anchors: `GentzenRoutePrograms.lean:46`, `GentzenHeadAtomization.lean:17`
and line 26,
`PositiveThinningAtomization.lean`, and the paragraph after Blocked-w on source
p.253. Claim inspected: general repairs supply CutFree witnesses; the later
clean-cut theorem needs Atomized and blocked witnesses simultaneously.
Failure mode: **unsupported_generalization** if the two existing existence
theorems are simply composed. Evidence: **structural_argument**. Generic
`StructuralProgram.empty` can thin any formula. Conversely `headThinL` at a
disjunction and `headThinR` at a conjunction duplicate their proof argument and
apply context duplication. Thus atomization can alter contraction occurrences;
its established equality and CutFree properties do not prove the required
tied-site invariant. Severity: major for clean cuts. Repair: prove a concrete
compatibility construction, with the full relevant ancestry and rank/termination
obligations. The lack of an Atomized field is not a defect in `ReducesL/R`.

**B4. Termination must imply the stated normal-form property.** Anchor:
`GentzenReducibleOccurrences.lean:90` and line 112 (`ReducibleL/R`), and
line 43 (`ProofAddress.proper_length`). Claim to establish: no eligible
site implies
all tied contractions are blocked. Failure mode: **unproved** if treated
as a definitional equivalence. Evidence: **derivation**. An arbitrary unblocked
tied contraction may itself have an unblocked tied ancestor and hence fail
the eligibility predicate. Severity: major for the final Blocked-w conclusion.
Repair: choose an unblocked tied occurrence of minimal path length; its proper
containing tied contractions must be blocked. This supplies an eligible site
and gives the required contradiction.

## (C) Minor issues

The full-paper contract still named `b2ab0a8` as its reviewed integration
checkpoint and directed readers to its successor instruction, although the
following paragraph correctly recorded full Reducibility. The new handoff
updates that immediate checkpoint and link to `5b8a199`; older instructions
remain historical records. AGENTS' immediate-scope phrase and the coverage
map's outside-transport sentence are aligned with the same boundary. These
are instruction-record repairs, not manuscript or mathematical corrections.

No requirement to limit the exchange repair to the previous proposed one or
two exits survives as an extra proof obligation. The completed construction
may use more exits and bound eligible contractions through them. The old
proposal remains evidence of its own scope, not a competing implementation
requirement.

## (D) Cross-section consistency failures

No new cross-section mathematical inconsistency was confirmed. The active
instruction-pointer issues in (C) are repaired in this pass. The following
checks delimit the source and evidence that support that assessment.

| Check | Evidence and conclusion |
| --- | --- |
| Public theorem types | `GentzenReducibility.lean`, `Checks/Reducibility.lean` and the retained public-types log agree: arbitrary P, contexts, proofs and positions; no Binary/Unary, Atomized, supplied reduct or coherence hypothesis. |
| Descendant scope | `GentzenReductionStatements.lean` quantifies every actual address in the replacement and every position satisfying Reducible relative to the rebuilt cut. The root address is included. |
| Dispatch | `AllInputReducer.left/right` case-split on actual input syntax and call the completed producer families. This review did not independently reprove all 67 new modules. |
| Containing shapes | All seven constructors per side were inspected with `BlockedSource`. Proper contraction sites must lie in free proof parameters; disjLLast contains actual exchanges. The proposed preservation result remains to be formalized. |
| Address multiplicity | Outside transport uses actual sibling divergence and preserves paths. Equal proof values in different branches remain distinct sites. |
| Local strict evidence | Final strict receipt exits 0; its log reports 398 source files, successful build, and a transitive axiom audit of 10,606 project declarations. |
| Controls and types | Final audit/presentation logs record all five expected rejections; public-types receipt exits 0 and its log displays the unrestricted exports. |
| Source identity | The 414-entry inventory has SHA-256 `4b8eb0f9febbd470d8c7ddd7c74e51c2a22b8492a9f0830d9cf9be8fa53c37db`. Sixteen locally materialized proof/check files matched their inventory hashes. This is a sample, not a new check of all 414 file bytes. |
| Log identity | Compressed and decompressed SHA-256 values for the final strict, audit-boundary, presentation-boundary and public-types logs match `LOG_ARCHIVES.json` and the relevant final receipts. |
| Supplied documents | Git blob hashes of all six uploaded instruction/review/report files match the repository tree at the reviewed commit. Their Downloads delivery is reported by the local run; the cloud review cannot independently inspect that destination. |
| Manuscript and authority | No manuscript revision is indicated. The v6 endpoint, accepted corrections, private visibility and local/cloud division of work remain in force. |

The source passage consulted for Blocked-w and clean cuts is Došen–Petrić,
*Proof-Theoretical Coherence*, September 2007, §11.2, printed p.253, retained
in `provenance/wsl-gentzen-full-reducibility/SOURCE_P248_P253.txt`. The
[authors' book PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf)
is the primary source. This continuation does not reopen novelty or priority.

## (E) Acceptance conditions, non-negotiable

1. Preserve the completed unrestricted endpoints and every descendant quantifier.
2. Prove both containing-blocked shape statements for all actual envelopes.
3. Account for every old/new eligible address and retain occurrence multiplicity.
4. Prove the well-founded multiset decrease rather than assuming a global rank drop.
5. Export Blocked-w with the same cut formula, cut-free premises, Reduced equality
   and both universal blockedness clauses.
6. Establish simultaneous atomization/blockedness before claiming clean cuts.
7. Verify new source, dependencies and committed-byte identity locally; retain
   honest distinctions among local, independent-kernel and registry statuses.
8. Keep manuscript corrections evidence-based and all documentation/delivery
   records consistent with the actual checked scope.

Failure of condition 1 defeats the completed Reducibility claim; failure of
conditions 2–5 withholds Blocked-w; failure of condition 6 withholds clean-cut
normalization. Conditions 7–8 govern verification and task-completion claims.
These conditions do not impose a fresh approval checkpoint on local Codex.

## (F) Not checked / uncertainty log

Strongest confirmed outstanding issue: the local-to-global eligibility and
termination arguments remain unproved. Strongest suspected defect: none
established in the completed public endpoints; no counterexample is asserted.
Unchecked here: a fresh Lean/TeX build, independent replay of the full proof
closure, all 414 source bytes, WSL working-tree/stash/SSH state, Downloads
contents, and whole-paper correctness. Those local-state assertions remain
attributed to the supplied completion report and retained receipts.

The WSL repository and `/mnt/c/Users/fleng/Downloads` are unavailable to this
cloud session. Retain this review in `docs/reviews/`; its byte-verified Downloads
copy is pending local delivery under the successor instruction.

Final certification recommendation: **unknown**; full independent proof
checking is outside this review and local-state/delivery claims depend on
unavailable WSL material. The strongest confirmed blocker to the next theorem
is the unproved eligibility/descent argument; no separate suspected defect in
the completed endpoints is established. The most important unchecked item is
independent replay of the full proof closure. The available evidence supports
the operational recommendation to continue with
`docs/CODEX_AFTER_5B8A199_BLOCKED_W.txt`, preserving full Reducibility and keeping
cut elimination, coherence and publication readiness open. No new mathematical
result is claimed by this review or its proposed proof strategy.
