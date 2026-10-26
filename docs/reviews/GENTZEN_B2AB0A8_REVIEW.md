# Source and evidence review of the completed binary integration

The inspected source and retained logs support Codex's scoped report at
`b2ab0a89bddc396dc7b6c0a4ccc30be08d4a088e`. Both full Reducibility Lemmata
remain open. The next instruction is
[CODEX_AFTER_B2AB0A8_REDUCIBILITY.txt](../CODEX_AFTER_B2AB0A8_REDUCIBILITY.txt).
This author-side review examines the reported endpoint, selected proof bodies,
source identity and the proposed continuation; it is not independent kernel
verification or peer review. The completed-run report preceded this handoff.

## (A) Kill-shots / hard blockers

**Full Reducibility is still unproved.** Anchors:
`DosenPetric/GentzenReductionStatements.lean`, definitions `ReducesL/R`;
`DosenPetric/GentzenBinaryInputReducers.lean`, `left/right` and
`selection_left/right`; integration report §7. The general definitions require
a witness at every actual address and the complete eligible-descendant bound.
The proved dispatchers require `f.ruleKind.Binary` and cover conjR, disjL,
mix and the internally impossible cut case. They do not cover unary inputs.
Failure mode: **unproved** if full completion were asserted. Evidence:
**structural_argument + absence_in_text**. Impact: the general endpoint and
its later Blocked-w consequences remain unavailable. Severity: a major blocker
to full completion, repairable by the remaining constructions. Codex's actual
report acknowledges this; no false completion claim is attributed to it.

No confirmed blocker to the reported binary-input theorem was found in the
inspected source and evidence. This is a scoped assessment, not a reproof of
every transitive declaration.

## (B) Major weaknesses

**The unrestricted exchange square remains to be constructed.** Anchors:
`GentzenGapExchangeData.lean`, `Data.outside0`, and integration report §7.
The fixed-gap interface excludes selected positions from the swapped interval.
It cannot instantiate the arbitrary same-side exchange target. Failure mode:
**unproved**, or **unsupported_generalization** if its restriction were omitted.
Evidence: **structural_argument** from the explicit hypothesis and the changed
order of selected sublists. Impact: unary dispatch remains incomplete.
Severity: major for the full target; repairable. The new instruction specifies
ordered pre-exchange extraction, the lower-context permutation and its actual
product/coproduct component equations.

**The two terminal-source one-premise W6 packages remain open.** Anchors:
`GentzenSourceOneSingletons.lean`, `blockedFirst/Second` and
`oldFirst/Second_singleton_blocked`; current continuation's W6 checklist.
Those declarations prove general repair blockedness and singleton old
blockedness. They do not give the requested general terminal-source old/new
definitions, rank equations and addressed results. Failure mode: **unproved**
for that source-correspondence obligation. Evidence: **absence_in_text +
structural_argument**, with the separate native producers explicitly inspected.
Repair: reuse these blockedness theorems and the now-proved terminal naturality;
complete the two packages without rebuilding native binary dispatch.

The later outside-site transport and finite multiset argument remain distinct
obligations. Bounds inside a replacement do not by themselves prove that all
outside or containing reducible sites have the required behavior.

## (C) Minor issues

The full-paper contract's immediate-continuation paragraph still called
`1e967bc` the current Lean baseline and directed work to the now-completed
two-premise W6 construction. The current continuation correctly superseded
that passage, but the stale wording could restart completed work. The handoff
updates that operational paragraph to `b2ab0a8` and the actual remaining tasks.
This is documentation consistency, not a manuscript or Lean defect.

The author's sequencing correction is now explicit in project instructions:
review a completed local run before issuing its successor handoff. This governs
the reviewer and adds no approval or stop condition to local implementation.

## (D) Cross-section consistency checks

| Claim | Evidence and assessment |
|---|---|
| Full descendant quantifier | `ReducesL/R` quantify over every actual containing address, replacement descendant address and typed position, with reducibility relative to the rebuilt cut. The binary signatures use these definitions directly. |
| Internally matched inputs | Mix, both conjunction directions and both disjunction directions obtain selections from the actual block. `Split` and `HeadSplit` jointly determine the indexed selection and lower context. Exported types do not request a decomposition or rank hypothesis. |
| All native binary branches | The final binary dispatcher cases on the input proof. The cut branch contradicts cut-freeness inherited from `hr`; no extra CutFree premise is added. |
| Smallest right W4 case | `NonemptyRight.old_rank`, `inner_rank` and `singleton_old_rank` give old `S+n+2`, inner `S+δ(n)`, and old `S+3` at n=1. `SingletonRightRegression.old_reducible` supplies an inhabited Empty-variable example; its inner operation is node-free. |
| Terminal/native distinction | `SourceLeft.old_rank` counts all macro exchanges. `NativeLeft.addressed_left` instead uses `ContractionBound` through its actual repair. Source singleton blockedness is not transferred along denotation equality. |
| Categorical equality | The inspected terminal proof uses retained-route factorization and `Rules.terminalDisjLeft_nat`; occurrence-relation equality is obtained afterwards by congruence. No occurrence-equality reflection is used there. |
| Strict run | The downloaded merged strict log hashes to `a93c79ca9d61ba80fc9ea611bb63f4462ed877d6f22058eb3663c9f83acda7b9`, matching its receipt. It records 330 screened files, 9,737 audited project declarations and successful build/audit completion. |
| Five negative controls | The audit-boundary log records rejection of direct, private and hidden-dependency axioms; the presentation-boundary log records rejection of identified projections and unwitnessed zeros. Their SHA-256 hashes match the merged receipts. |
| Whitespace failures | The merged cached-diff check did fail before correction. `RECORDS_CHECKS.json` retains that failure and subsequent successful checks. The report discloses the distinction; it is not evidence that the final check failed. |
| Committed-source continuity | GitHub comparison from `f4bc6ff15b27543db28e66065a8013ce0d052039` to `b2ab0a8` contains no Lean-file change. The 58 downloaded text files match their committed Git blobs; 38 covered by `CHECKED_SOURCES.sha256` also match those hashes. This is a sampled source/manifest comparison, not a new entire-source kernel replay. |
| Attachments and manuscript | All three supplied integration reports are byte-identical to their committed copies. All seven manuscript file blobs match the prior reviewed repository snapshot. No manuscript revision is required by this review. |

The proposed exchange construction was checked independently at the level of
tagged lists. When both swapped blocks contain selected copies and the suffix
contains none, the first exit exchange swaps the surviving blocks; the second
moves the retained C across `R_Y++L_X`. In all other regimes one exchange
suffices. Fixed equal-label occurrences keep their distinct tags. The positional
square commutes in a finite check of 21,119 cases, covering all four-segment
partitions of total lengths 2 through 7 and all selected subsets of size at
least two. See
[the diagnostic script](../../provenance/chatgpt-b2ab-review/exchange_positions.py).
This **toy_test** supports the proposal but does not prove the general Lean
construction, categorical square or address theorem.

The rank argument for that proposal is separate: old retained rank `S+n+1`
and inner retained rank `S+1` give a strict bound at the inner contraction.
`ContractionBound.exchangeL/R` can lift a bound through actual exchange nodes,
which are not lower contractions. Thus a two-exchange repaired root may tie
the old root at n=2 without invalidating the target. This is a mathematical
derivation to implement, not a newly compiled declaration.

## (E) Acceptance conditions, non-negotiable

1. Complete both terminal-source one-premise packages with exact coordinates,
   Reduced equality, actual blockedness, ranks and addressed conclusions.
   Until then that source-correspondence item remains open.
2. Prove both unrestricted exchange producers, including retained-copy
   relocation and fixed equal-label positions. A fixed-gap square or a
   caller-supplied permutation does not satisfy the endpoint.
3. Close every remaining unary/basis branch internally and export both general
   `Reduces` theorems with the unchanged full quantifier. Failure leaves full
   Reducibility incomplete.
4. Establish outside-site and containing-blocked transport before claiming
   finite multiset descent and Blocked-w.
5. Preserve required source/axiom boundaries, meaningful verification and
   exact claim correspondence. Complete the broader v6 contract before calling
   the paper fully formalized; service acceptance requires separate evidence.

## (F) Not checked / uncertainty log

Inspected the uploaded reports, current instructions and claim-map updates,
exported binary dispatch and selection matching, terminal-source W6 equality
and ranks, right-W4 singleton coverage, and the contraction-bound infrastructure
used by the proposed exchange proof. Read the relevant September 2007 book
passages at printed pp.250–252 from the previously hash-verified source.
The full v6 source was read earlier in this conversation; this pass did not
repeat a whole-manuscript correctness or novelty review.

No Lean/TeX build, independent clean kernel replay, Comparator, Palomar preflight
or submission was performed by this reviewer. The local WSL working tree,
stash, live SSH state and Downloads receipt are not accessible here. Codex's
report of twelve byte-verified deliveries is retained as its report, not an
independently observed cloud delivery. The source inspection does not certify
all 81 new modules independently of the retained local verification.

Strongest confirmed blocker to full completion: unrestricted unary dispatch.
Strongest suspected, unconfirmed mathematical blocker: none with positive
evidence in the scoped completed results. Most important unchecked proposed
result: the general Lean proof of the exchange component square and full
descendant bound, followed by the remaining dispatcher. This assessment does
not depend on an unavailable mathematical source. Final recommendation:
**reject a full-completion claim; retain the supported binary checkpoint and
proceed with the concrete continuation.** An unrestricted publication decision
remains outside this review.
