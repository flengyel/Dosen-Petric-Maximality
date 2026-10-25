# Review of Gentzen Reducibility checkpoint 05c6bc8

Reviewed checkpoint: `05c6bc8a86126fde494a9c9f2b42e693687b76d6`.
Review date: October 24, 2026 (America/New_York).
This is an AI-assisted author-side mathematical and editorial audit.

The checkpoint addresses the previously identified replacement-and-rank gap, but neither full Reducibility Lemma is proved. The addressed left-W4 result has the required descendant quantifier under an extra injectivity hypothesis. The proposed entry-frame proof is relevant to removing that hypothesis. The right-W4 replacement needs a separate argument that follows eligible contractions through its exchanges.

## (A) Kill-shots / hard blockers

### A1. Both full Reducibility Lemmata remain unproved

**Anchor:** [GentzenReducibilityLogical.lean, line 38](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenReducibilityLogical.lean#L38); the report's opening and exact target.

**Claim as written:** `addressed_left_of_injective` gives cut-freeness, local and rebuilt Reduced denotation equality, and a strict rank bound for every contraction reducible after replacement.

**Finding:** The claim is correctly qualified by `a.InjectiveAscend .left` and restricted to terminal-left W4. It is not the general left lemma. There is no full right producer among the reviewed declarations. Failure mode: **unproved** for any claim of full Reducibility; evidence: actual theorem types and proof bodies. Severity: major for completion, with no false completion claim in the supplied report. Repair requires general producers from the existing `ReducibleL/R` hypotheses, without a caller-supplied replacement, injectivity, or assumed rank conclusion.

The source target in Došen–Petrić, September 2007, §11.2, printed p.250, concerns every contraction inside the replacement that is reducible after replacement; the right analogue is on p.252. It does not require every positional rank to decrease. [Primary source](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).

### A2. The existing right-W4 candidate fails in a concrete two-copy root case

**Anchors:** [terminal_right_w4_unblocked, line 44](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenReducibilityObstructions.lean#L44); [right endpoint ranks, line 150](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenSelectedLogicalRanks.lean#L150); [ReducibleR, line 112](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenReducibleOccurrences.lean#L112).

The committed theorem proves that the terminal candidate `newR` is unblocked. Its contracted disjunction introduction has a nonempty prefix; the corresponding blocked unary pattern requires an empty prefix.

A stronger consequence follows from the committed definitions and rank formulas. Let `P = Empty`, let `A = B = bot`, put `C = disj bot bot`, and use `gs = [[],[]]` and `Θ = []`. The existing `W4.SelectedLogical.Examples.constRight` gives the premise of type `G Empty [bot] [C,C,bot,bot]`; use `BlockedExamples.l [C]` as the opposite cut premise of type `G Empty [C] [top]`. These constant constructions are cut-free. Both `oldR` and `newR` then have type `G Empty [bot] [C]`.

Both roots are unblocked contractions tied to the cut. For the old root, use the same nonempty-prefix observer argument as for the new root. The proper-containing-contraction condition is vacuous at the root. Thus the new root itself remains reducible after replacement. If `L = rankInnerR`, the checked endpoint formulas give old rank `L+3` and new rank `L+3`. The strict inequality fails at that root.

This is a **source-derived counterexample to this candidate**, not a newly compiled Lean example and not a counterexample to the existential Reducibility Lemma. No minimality claim is made. Failure mode: **false** if this candidate is claimed to witness the full target at two copies. Severity: major for that route; repairable by another candidate or argument. A compiled regression should establish all the stated typing, cut-freeness, reducibility, and rank facts.

## (B) Major weaknesses

### B1. Entry uniqueness is still a hypothesis, but it has a concrete proof route

**Anchors:** [boundary criteria, line 70](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenReducibilityBoundary.lean#L70); [EntryFrame.unique_origins, line 49](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenEntryFrames.lean#L49).

For a proof address `a` from a cut premise to the chosen contraction `w`, ascent follows a whole-formula position from `w` toward the cut premise. The needed statement concerns only the positions that ascend to the distinguished cut-formula position. It does not require injectivity for every formula position.

The proof of `entry_unique_of_injective` merely applies its injectivity hypothesis. The missing inference from reducibility remains **unproved**. Evidence: the hypothesis and two-line proof. Severity: major for arbitrary-address W4.

The following is an unformalized structural proof plan.

1. Suppose distinct positions `x,z` in `w` ascend to the same cut position.
2. Traverse their ancestry along the same branch from the cut premise toward `w`. At the first rule where the positions separate, the two distinct premise positions have one parent.
3. `Premise.equal_parent_or_lower` forces that parent to be the lower position of a contraction of the cut formula.
4. This contraction is tied to the cut and properly contains `w`; reducibility therefore makes it blocked.
5. A frame for that blocked contraction's premise, applied to the descendant contraction `w`, yields equality of the two selected origins by `EntryFrame.unique_origins`, a contradiction.

Each displayed blocked-pattern frame appears compatible with this argument: binary rules separate selected copies into different premises; a logical introduction gives no whole-formula predecessor to the newly formed compound. The actual `disjLLast` exchanges must be included. The production proof must supply the frames, selected-origin memberships, typed path decomposition, and first-separation argument.

This route has not been checked by Lean in this review. If a candidate frame or uniqueness statement fails, exhibit the precise failure and pursue the unchanged full target by another criterion. Do not promote an auxiliary proof plan into an assumption of the theorem.

### B2. The repaired right candidate needs a bound below the blocked contraction

**Anchors:** `CODEX_NEXT_SESSION.txt`, lines 29–37; [BlockedR.disjunction, line 48](https://github.com/flengyel/Dosen-Petric-Maximality/blob/05c6bc8a86126fde494a9c9f2b42e693687b76d6/DosenPetric/GentzenBlockedPatterns.lean#L48).

Let `n = gs.length`, `C = A ∨ B`, `X = gaps gs`, `Y = Θ`, and `I = X ++ C :: Y`. The proposed construction starts with `innerR`, whose output is `I ++ [A,B]`. Exchange this to `[A,B] ++ I`, introduce `C` at the head, apply the existing blocked binary contraction with gaps `[[],X]` and tail `Y`, then exchange the retained `C` across `Y`.

For a construction using these two explicit exchanges, the selected rank calculation predicts:

| Position or stage | Rank |
| --- | ---: |
| Retained position in innerR | L |
| Surviving position after inner exchange | L+1 |
| Surviving C after head disjunction introduction | L+2 |
| Lower position of blocked binary contraction | L+4 |
| Retained position after final exchange | L+5 |
| Original contraction | L+n+1 |

These are calculations for the proposed construction, not committed theorems. At `n=2`, root nonincrease would fail. That does not prevent Reducibility.

Instead, prove that every eligible contraction lies at or below `innerR` on the retained-C ancestry. The inserted middle contraction is blocked; the logical and exchange nodes are not contractions; the fresh compound has no predecessor through its introduction. With the unique-entry result and explicit routing, each remaining eligible contraction has rank at most `L`, hence less than `L+n+1`. Repeated formulas in `X,Y` must retain distinct positions.

For `n ≥ 3`, the existing terminal candidate already has strictly smaller endpoint rank. Under unique entry, `ascend_rank_le` supplies a potentially shorter argument even though the root is unblocked. This is an optional simplification, not a separate required development.

Categorical equality, path classification, and the complete eligible-descendant conclusion for the repaired candidate remain **unproved**. Severity: major for right Reducibility. Evidence: unconstructed terms and missing theorem, supplemented by the concrete rank analysis above.

### B3. Full case coverage and termination remain separate obligations

**Anchors:** report “Source correspondence” and “Remaining obligations”; continuation lines 39–45; source §11.2, pp.251–253.

The new boundary lemmas do not provide the missing mixed/logical reductions or dispatch from arbitrary reducible occurrences. They also do not compare eligibility and ranks of surrounding occurrences for the subsequent multiset argument. Failure mode: **unproved**; evidence: stated theorem domains and missing producers. Severity: major for full Reducibility and Blocked-w, respectively.

Do not use declaration counts or successful builds as evidence for these missing mathematical implications. Complete local cases as branches of the general theorems, then prove the outside-occurrence and multiset statements needed for Blocked-w.

## (C) Minor issues and mathematical-writing review

The report's actual outline is:

1. Status and governing endpoint: central question and target.
2. Preserved and combined source: reconciliation evidence.
3. Proved declarations and exact hypotheses: contributions.
4. Source correspondence: proved and missing comparisons.
5. Exact blocker and attempted repair: outstanding mathematical inferences.
6. Verification and evidence: recorded checks.
7. Remaining obligations and delivery: continuation.

This order works for a technical checkpoint report. No manuscript reorganization is recommended.

| Anchor | Issue | Rationale | Repair |
| --- | --- | --- | --- |
| Report lines 23–32 | The displayed target uses I and v without declaring I,J and v's type. | KLR §1 points 5 and 11: self-contained theorem conditions and introduced variables. | Write “for every I J : List (NormalForm P), v : G P I J, b : ProofAddress h v, and y : At I C”. |
| EntryFrames line 11 | “Before any contraction” is broader than the constructor condition. | Independent typing rationale: the condition fixes both side and formula. | Write “before any contraction of C on side s”. |
| Continuation lines 18–27 | A proposed sufficient lemma is commanded as the compulsory route. | Independent mathematical rationale: the intended theorem does not depend on a particular auxiliary criterion. | Require proving the candidate or identifying its precise failure and constructing another proof of the unchanged target. |
| Continuation line 55 onward | The superseded history dominates the active instructions. | Independent usability judgment. | Preserve history separately and link it; provide a concise active prompt. |

The report correctly distinguishes proof addresses from proof values, root entry positions from descendant positions, Reduced denotation equality from ancestry, and global injectivity from the needed unique-entry property. Its writing review missed the small undeclared-binder omission; the Lean boundary statements themselves bind those variables correctly.

The governing writing source was consulted in the [MIT-hosted KLR course report](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf), §1 points 5 and 10–14, and §4 (printed pp.2–3 and 9). The Stanford PDF request failed; no identity between the two PDF files was checked. No advice about continuation-file design is attributed to KLR.

## (D) Cross-section consistency failures

The report calls entry uniqueness a proposed sufficient lemma and its frame proof an attempted repair; the continuation makes that proof route mandatory. The corrected prompt preserves the theorem while allowing another mathematically justified route.

The historical mixed-W5 instructions are expressly superseded at continuation lines 55–56. They do not formally override the active target. Their repetition is a clarity problem, not evidence that the current instructions changed the target.

The right-W4 section already recognizes that an outer exchange is neither a blocked contraction nor rank-transparent. The new rank analysis sharpens that instruction; it does not correct a false claim in that section.

No new defect in manuscript v5 has been established by this review. The manuscript was not re-reviewed.

## (E) Acceptance conditions, non-negotiable

1. Prove both general replacement-and-all-eligible-descendant-rank theorems from the existing ReducibleL/R data, without extra caller-supplied injectivity, candidates, or rank assumptions. Failure rejects a Reducibility completion claim.
2. Resolve the relevant cut-position entry ambiguity by proved frames and path arguments, or another proved criterion. Connect the result immediately to arbitrary-address W4.
3. Handle the two-copy right case with a candidate satisfying the actual descendant quantifier. Compile the explicit failure test for the existing candidate and verify the repaired candidate's equality, cut-freeness, routing, and rank bound.
4. Integrate remaining primitive/macro and mixed/logical cases into the full producers. Do not replace the producers by another classification theorem.
5. Run the repository's required checks on the changed code, apply both author-side reviews, and preserve checked/committed identity and delivery requirements.
6. Before claiming Blocked-w, prove the surrounding-occurrence transport and finite well-founded multiset induction. Before claiming complete formalization, finish the subsequent cut-elimination, coherence, and maximality endpoints.

## (F) Not checked / uncertainty log

The four supplied files match the content fetched from commit 05c6bc8: the main report, hostile report, writing report, and continuation. Twenty downloaded Lean source files match the checkpoint's CHECKED_SOURCES.sha256 inventory. The two example modules were additionally read directly from that commit.

The recorded final command receipts report exit 0 for the strict build, both boundary scripts, manuscript checksum check, and whitespace checks. The two negative-control records report the five expected rejections. The public API inventory contains the reported 75 queries. This review did not rerun those commands, recount all 8,602 declarations, replay the kernel, inspect the entire archive, check live remote/WSL state, or verify Windows Downloads.

No production files or manuscripts were modified, and no repository commit or push was made. This review and its accompanying continuation are separate deliverables; the WSL continuation retains the requirement to save future reports in the repository and Downloads.

Strongest confirmed blocker: neither full Reducibility theorem is proved; addressed left W4 still requires an extra hypothesis, and the existing right candidate cannot meet the strict target in the specified two-copy root case.

Strongest suspected, unconfirmed blocker: a remaining primitive/macro case may require a different argument than the sufficient criteria currently developed. No counterexample to the full existential theorem was found.

Most important unchecked item: Lean verification of the proposed entry proof and repaired right-W4 construction. The noncompletion finding does not depend on unavailable material.

Final recommendation: **reject a Reducibility completion claim; continue from this checkpoint toward the unchanged full target.** Confidence: High on existing theorem scope and the source-derived candidate failure; Medium on the proposed unformalized proof routes.
