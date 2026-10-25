# Review of Gentzen Reducibility checkpoint 1e967bcb

Reviewed commit: `1e967bcb913a74ae590dde940f246acaddce1fba`.
Date: October 25, 2026.
This is an AI-assisted author-side audit, not independent certification.

The previous entry-uniqueness and W4 proof obligations are discharged for the stated local families. Both general Reducibility Lemmata remain unproved. The next work must connect arbitrary reducible occurrences to the constructed replacements, complete the logical cases, and include the native right-W4 case with one parametric copy.

## (A) Kill-shots / hard blockers

**A1. The general replacement theorems are still absent.**
Anchor: follow-up report, “Status and unchanged target” and “Precise remaining inference”; [GentzenReducibilityMixed.lean, line 12](https://github.com/flengyel/Dosen-Petric-Maximality/blob/1e967bcb913a74ae590dde940f246acaddce1fba/DosenPetric/GentzenReducibilityMixed.lean#L12), and its right counterpart at line 33.

The implemented mixed theorems take an address to a constructed `oldL/oldR p q f g`. They do not extract `p,q` from every arbitrary contraction over mix. The W4 theorems likewise retain their specified input shapes and arity bounds. Failure mode: **unproved** for full Reducibility. Evidence: exact theorem types and the report's explicit remaining-case ledger. Severity: major for completion; repairable by missing constructions and coverage proofs. This is not a false completion claim in the report.

The following previous blockers are resolved:

| Previous obligation | Committed result and anchor | Assessment |
| --- | --- | --- |
| First separation and all blocked-premise frames | GentzenEntrySeparation.lean:85,111; GentzenBlockedEntryFrames.lean:13,29 | Actual typed paths and rule frames, including disjLLast exchanges. |
| Unique cut entry from reducibility | [GentzenBlockedEntryFrames.lean:45](https://github.com/flengyel/Dosen-Petric-Maximality/blob/1e967bcb913a74ae590dde940f246acaddce1fba/DosenPetric/GentzenBlockedEntryFrames.lean#L45), :51 | No global injectivity assumption. |
| Addressed terminal-left W4 | [GentzenReducibilityLogical.lean:37](https://github.com/flengyel/Dosen-Petric-Maximality/blob/1e967bcb913a74ae590dde940f246acaddce1fba/DosenPetric/GentzenReducibilityLogical.lean#L37) | Cut-freeness, local/rebuilt equality and all eligible descendants from local data and ReducibleL. |
| Failed terminal-right candidate test | GentzenRightLogicalRegression.lean:34,43,52,56 | The previous source-derived example is now a Lean theorem. |
| Repaired addressed right W4 | [GentzenReducibilityRightLogical.lean:14](https://github.com/flengyel/Dosen-Petric-Maximality/blob/1e967bcb913a74ae590dde940f246acaddce1fba/DosenPetric/GentzenReducibilityRightLogical.lean#L14) | The structural bound is constructed internally; no caller-supplied bound or injectivity. |
| Constructed mixed W5, both sides | GentzenReducibilityMixed.lean:12,33 | Complete descendant quantifiers, including surviving eligible descendants and singleton premise selections. |

The entry proof uses a separating tied contraction, its proper containment, reducibility's blockedness condition, and `unique_origins`. No circular use of the full Reducibility theorem was found. The repaired right W4 counts the two exchanges and proves retained root rank `L+5`; its structural argument bounds eligible contractions by `L`. Thus it does not rely on the false root-nonincreasing criterion.

## (B) Major weaknesses

### B1. A native right-W4 case with one parametric copy needs coverage

**Anchors:** GentzenReducibilityRightLogical.lean:10 requires `2 ≤ d.gs.length`; [GentzenReducibilityObstructions.lean:32](https://github.com/flengyel/Dosen-Petric-Maximality/blob/1e967bcb913a74ae590dde940f246acaddce1fba/DosenPetric/GentzenReducibilityObstructions.lean#L32) gives the prefix restriction for blocked right contractions.

Here `d.gs.length` counts the parametric copies. The fresh compound is an additional selected occurrence.

| Case | Parametric copies | Fresh compound | Total selected by outer contraction |
| --- | ---: | ---: | ---: |
| Existing minimum W4 theorem and regression | 2 | 1 | 3 |
| Additional native terminal case | 1 | 1 | 2 |

For explicit data, take `C : NormalForm Empty := .disj .bot .bot` and form:
```lean
f := BlockedExamples.r [C, .bot, .bot]
-- f : G Empty [.bot] [C, .bot, .bot]

t := G.disjR [.bot] [C] [] .bot .bot f
-- t : G Empty [.bot] [C, C]

w := G.contractR [.bot] C [[], []] [] (Nat.le_refl 2) t
-- w : G Empty [.bot] [C]

other := BlockedExamples.l [C]
-- other : G Empty [C] [.top]
```

The premises are cut-free. The root of `w` is a tied contraction, and it has no proper containing contraction. Its contracted-disjunction prefix is `some 1`, so the necessary blockedness condition excludes `BlockedR w`. Therefore it satisfies `ReducibleR w other ProofAddress.root (.here C [])` by the same argument as the committed regression, with prefix length one rather than two.

This is a source-derived coverage example, **not a newly compiled theorem**. It is not a counterexample to the existing addressed theorem or to Reducibility. Failure mode: **unproved coverage** for any complete right-W4 dispatch claim. Evidence: explicit well-typed construction and the current arity hypothesis. Severity: major for a complete producer, not a defect in the stated local theorem.

If `S` is the retained C-rank in `f`, the original contraction's rank is `S+3`: the surviving C gains one at disjunction introduction, the fresh C has rank one, and the binary contraction adds one. A singleton-aware inner operation has rank `S`, with no contraction node. Consequently the existing formula `old = L+n+1`, derived with an actual inner contraction, must not be extended blindly to this singleton case. Construct and prove the replacement using the new singleton-aware operations or another valid argument.

### B2. Positional extraction still needs actual input and endpoint comparisons

**Anchors:** GentzenSelectedExtraction.lean:35; GentzenChainedSelection.lean:53,126; GentzenReducibilityMixed.lean:14,35.

The extraction theorem yields an existential lower context and a selection with the prescribed ordered positions. The extensionality theorem `ext_selected` compares selections with the same upper and lower contexts. It does not itself prove that the lower context obtained by extraction equals the lower context of the input contraction.

For an arbitrary contraction over `G.mix f g`, split its selected positions according to the two actual premises. Prove the order and nonemptiness facts needed for each branch, extract its selections internally, and then prove the lower-context equality, retained-position equality, and actual old-proof comparison. Use a one-premise construction when a selected branch is empty and the new mixed construction when both branches are nonempty. Respect the repository's order: for `f : G P U Δ` and `g : G P F Λ`, mix concludes `F++U ⊢ Λ++Δ`.

Failure mode: **unproved**; evidence: the constructed inputs required by the addressed theorems. Severity: major for general dispatch. This is an appropriate integration target while constructing W6; it should not become another independent catalogue.

### B3. W6 is relevant, but its smallest source-macro cases are blocked

**Anchors:** report's W6 construction; GentzenBlockedPatterns.lean:26–34; GentzenChainedSelection.lean:53–85. Source: Došen–Petrić, September 2007, §11.2, printed p.252, [W6](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).

For `C = disj A B`, nonempty selections
`p : ContractionSelection C Γ K`, `q : ContractionSelection C Θ L`,
and premises `f : G P (Γ++[A]) Δ`, `g : G P (Θ++[B]) Λ`, the report's
`s := (p.chain q).chain (.last [])`
has the intended final antecedent `(p.erased++q.erased)++[C]`. It selects the parametric copies from both premises and the fresh terminal C.

When both premise selections are singletons, write their contexts as `X++C::Y` and `Z++C::T`. The three selected positions are precisely the source-macro `BlockedL.disjunctionBoth` pattern, with gaps `[X,Y++Z,T]` and empty tail. Fresh C plus one parametric singleton in only one premise gives `disjunctionFirst` or `disjunctionSecond`. These identifications need explicit transports and positional equalities in Lean. They exclude reducibility in those source-macro cases; they are not examples of unresolved reducible occurrences.

The exclusions do not automatically apply to primitive `disjL`. Its explicit syntax and ancestry differ from `disjLLast`; the existing freshBoth example already demonstrates this distinction.

For the remaining W6 cases, include singleton selections without artificial contraction nodes, independent premise arities, repeated equal formulas at fixed positions, the actual source-macro exchanges, both sides, and the complete eligible-descendant bound. The new `ContractionBound` can handle binary branches abstractly, but its concrete rule instances and categorical equations must still be proved.

Failure mode: **unproved** for W6 and its general dispatch. Evidence: the future construction and missing producer. Severity: major for full Reducibility. The W6 proposal is on target; completing only its constructed family would leave the coverage gap.

## (C) Minor issues and writing review

The follow-up report's actual outline is: status/target; baseline/preservation; proved declarations; source correspondence; remaining inference/W6; verification; reviews/delivery. It puts hypotheses and mathematical scope before counts. No reorganization is needed.

| Location | Issue | Repair |
| --- | --- | --- |
| GentzenReducibilityRightLogical.lean:12 | “Including the two-copy case” does not say whether the fresh compound is counted. | “Including two parametric copies.” State separately that the outer contraction selects one additional fresh compound. |
| Summaries of W4 completion | The theorem's `n≥2` local-family restriction can disappear in compressed prose. | State “the addressed W4 families with at least two parametric copies”; add the native one-parametric case to dispatch coverage. |
| Next instructions | W6 construction and matching arbitrary inputs are separate proof obligations. | Require actual selected-position/context/proof comparisons when integrating each branch. |

The earlier report's undeclared I,J,v binders are corrected. EntryFrame's comment now fixes both formula and side. No additional false theorem claim was found in the scoped follow-up report.

The editorial principles used are explicit theorem conditions and consistent notation, from KLR's [Mathematical Writing course report](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf), §1 points 5 and 11–14, with the definition-placement qualification in §4. The counting distinction and dispatch requirements are mathematical judgments, not rules attributed to KLR.

## (D) Cross-section consistency failures

The report and current continuation consistently retain both full Reducibility Lemmata as open. They correctly archive the older continuation rather than issuing it as a competing task.

The supplied historical report continues to describe the earlier checkpoint; it must not be used to reinstate the now-resolved entry and stated W4 blockers. Conversely, the new W4 results do not imply all native W4 inputs have been covered. The theorem table correctly states the arity restriction; the newly identified case should be added to the remaining ledger.

No manuscript defect follows from these unfinished formalization steps. Manuscripts v4/v5 were not reviewed here.

## (E) Acceptance conditions, non-negotiable

1. Retain the proved entry, W4, and constructed mixed-W5 results; do not repeat their proofs or audits without a changed dependency or identified defect.
2. Compile the one-parametric native right-W4 example and cover its arbitrary-address replacement, or prove its inclusion in another implemented reducer.
3. Extract premise selections and establish actual input comparisons internally for arbitrary mix contractions, with both variances.
4. Complete W6 and logical W5 with source/native distinctions, blocked base cases, singleton branches, and every eligible descendant.
5. Complete the remaining W1 configurations and general dispatch, producing both full Reducibility theorems without additional caller assumptions.
6. Prove outside-occurrence/containing-blockedness transport and finite multiset descent before claiming Blocked-w. Subsequent cut elimination and coherence remain separate conclusions.

Failure of conditions 2–5 rejects full Reducibility completion; failure of condition 6 rejects Blocked-w, without invalidating the local theorems already proved.

## (F) Not checked / uncertainty log

All five supplied files match their corresponding contents at commit 1e967bcb. All 27 downloaded added/changed Gentzen source modules match the committed checked-source inventory. The final command receipts report success for the strict build, both boundary scripts, manuscript checksums and whitespace checks; the negative-control receipt records five expected rejections.

This review inspected the entry, W4, mixed-W5, extraction and continuation arguments. It did not run Lean, replay an independent kernel, recount the entire audit, inspect all raw exploratory logs, access the live WSL working tree or verify Windows delivery. The one-parametric example and source-macro singleton exclusions are source-derived deductions to formalize, not newly executed Lean results.

Strongest confirmed blocker: general input-to-replacement coverage remains unproved, including the explicitly identified native one-parametric right-W4 case.

Strongest suspected unconfirmed blocker: another raw-syntax or exchange configuration may require a distinct ancestry argument. No counterexample to either full Reducibility Lemma was found.

Most important unchecked item: the complete case analysis and its Lean verification. The scope findings do not depend on unavailable material.

Recommendation: **reject a full Reducibility completion claim; continue the unchanged task using the resolved entry and local reduction results.** Confidence: High on current theorem scopes and the identified coverage distinction; Medium on unimplemented general proof routes.
