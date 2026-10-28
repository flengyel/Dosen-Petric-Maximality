# Review of 5c72a84 and the cut-elimination continuation

The reviewed source supports simultaneous clean-cut normalization and the
listed base equations. No defect in those results was confirmed. Global cut
elimination and the remaining full-paper formalization are still open.

This is an author-side review using
[HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe).
The reviewed commit is
[5c72a84c665bdc5102e546cef88f9fd29838e9b4](https://github.com/flengyel/Dosen-Petric-Maximality/commit/5c72a84c665bdc5102e546cef88f9fd29838e9b4),
whose parent is a006ecdf7ca961f5355a44ed97629f960d5605d2.
The local run was complete before this successor review began. This review
examines source and retained evidence; local Codex remains responsible for builds.

## A. Kill-shots / hard blockers

**No confirmed hard blocker in the claimed clean-cut milestone.** At
GentzenCleanCuts.lean:14, the same f', g' satisfy the original sequent types,
Topmost, both Atomized predicates, individual Reduced equalities and both
AllBlocked conditions. At line 31 the cut-equality statement expands the full
universal addressed clauses. Checks/CleanCuts.lean ascribes the expanded public
types; its retained successful log agrees with the source. No extra coherence,
Nonempty P, DecidableEq P, supplied reduct or normalization hypothesis appears.

The old negative atomizer example and CleanCutChecks.boundary_clean are compatible:
one particular procedure fails to preserve blockedness, while simultaneous
representatives exist by a different construction. The former file is unchanged
from the parent. Nothing here establishes an error in manuscript v6.

## B. Major weaknesses and successor proof obligations

**Global elimination remains unproved, as the report states.** Anchors:
GentzenCutBase.lean, GentzenCutConstants.lean, GentzenCutThinning.lean and the
report's final obligation. These prove particular equations, not exhaustive
rank-two classification, all principal/parametric/blocked reductions or their
well-founded assembly. Severity: a blocker to full-paper formalization
certification, not a defect in the completed local theorem. Repair: construct
the unrestricted same-sequent CutFree representative with equal Reduced
denotation, then continue the established coherence and full-paper dependency chain.

Two inference risks must be controlled in that construction:

| Anchor and claim tested | Evidence and failure mode | Required repair |
| --- | --- | --- |
| GentzenCleanCuts.lean:14,31; reuse inside a same-degree rank step | Neither statement bounds the ranks of the new witnesses. A decrease before re-cleaning does not establish a decrease afterwards. This is a limitation of the available theorem, not a failed new proof. | Separate outer degree induction from inner clean-cut rank induction. Prove cleanliness of unchanged-degree recursive subcuts; use unrestricted normalization only where its rank is unrestricted. |
| PositiveGentzenSyntax.lean:32–33 and GentzenClusterRank.lean:40–65; moving a selected position to the head | Native cut selects heads. rho counts actual trace nodes, including exchange nodes. The source's positional decrease does not automatically transfer to the routed native premises. | Derive a positional cut interface and measure the original selected premises, proving its equations and head specialization; alternatively prove sufficient native adapter bounds. Do not change rho or erase existing exchange nodes from its count. |

The successor proposes a positional interface as a construction target, not an
existing Lean declaration. Its recursive measure must be explicitly distinguished
from cutRank of the routed native premises. The existing G syntax and equations
remain fixed.

A further nested-cut obligation has a concrete approach. After eliminating
the inner cut(s) in a principal blocked family, build a fresh principal logical
conclusion. Its selected cluster has no predecessors and rank one independently
of the internal normal form's size. This can justify the next same-formula cut
without assuming rank-nonincreasing normalization. The actual native constructor,
cleanliness and total-rank inequality must be proved. Source terminal wrappers
such as disjLLast include exchanges and cannot simply be assigned rank one.

## C. Minor issues and confirmed source corrections

The current continuation still described the preceding six deliveries as
scheduled. The author has now reported those committed-byte deliveries complete.
The successor records that completion and separately identifies its own three
pending Downloads copies. This is a status correction, not independent cloud
verification of WSL files.

Two typographical errors were confirmed in the rendered primary source,
Došen–Petrić, *Proof-Theoretical Coherence*, September 2007:

| Printed anchor | Correction | Independent mathematical check |
| --- | --- | --- |
| p.260, (w gamma 3), rank comparison below the displayed reduction | Reverse the printed inequality to r' < r. | The recursive selected occurrence is a strict predecessor of the old selected cluster; the other premise is unchanged. Actual adapter contributions must be accounted for in Lean. |
| p.262, continuation of (w disjunction 1), final outer cut | Read “rank is 1” as right rank one. | Each side has positive rho, so total rank is at least two. The new principal occurrence is a leaf; the analogous p.261 passage explicitly identifies the right rank. |

Primary [PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Printed p.260 and p.262 are one-based PDF pages 272 and 274. Both pages and the
intervening argument were visually checked from that downloaded file.
These are errors in the cited source's wording, not counterexamples to its
theorem or newly established errors in v6. After this review, the author explicitly
requested their inclusion in the arXiv paper. The successor therefore supplies
an Appendix C addition for the next manuscript version, with the existing v6
source/PDF pair preserved. Record the addition and the exact Lean correspondence
obligations in the external ledger. Local Codex must build and inspect it.

## D. Cross-section and proof-dependency checks

| Reviewed component | Finding |
| --- | --- |
| AtomicPrograms and EconomicalRoutes | AtomicOmissions quantifies over individual typed tags. The route program recurses on the lower context, selects the whole nonempty fiber, treats singletons without a contraction node, and thins only an unsupported atomic head. |
| ResidualSupport and InputRouteSupport | fixedAt and the two-way preimage lemma justify residual support. Exchange and contraction surjectivity, and the actual inserted thinning position, supply the hypotheses internally. Equal labels do not identify distinct tags. |
| ParameterizedRouteRepair | CutFree, Atomized, categorical equality and the descendant bound refer to the same chosen tail program and repair. Component extensionality is the proved product/coproduct property, not Boolean coherence or occurrence-relation reflection. |
| All strengthened input dispatch and leaf modules | Every actual input case is covered, including opposite rules, binary one/two-premise regimes, selected logical singletons, right HEAD-disjunction and terminal-source W6. CutFree excludes cut input; basis impossibility is internal. |
| ChosenRankReplacement and AtomizedBlockedNormalization | The actual chosen h and its complete bound enter the old/new multiset decomposition. Multiplicity, inserted-root coverage and outside correspondence are reused. Replacement preserves Atomized throughout descent. |
| CleanCuts | Initial atomization precedes the invariant-preserving normalization. Both premises retain individual equalities. Each AllBlocked condition depends only on its own premise, allowing successive normalization. |
| CutBase, CutConstants and CutThinning | Identity/zero, fresh-thinning and constant equations are in Reduced. Same-sequent repairs and empty-list transports are explicit. No faithfulness premise or unwitnessed zero is introduced. |
| CleanCutChecks | Includes compound identity, repeated fibers, omitted atomic positions, constants over Empty, signed literals, equal-labelled swaps and the negative unsupported compound tag, plus a positive simultaneous representative for the old counterexample. |
| Active records | The proved endpoint, remaining global theorem, three milestones and further full-paper endpoint agree. The later author-requested errata appendix is an explicit addition to the manuscript task. |

The parent-tree comparison shows that old Lean files changed only in the public
imports, appended axiom-print checks, and the already-requested comment typo in
GentzenFiniteOccurrences.lean:100. No previous proof body was replaced. All
seven manuscript-directory blobs and the original atomizer counterexample retain
their parent blob identities.

## E. Acceptance conditions for the continuation

1. Preserve the complete existing theorem signatures and same-witness bounds.
2. Prove selected-position transport and cleanliness inheritance before relying
   on them in recursive calls; keep actual exchange and contraction conventions.
3. Exhaust minimal-rank cases, both principal reductions, all parametric cases
   and all seven blocked families on each side with exact sequents and equations.
4. Distinguish smaller-degree calls from same-degree smaller-rank calls.
   For sequential blocked cuts, prove the fresh-principal rank calculation.
5. Export unrestricted topmost and global elimination without a caller eliminator,
   coherence premise or conclusion-shaped assumption. Continue the full contract.
6. Check exact signatures, public dependency closure, allowed axioms, all five
   existing controls and committed-source identity; update the claim ledger.
7. Retain reviews and verify the new Downloads copies locally, keeping delivery
   and registry/publication statuses separate.

These are mathematical and verification requirements within the authorized
task, not a new author-approval condition.

## F. Not checked / uncertainty log

Read all 29 added production modules, Checks/CleanCuts.lean, the modified source
patches, relevant old syntax/classification/rank/blocked/routing interfaces,
current instructions and status records, report and local reviews. Read the
relevant primary-source passages at printed pp.249, 253–262, 272–273 and 291–292.
The old multiset well-foundedness and earlier transport proofs were reused from
their prior reviews rather than independently reproved in full.

Independent cloud checks verified 65 fetched UTF-8 Git blobs against their tree
identities, and 43 inventoried source files against the retained SHA-256 list.
Eight selected compressed logs were checked against their compressed and
uncompressed digests and Git blobs. Their contents include the final strict
run, three exact-signature runs, both boundary scripts, manuscript checks and
whitespace check.

The retained final log records Lean 4.35.0, 442 screened Lean files and 11,105
audited project declarations, no errors/warnings, allowed axiom dependencies,
and successful build/audit. The type logs agree with the full public statements.
The boundary records show all five deliberate controls rejected. The inventory
has 458 entries; COMMANDS.json has 62 entries, of which 25 exit nonzero, and
LOG_ARCHIVES.json lists 62 retained logs. Those failed attempts are not silently
reported as successful final checks.

This review does not independently rebuild Lean, replay a kernel, download and
hash all 458 inventoried files, or inspect WSL's checkout, stash, live SSH refs
or Downloads. The author's completion report supplies the latter status.
No Comparator, official preflight, service verification or publication is claimed.
The repository remains private. No new complete manuscript or rendered-v6 review
was performed; the reviewed manuscript is unchanged. The author-requested
appendix is supplied as exact TeX in the handoff, pending local insertion,
build and rendered review.

Strongest confirmed blocker to full-paper formalization: global cut elimination
and subsequent coherence/presentation obligations remain open. Strongest suspected
but unconfirmed defect in the claimed clean-cut theorem: none identified.
Most important unchecked result: the proposed positional degree/rank induction,
especially its blocked-family equations. Recommendation: the evidence supports
the reported local milestone; full-paper formalization remains incomplete.
This scoped result does not reopen the separate manuscript submission-readiness
assessment; the new appendix requires its own local source/PDF verification.

Retain this review in the repository. Its Downloads delivery is pending local
Codex access and must be certified from committed bytes, together with the
successor instruction and writing review.
