# Blocked-w and finite eligible-site descent

Both containing-shape theorems, complete eligible-site correspondence, exact
rank-multiset replacement and **actual Blocked-w** compile. The same cut formula
and contexts have cut-free representatives whose cut denotation is equal in
Reduced and whose tied contractions are blocked on both sides. This is the
source §11.2 printed p.253 corollary, with the existing constants/atomic-zero
syntax retained. Simultaneous atomization and blockedness remains open; a
counterexample to using the existing atomizer is proved below.

## Baseline and exact endpoint

Started with clean main at 5b8a1996cab3f53e8c771dbd6126274236b1db4a. SSH fetch and
fast-forward incorporated 85a16cdc077e8a3c4deedd3b7a521361e1e54e54. Stash
dedfd8fc8cd49930e9a162d5be585215b062a43c is preserved. No reset, clean,
force push, stash deletion, manuscript edit or repository-visibility operation
was used. Lean 4.35.0 and the Init-only dependency closure are unchanged.
The existing full Reducibility construction and outside-address transport are
reused; no unchanged-baseline rebuild was performed merely to begin the task.

For arbitrary P : Type u, C : NormalForm P and all contexts, blocked_w takes
f : G P Γ (C::Δ), g : G P (C::Θ) Λ and G.Topmost f g. It constructs f',g'
at those same sequents with Topmost, equality
ofTerm (G.cut f' g').denote = ofTerm (G.cut f g).denote, and the clauses:

```lean
∀ {U V} {w : G P U V} (a : ProofAddress g' w) (x : At U C),
  g'.TiedRight (a.traceAt .left x) → BlockedL w
∀ {U V} {w : G P U V} (a : ProofAddress f' w) (x : At V C),
  f'.TiedLeft (a.traceAt .right x) → BlockedR w
```

blocked_w_premises supplies stronger separate denotation equalities.
No Nonempty P, DecidableEq P, Atomized premise, caller reduct, rank bound,
normal form, coherence or equality-reflection hypothesis is added. The original
G syntax, equations, rho, Blocked/Reducible and Reduces definitions are unchanged.

## Dependency and occurrence correspondence

All Gentzen names below are under DosenPetric.Reduced.Gentzen.

| Declaration | Constructed content |
| --- | --- |
| BlockedL/R.replace_lower | All fourteen blocked envelopes; arbitrary D and replacement at a proper same-side lower contraction. Reindexing is node-free; disjLLast exchanges remain nodes. |
| ProofSpine/ProofAddress.compare, suffix_of_prefix, split_prefix | Actual typed decomposition, rather than a raw path comparison alone. |
| ProofAddress.containing, replace_lower_iff | Actual rebuilt ancestor, unchanged ascent and lower output position. |
| ReducibleL/R.blocked_containing | A new strict containing tied contraction remains blocked. |
| ReducibleL/R.outside_iff | Full eligibility equivalence at corresponding preserved occurrences. Common containing ancestors use the shape theorem; unaffected ancestors use forward/inverse outside transport. |
| ReducibleL/R.new_site, outside_or_same | Every new site is inside the repair, including its root, or is an old incomparable site; no old proper descendant or distinct eligible ancestor survives as an extra old site. |
| G.occurrences, finiteOccurrences | Complete finite dependent occurrence records. Only duplicate whole records are removed; distinct branch paths with equal proof values stay distinct. |
| EligibleEnumeration, EligibleSites.left/right | One path/rank key per actual eligible occurrence. The lower output position is uniquely determined by the contraction indices. Formula labels are not used as occurrence identifiers. |
| ReducibleL/R.rank_replacement | Old ranks permute to r::O and new ranks to I++O, with every I entry smaller than r. |
| DosenPetric.FiniteRank.descent_wf | Fixed-support multiplicity vectors, ordered from highest rank down; fixed-length product lexicographic well-foundedness. |
| exists_reducible_left/right, blocked_left/right_of_no_reducible | Strong induction on address depth finds an eligible unblocked ancestor; absence of eligible sites implies the required blocked normal form. |
| blocked_normalization_left/right, blocked_w_premises, blocked_w | Well-founded induction constructs actual witnesses. Successive premise normalization preserves the first side's property because its typed cluster depends on its own premise and cut-entry position. |

The list representation retains equal-rank multiplicity. Descent neither
assumes a smaller maximum nor a smaller rank sum, contraction count or proof
size. One support bound N is chosen above the starting ranks and preserved
throughout accessibility. The proof does not order variable-length vectors
lexicographically. Classical choice is used only within the permitted foundation
policy; no variable-label decision instance is required.

## Atomization obstruction and next exact obligation

AtomizationBlockedBoundary.before : G Empty [top, disj top bot] [top] is a
compound thinning above a top thinning and topI. It is cut-free and AllBlockedL;
it has no left contraction. G.atomize before is cut-free, atomized and equal
in Reduced, but its occurrence at [0,0,0,0] is a tied left contraction on top.
The immediate premise of that contraction is native disjL. BlockedL.premise_kind
excludes that kind, proving it unblocked. The theorem
cutFree_equal_atomized packages these facts; atomize_not_blocked states the
failed preservation implication directly.

This refutes the construction that applies this atomizer after Blocked-w.
It does not refute simultaneous clean-cut existence or identify a manuscript
defect. The next required statement is: for every original topmost f,g,
construct f',g' at the same sequents with both Atomized, Topmost, Reduced cut
equality and AllBlockedR f' / AllBlockedL g'. The current continuation gives a
concrete proposed economical-route construction with atomic unused slots.
That construction and its full descendant-bound laws remain unproved.
Alternating the two existence theorems supplies no terminating combined procedure.

Clean-cut normalization, cut elimination with constants/atomic zeros,
restricted mix/positive coherence, Reduced.Faithful, Boolean Coherence,
actual-presentation instances/maximality, the short q/e route, model corollary
and remaining appendix claims remain open. Milestones I–III and whole-paper
completion remain distinct. The preserved symmetric-fold alternative and
tagged-block/ordinal correspondence requirements remain active.

## Boundary examples and verification

GentzenBlockedChecks.all_fourteen_paths computes actual lower-contraction paths
for all fourteen inhabited envelopes over Empty, with a lower contraction at
every free-premise root. Identical mix siblings occupy different paths.
nested_empty_exchange_paths counts actual empty exchanges. common_eligible and
common_preserved test two eligible identical subproofs in different branches
beneath one blocked ancestor, including arbitrary signed literals.
multiset_boundaries tests zero, one and several inserted smaller ranks with
several unchanged equal maximal ranks. Existing regressions and both unrestricted
Reducibility signatures are preserved. The inserted repair root is included in
new_site and the complete Reduces descendant bound.

Final local checks cover **412 Lean files and 10,906 audited project
declarations**, including generated helpers; 428 checked source/configuration/
manuscript files are inventoried. Thirteen new public modules and one public-type
check are added. All regular files have module headers and stay below 10,000 lines.

| Command | Exit | Seconds |
| --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 6.489 |
| `python3 scripts/check-audit-boundaries.py` | 0 | 8.361 |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.028 |
| `sha256sum -c SHA256SUMS` | 0 | 0.036 |
| `git diff --check` | 0 | 0.019 |
| `lake env lean -DwarningAsError=true Checks/BlockedW.lean` | 0 | 0.626 |
| `lake env lean -DwarningAsError=true Checks/Reducibility.lean` | 0 | 0.53 |

Both boundary scripts returned zero with five expected rejected controls:
public custom axiom, unused private custom axiom, hidden dependency axiom,
identified tagged projections, and zero without an existing-arrow witness.
The strict audit permits only propext, Quot.sound and Classical.choice.
Source screening also found no production proof holes or custom mathematical
axioms. 33 nonzero exploratory receipt rows remain in COMMANDS.json,
including dependent-elimination failures, source-screening of a forbidden word
inside a comment, and an unavailable Repr instance in exploratory printing.
They are not treated as successful checks; final checks follow all proof edits.

provenance/wsl-gentzen-blocked-w retains final receipts, public types, every
archived run log with raw/compressed digests, both control reports and sources,
the complete checked-source inventory, module hashes and declaration anchors.
Repository maps, corrections, validation, README and continuation reflect the
actual checked scope. Prior continuation and README are preserved in history.

The cached September 2007 source §11.2 printed pp.248–253 was consulted,
including the Blocked-w and clean-cut paragraph on p.253. The manuscript v6
source, including both appendices, was read and left unchanged. Its v4/v5/v6
hash checks passed. Author-side hostile and KLR writing reviews accompany
this report. Independent kernel replay, Comparator, official Palomar preflight,
service verification, publication and a new whole-paper novelty judgment were
not performed.

## Retention and delivery

Retain this report at docs/GENTZEN_BLOCKED_W_REPORT.md and both new reviews
under docs/reviews/. Deliver those three committed copies and the instruction
CODEX_AFTER_5B8A199_BLOCKED_W.txt plus both GENTZEN_5B8A199 reviews to Downloads.
Preserve any differing destination and use a dated/commit suffix. The local
POST_COMMIT_DELIVERY.json receipt records actual destinations, SHA-256/byte
equality, checked-versus-committed inventory, preserved stash and agreement of
local main, origin/main and live SSH main. It supplies the containing commit
identity after commit, avoiding a self-hash cycle in this report.
