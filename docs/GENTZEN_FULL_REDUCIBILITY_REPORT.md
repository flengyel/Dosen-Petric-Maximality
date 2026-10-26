# Full Gentzen Reducibility and outside-site transport

Both full `DosenPetric.Reduced.Gentzen.reducibility_left` and
`reducibility_right` compile with the unchanged `ReducesL/R` definitions.
The two terminal-source one-premise W6 families, unrestricted exchange reducers,
and every remaining unary input are implemented. Work continued to typed
outside-site transport for all incomparable addresses. The full manuscript
contract remains incomplete: containing-blocked transport, multiset descent,
Blocked-w, cut elimination, coherence and the final paper instances are open.
This is a local, author-side implementation/verification report, not independent
kernel verification, peer review or Palomar acceptance.

## Baseline and preserved work

Started from clean main at b2ab0a89bddc396dc7b6c0a4ccc30be08d4a088e;
fetched SSH origin and fast-forwarded the documentation-only successor
434aa77751d25020d8a98e0815167ccae61ba101. The unchanged baseline's retained
strict evidence reports 330 screened Lean files and 9,737 audited declarations
in `provenance/wsl-gentzen-reducibility-integration/`. The successor explicitly
requires reusing this verification rather than repeating an unchanged baseline.
The stash dedfd8fc8cd49930e9a162d5be585215b062a43c is preserved. No reset,
clean, force push or stash deletion is used. No manuscript or old production
module is changed. Toolchain: Lean 4.35.0; active dependencies: Init only.
The repository remains private; no publication/service operation is performed.

## Exact principal endpoints and hypotheses

For arbitrary `P : Type u`, `C : NormalForm P` and all displayed contexts:

```lean
(f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ)
(w : G P U V) (x : At U C) : ReducesL f g w x

(f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ)
(w : G P U V) (x : At V C) : ReducesR f g w x
```

The declarations are in `DosenPetric/GentzenReducibility.lean`. `ReducesL`
quantifies over every `a : ProofAddress g w`. Given the existing
`ReducibleL f g a x`, it constructs a cut-free `h : G P U V` with equal Reduced
denotation. For **every** `b : ProofAddress h v` and typed position `y`, if the
corresponding inserted address is reducible relative to the rebuilt cut,
`v.rho .left y < w.rho .left x`. The right theorem is independently typed with
addresses in f and succedent positions. Its strict bound is on `.right`.
Topmost cut-freeness, tiedness, unblockedness and blocked proper containing
contractions are premises inside `ReducibleL/R`; they have not been removed.
There is no Binary/Unary restriction, caller reduct, selection decomposition,
rank/coherence/injectivity premise, `Nonempty P`, `DecidableEq P`, enumeration,
freshness or formula-disequality hypothesis. Existing `LowerContraction`
recovers the actual outer constructor and its position. `AllInputReducer`
dispatches internally over the actual input syntax. These existential results
supply neither a quotient-level proof transformation nor rank invariance under
Reduced equality. `Atomized` preservation is not a field of `ReducesL/R` and
is not asserted for the general routing repair.

## Proved declarations and constructor coverage

All names in this table are under `DosenPetric.Reduced.Gentzen`.
`MODULES.tsv` and `DECLARATION_ANCHORS.tsv` retain all new source anchors;
those are inventories, not counts of mathematical theorems.

| Declarations | Exact scope |
| --- | --- |
| `W6.TerminalOne.oldFirst/Second`, `repairFirst/Second`, `denoteFirst/Second`, `old_rankFirst/Second`, `repair_rankFirst/Second`, `reducesFirst/Second` | Both source-terminal one-premise W6 families, arbitrary nonempty parametric arity, source macros and all containing addresses. |
| `UnrestrictedExchange.factor`, `square`, `selected_perm`, `old_rankL/R`, `left/right` | Arbitrary block exchange and actual contraction selection, with constructed exit exchanges and complete tagged component square. |
| `Route.program`, `program_get`, `program_arrow`, `anchored_factor`; `ContractionSelection.factor_route` | Syntactic realization and selected-fiber factorization of typed routes, using existing Gentzen rules only. |
| `RoutingInputReducer.left/right` | All same-side exchange, thinning and nested contraction placements, including shared/interleaved/disjoint selections. |
| `OppositeUnaryReducer.left/right` | The four opposite-side unary families on each side. |
| `FixedLogicalReducer.left/right` | Unary logical principal formula is fixed, even if its label equals the contracted formula. |
| `SelectedLogicalReducer.left/right` | Unary logical principal formula is selected; arbitrary position, including one parametric copy. |
| `LogicalInputReducer.left/right` | Internally distinguish fixed/selected principal slots with indexed positional masks. |
| `AllInputReducer.left/right`, `reducibility_left/right` | Exhaustive actual input dispatch and both full unchanged Reducibility conclusions. |
| `Premise.sibling_exists`, `ProofAddress.outside_of_incomparable`, `outside_cluster` | Outside occurrence's proof value, branch path, every typed ancestry map and cluster membership survive replacement. |
| `ReducibilityChecks.singleton_actual_repair`, `literal_left/right`, `equal_label_swap`, `crossing_factor` | Inhabited Empty-variable right-W4 regression, arbitrary signed literal repairs, equal-label transposition and crossing exchange factor. |

| Actual input schema | Left contraction | Right contraction |
| --- | --- | --- |
| identity, atomic zero, topI, botE | `not_basisL`: two distinct selected positions impossible | `not_basisR` |
| exchangeL | RoutingInputReducer / separately exported unrestricted exchange | OppositeUnaryReducer |
| exchangeR | OppositeUnaryReducer | RoutingInputReducer / unrestricted exchange |
| thinL | RoutingInputReducer, including selected thinning | OppositeUnaryReducer |
| thinR | OppositeUnaryReducer | RoutingInputReducer, including selected thinning |
| contractL | RoutingInputReducer, all selected-fiber regimes | OppositeUnaryReducer |
| contractR | OppositeUnaryReducer | RoutingInputReducer, all regimes |
| conjL | LogicalInputReducer: fixed or selected | OppositeUnaryReducer |
| disjR | OppositeUnaryReducer | LogicalInputReducer: fixed or selected |
| conjR, disjL, mix | Existing BinaryReducer | Existing BinaryReducer |
| cut | Contradicts cut-freeness already supplied by reducibility | Same |

## Source correspondence and categorical argument

Source: Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
§11.2 printed pp.248–253. Printed p.n is one-based PDF page n+12.
Verified cached PDF SHA-256:
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
The retained extraction `SOURCE_P248_P253.txt` has SHA-256 `0811ff3f3ecb636057170fc0ddad4b76736699e07e2dc68aba085c766a94e096`.
The prior rendered-page inspection and historical access records are preserved.
No new source discrepancy or manuscript defect is established.

| Source anchor | Implemented correspondence |
| --- | --- |
| pp.248–249 cluster and rank definitions | Existing whole-formula `At`, `ProofAddress`, predecessors and all-node `rho` unchanged. |
| p.250 Reducibility Lemma; p.252 right analogue | `reducibility_left/right`, exact all-address/rebuilt-eligible-descendant quantifiers. |
| p.251 W1–W3 | Opposite unary families, unrestricted exchange and the stronger derived selected-fiber route factor. The source's Semilattice Coherence invocation is replaced by proved product/coproduct component laws. |
| p.251 W4; p.252 dual | Fixed-principal naturality or selected-principal source-W4 repair, with explicit terminalizing exchange and singleton-aware inner selection. |
| pp.251–252 W5 | Existing binary producers reused, no restart. |
| p.252 W6, equations `(w ∨ 1–3)` on p.250, `(dL nat)` | Both newly packaged terminal-source one-premise families use retained-last block factorization and `Rules.terminalDisjLeft_nat`. |
| p.253 Blocked-w and cut-elimination statements | Not closed by Reducibility alone; see open dependency table below. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Existing constant and atomic-zero bases retained. No empty-sequent leaf or new zero constructor. |

For terminal-source W6 with k parametric selected copies, define δ(k)=0 for
k=1 and δ(k)=1 for k≥2. In the first family S is the sum of f's ranks at the
complete selected list embedded before [A]; in the second use g and [B].
The actual source macro gives old rank `S+3*k+3` and repaired rank
`S+δ(k)+6`. The factor 3 counts actual source macro nodes; the fresh principal
has rank 2. Both repairs are syntactically blocked. Singleton old blockedness
is reused, not inferred from denotation. Counts, CutFree, Atomized and complete
tagged relations are preserved in these source packages.

Unrestricted exchange extracts the complete before-swap selection in source
order using masks, centers the retained position, swaps the fixed remnants,
and restores the lower context. This is an alternative to the handoff's
at-most-two-exchange proposal: the derived script may contain more exchanges.
No at-most-two claim is made. The all-position square covers selected copies
and every distinct fixed tag, including equal labels. The selected lists
across the original swap are related by a proved permutation, not a false
order-preservation claim for the whole block swap. Product/coproduct universal
properties prove Reduced equality; no occurrence-equality reflection is used.
Old retained rank is `S+n+1`; the inner contraction has rank `S+1` for n≥2.
Bounds lift through exchange nodes without demanding a bound on the repaired
root. Empty exchanges still count as actual proof nodes.

The stronger unary route repair factors the exact composite selected fiber
first, then realizes remaining routing on the fixed tail below a distinguished
head. Every new tail contraction is excluded from eligibility at that head
by its proved parent map. `ContractionBound` bounds the genuine inner selected
contraction and all eligible descendants. Generic route realization can use
compound thinnings, so no blanket Atomized preservation is claimed. This is
sufficient for the exact unchanged Reducibility interfaces; later clean-cut
arguments must separately address atomization and its interaction with descent.

For fixed logical principal slots, both consumed component cases are proved
categorically. For selected slots, one actual exchange moves A,B to the source
terminal convention, and a derived exit script restores the original lower
context. With k parametric copies, old rank is `S+k+2`, moved inner rank is
`S+k+δ(k)`, and the minimal eligible bound is inner+1 ≤ old rank. The right
repair uses the **head** source-disjunction blocked form. The known terminal
right candidate remains proved unblocked; denotation equality never transfers
blockedness. Rank is not invariant under these exchanges or Reduced equality.

## Continuation after Reducibility: proved transport and exact open steps

Outside transport is established for any two actual addresses whose paths are
incomparable by prefix. `ProofSpine.apart_of_incomparable` constructs the sibling
divergence internally; no caller supplies a branch decomposition. The outside
proof itself is unchanged, so its local rank, lower-contraction status and
blockedness are unchanged. `outside_cluster` proves whole-formula membership
before/after. This does not yet prove preservation of its full Reducible
predicate: proper containing tied contractions may also have changed.

| Dependency | Typed target / predecessors | Status |
| --- | --- | --- |
| Both full local producers | `∀ f g w x, ReducesL f g w x`, independently `ReducesR` | Proved here. |
| Outside path/cluster transport | `ProofAddress.outside_of_incomparable`, `outside_cluster` | Proved here. |
| Containing blocked pattern | For `hb : BlockedL k`, `a : ProofAddress k w`, `a.path≠[]`, `hw : w.LowerContraction .left x`, `h` of w's sequent, prove `BlockedL (a.replace h)`; separately right. | Open; decompose every actual blocked envelope, including terminal macro exchange nodes. LowerContraction prevents replacing an envelope's noncontraction node. |
| Eligible-site correspondence outside replacement | Transport ReducibleL/R using outside clusters plus containing blocked preservation; account for any containing sites separately. | Open; the existing inside-descendant bound alone does not imply it. |
| Finite reducible-site enumeration and multiset decrease | Enumerate addressed lower positions without deduplication by labels; replace one rank by finitely many smaller ranks, keeping other eligible sites controlled. | Open; requires previous rows and a proved well-founded multiset order. |
| Blocked-w | For a topmost cut, construct equal-denotation cut-free premises with every tied contraction blocked. | Open; pp.252–253, uses actual finite descent. |
| Clean cuts / atomization | Combine Atomic-k with Blocked-w without assuming rank monotonicity of atomization or that generic routing preserves Atomized. | Open. |
| Cut elimination / positive coherence | Existing G0/G1, Atomic-k, future clean-cut reduction, constants/atomic zeros and restricted mix coherence. | Open. |
| Reduced/Boolean Coherence | Use existing faithful_of_positive_coherence and representation transfers only after their premise is proved. | Open; no supplied instance. |
| Full-paper v6 ledger | Actual-presentation instances/congruence bridges, short q/e proof, unconditional maximality, model corollary, tagged ordinal substitution, both appendices. | Still required under unchanged full-paper contract. |

The first missing inference is containing blocked preservation. A local strict
bound for descendants **inside** h does not constrain changed ancestors, and
an outside occurrence's unchanged proof does not settle the blockedness of its
proper containing contractions. No multiset decrease or Blocked-w theorem is
claimed by substituting these weaker facts. This is an unfinished formalization,
not a counterexample or a defect in the published or author manuscript.

## Verification, exact evidence and limits

Final checked sources: **398 Lean files / 10,606 audited project
declarations**, including generated declarations. Added 67 production
modules and one exact-type check module; no old production definition changed.
All new modules belong to the audited public import closure. Every regular
source has a module header and fewer than 10,000 physical lines.

| Command | Exit | Seconds |
| --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 6.073 |
| `python3 scripts/check-audit-boundaries.py` | 0 | 12.25 |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.156 |
| `sha256sum -c SHA256SUMS` | 0 | 0.018 |
| `git diff --check` | 0 | 0.013 |
| `git diff --cached --check` | 0 | 0.006 |
| `lake env lean -DwarningAsError=true Checks/Reducibility.lean` | 0 | 0.771 |

The manuscript command runs in manuscript/. The strict build and axiom audit
passed with only propext, Quot.sound and Classical.choice. All five negative
controls rejected with exit 1 and their expected diagnostic: public custom
axiom, unused nonpublic custom axiom, external hidden axiom dependency,
distinct tagged projections by rfl, and zero without a typed existing-arrow
witness. Both control scripts returned 0. The public type file instantiates
both exact full signatures and prints all listed endpoint types.

Retained 129 exploratory build invocations and 84 nonzero receipt
rows across all checks in this run, including the missing universe binder in
the first exact-type test and dependent-elimination/cast failures. They are
not reported as successes; no unfinished production proof remains. Final
verification follows final production and public-check edits. Log archives
retain the actual diagnostics, commands, exit codes, elapsed times and hashes.
The final diff checks preceding documentation are supplemented after staging.

Evidence directory: `provenance/wsl-gentzen-full-reducibility/`:

- `CHECKED_SOURCES.sha256`, SHA-256 `4b8eb0f9febbd470d8c7ddd7c74e51c2a22b8492a9f0830d9cf9be8fa53c37db`, freezes all checked Lean,
  scripts, configuration and manuscript bytes. Compare this with committed
  Git blobs after commit. Reports are outside this nonrecursive inventory.
- `FINAL_VERIFICATION.json`, `PUBLIC_TYPES.json` give exact final commands,
  exits, timings and raw-log hashes. `COMMANDS.json` includes failed attempts.
- `LOG_ARCHIVES.json` names **retained .gz files**, with compressed and raw
  digests. Decompression is checked against each original log; no ignored raw
  log path is presented as a tracked archive.
- `AUDIT_CONTROLS.json`, `PRESENTATION_CONTROLS.json` and controls/ retain all
  five rejected input sources and expected diagnostics.
- `MODULES.tsv`, `DECLARATION_ANCHORS.tsv` give source anchors and hashes.

No independent clean kernel replay, NanoDa/con-ron/Comparator, official
Palomar preflight/service result, publication or whole-manuscript novelty
review was performed. Manuscript v4/v5/v6 bytes and accepted corrections are
preserved. The review reports are author-side audits of this argument.

## Checkpoint and report delivery

Retained reports:
`docs/GENTZEN_FULL_REDUCIBILITY_REPORT.md`,
`docs/reviews/GENTZEN_FULL_REDUCIBILITY_HOSTILE.md`, and
`docs/reviews/GENTZEN_FULL_REDUCIBILITY_WRITING.md`.
The corresponding Downloads basenames are the same under
`/mnt/c/Users/fleng/Downloads/`; differing existing files must be preserved
with a dated/commit suffix. Also deliver the retained B2AB0A8 instruction and
its two linked reviews as that instruction requires. Post-commit receipts
record actual destination names, byte comparisons, checked/committed inventory
identity, main/origin/live SSH ref agreement and preserved stash. The final
response supplies the commit SHA and actual paths; this report's own commit
identity is the commit containing its retained bytes, avoiding a self-hash cycle.
