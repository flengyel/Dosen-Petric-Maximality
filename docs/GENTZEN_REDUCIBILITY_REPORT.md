# Gentzen Reducibility: reconciliation and verified partial results

## Status and governing endpoint

**Both full Reducibility Lemmata remain unproved.** This checkpoint reconciles
the concurrent sources, proves replacement/cluster transport and conditional
descendant bounds, and connects terminal-left W4 to that bound. It also proves
two representation separations that prevent a direct reuse of the source case
analysis. It is not completed Reducibility, source-faithful reduction dispatch,
Blocked-w, or cut elimination.

The governing instruction is [the complete Reducibility task](CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
imported from its Downloads copy (original SHA-256
`6d33982103e1a0265a2d7ed02ed62dfd17ffd07811610eaee2b8a53e62491cc9`).
It supersedes the mixed-W5-only continuation. The supplied
[review of the preceding checkpoint](reviews/GENTZEN_REDUCIBILITY_REVIEW_2026-10-24.md)
is retained, with only its redundant EOF blank line removed in the tracked import.
Exact original bytes of both supplied files remain in the reconciliation archive;
FORMAT_ONLY_IMPORTS.json records the before/after hashes. The reviewed base is
`9075ecc343be5c07d38b7f5ba53676f8f8f32bea`, after the replacement/integration commit
`6b860df5fdb6e4c1c50dc583e0de0d04c102eb25`.

For arbitrary P, C, contexts and proofs
`f : G P Γ (C::Δ)`, `g : G P (C::Θ) Λ`,
`w : G P U V`, `a : ProofAddress g w`, `x : At U C`, the missing left theorem
must obtain from `ReducibleL f g a x` a proof `h : G P U V` such that
`h.CutFree`, `ofTerm h.denote = ofTerm w.denote`, and, for **every**
`b : ProofAddress h v` and `y : At I C`,

```text
ReducibleL f (a.replace h) ((a.inserted h).append b) y →
  v.rho .left y < w.rho .left x.
```

The right theorem places a in f, uses `ReducibleR`, and compares right ranks.
Neither theorem may require a caller-supplied reduct, coherence, injectivity,
or an assumed rank conclusion. The results below do not meet that full target.

## Preserved and combined source

Both sessions used the same checkout. The identified WSL2 writer PID 700028
exited; PID 3970616, the VS Code CLI, remained. Ten snapshots over twenty
seconds showed no further source/record/Git-state writes before continuation.
`WRITER_PROCESSES.json` records the later process observation. An observed
stable interval alone is not proof that every possible writer has stopped.

Before integration, tracked binary diffs, index state, all untracked bytes,
recent history, worktrees, stash refs and process working directories were
preserved. The archive `PRESERVED_RECONCILIATION.tar.gz` also retains the
overlapping exploratory implementations, including their original filenames
and hashes. They remain evidence outside the production import closure, not
discarded replacements or accepted proofs. The independent temporary candidate
was compared with 9075ecc: its ten modified Lean files match that commit.
The root import/audit differences in the live checkout were additive transport
registrations. Correctness and provenance were not inferred from Git status.

Four formerly untracked modules are incorporated **byte for byte**:
`GentzenAddressTracing`, `GentzenAddressPaths`, `GentzenClusterTransport`, and
`GentzenEntryFrames`. Four new modules add the checked boundary/W4/separation
results and examples. Only public imports and selected axiom prints change in
existing Lean files. No existing grammar, equation, predicate, rank, dependency,
or manuscript definition was changed. The integration stash
`dedfd8fc8cd49930e9a162d5be585215b062a43c` remains intact. No reset, clean,
stash drop, competing-file overwrite or work in another project was used.

The resulting combined baseline passed at **220 source files / 8,538 audited
declarations**, strict exit 0 in 8.509s, plus both boundary scripts and the
five expected negative rejections. These are measured results, not the older
216/8,406 checkpoint figures.

## Proved declarations and exact hypotheses

All names below are in `DosenPetric.Reduced.Gentzen`. The complete 75 public
queries and 59 selected theorem axiom prints are in `integrated-api.json`,
`PublicTypes.lean` and the retained output. These counts concern this task's
eight modules; the transitive audit covers the entire production closure.

| Declarations | Checked conclusion and hypotheses |
| --- | --- |
| `TraceNode.rank_eq_rho`, `edge_rank_lt`, `reach_rank_le/lt` | Cluster-node rank is the selected proof rank; immediate ancestry decreases it. Reachability gives ≤, or < when endpoint addresses differ. No denotation hypothesis. |
| `Branch.eq_of_branch`, `ProofSpine.eq_of_path`, `ProofAddress.eq_of_path` | Actual branch sequences identify typed proof occurrences with fixed endpoints. Equal proof values in different branches retain different addresses. |
| `ProofAddress.ascend`, `ascend_append/inserted`, `ascend_reach`, `ascend_rank_le/lt` | Partial whole-formula ascent along an actual address; strict rank bound requires a nonempty path and a successful ascent. |
| `cluster_iff_ascend`, `ascend_replacement`, `replacement_cluster_iff` | Membership in the rebuilt cluster is equivalent to an intermediate local position z with `b.ascend s y = some z` and `a.ascend s z = some x`. Formula, side, proof and position types are retained. |
| `EntryFrame.mono/index_reindex/of_index/immediate/unique_origins` | A finite separation frame bounds which root entries can reach a descendant contraction. `unique_origins` equates the root entry positions, not arbitrary descendant positions. An actual `EntryFrame` is a hypothesis; the source blocked-pattern instances have not been constructed. |
| `Premise.equal_parent_or_lower` | Two upper positions with the same parent are equal, or that parent is a lower contraction position. This follows from the established independent predecessor classification. |
| `ProofAddress.injective_root/down`, `noncontracting_injective` | Root ascent is injective; step preservation requires no lower contraction on the selected side in the parent. `NoncontractingPath` is an explicit sufficient syntactic condition, stronger than ReducibleL/R. |
| `ReducibilityBoundary.entry_unique_of_injective` and `_right` | Given ReducibleL/R and InjectiveAscend, any local position ascending to the cut position equals the chosen lower contraction position. The injectivity premise is not derived from reducibility. |
| `ReducibilityBoundary.descendants_left/right` | Given a blocked candidate h, a unique cut entry x at the original address, and `h.rho s x ≤ w.rho s x`, every post-replacement reducible descendant has rank < the original selected rank. No denotation equality or cut-freeness is assumed or inferred by these boundary lemmas. They do not construct h. |
| `G.reindex_trans`, `BlockedL.reindex`, `BlockedR.reindex` | Composition of actual equality transports and transport of the existing blocked predicates. No new exchange constructor is hidden in a cast. |
| `W4.SelectedLogical.new_blockedL` | The existing terminal-left W4 reduct is exactly the `(w∧1)` blocked pattern after proved endpoint transports, for arbitrary d, arity≥2, contexts and premise. |
| `addressed_left_of_injective` | For an arbitrary address to a terminal-left W4 old proof, `ReducibleL` **and** `InjectiveAscend .left` give a cut-free new proof, equal local/rebuilt Reduced denotations, and the full quantifier over all post-replacement reducible descendants. No atomicity assumption. |
| `addressed_left_noncontracting` | The descendant conclusion follows under ReducibleL and the stronger syntactic NoncontractingPath condition. This is a conditional specialization, not the full left lemma. |
| `two_copy_root_left` | For arbitrary A,B,P, a cut-left proof and a cut-free premise `G P [A∧B,A∧B,A,B] Δ`, constructs h at `[A∧B] ⊢ Δ`, with equal Reduced denotation and the complete post-replacement descendant bound. The containing address is root, so no injectivity premise is needed. |
| `ReducibilityObstructions.terminal_right_w4_unblocked` | Every existing terminal-right W4 reduct is **not** BlockedR. Its unary disjR premise has a nonempty fixed prefix. The current blocked unary right pattern has empty prefix. This does not refute existence of another suitable reduct. |
| `freshBoth_unblocked`, `splitMix_blocked` | The native three-copy disjL example is unblocked despite its proved selectedBoth profile; singleton/singleton mix is already a gammaMix blocked contraction. Neither observation is a counterexample to the classifier or the full Reducibility theorem. |

For the two-copy root W4 case, old and new retained endpoint ranks tie.
The proof excludes a reducible root because the new root is blocked; every
eligible proper descendant follows a nonempty ancestry path and therefore
has strictly smaller rank. This handles surviving old descendants as well as
newly created nodes. Under the additional injective-address hypothesis the
same reasoning works below arbitrary containing rules.

Compiled examples distinguish identical siblings by both address and selected
position, check their two different clusters, trace a surviving position
through an actual cut, cover both literal signs, and instantiate the root W4
existential over `P = Empty` with an inhabited constant premise. Existing
replacement identity/sibling/congruence/count proofs are reused unchanged.
No cut-count or proof-size comparison is converted into a cluster-rank claim.

## Source correspondence

The hash-verified September 2007 PDF is
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n corresponds to PDF n+12, one-based. Printed pp.248–253 were
consulted; rendered p.250 was inspected again. Historical access records and
the cached PDF remain preserved. No new equation is attributed to the source.

| Source | Present construction | Remaining comparison |
| --- | --- | --- |
| pp.248–249: whole-formula basic sequences, cluster, all-node rank | Typed At positions, actual branches/paths, finite cluster and successful partial ascent; exact rank/reachability bridge | No rank invariance under arrow equality. |
| p.250: seven displayed blocked patterns and proper-containing reducibility | Existing BlockedL/R and ReducibleL/R retained; new blocked reindex laws and W4 `(w∧1)` instance | Macro adequacy for primitive disjL and right-retention/order remains unproved. |
| p.250: Reducibility Lemma; pp.251–252 case analysis | Full required quantifier appears in both boundary criteria and the scoped left W4 theorems | Criteria assume a candidate and entry/rank data. No general producer from ReducibleL/R exists. |
| p.251 W4, `(w∧1)` | `new_blockedL`, retained endpoint bound and all-descendant W4 specialization | General blocked-ancestor entry uniqueness is open. |
| p.252: right analogue after W6 | Separately typed right boundary criterion; terminal-right W4 mismatch proved by a syntactic prefix observer | The head/terminal comparison and its eligible-descendant rank bounds are open. |
| pp.251–252 W5 and p.252 W6 | Existing one-premise mix families reused; singleton/singleton blockedness checked | General mixed extraction, binary logical reducers and full dispatch are open. |
| p.253: Blocked-w multiset induction | No new claim | Outside-occurrence/blocked-ancestor transport, finite eligible-occurrence collection and well-founded multiset order remain to be constructed. |

The source's Semilattice Coherence appeals have not been installed as Lean
assumptions. Earlier local categorical equations use the existing Reduced
laws. Literal-occurrence equality follows from those equations where used;
it never proves syntactic arrow equality. Whole-formula ancestry is a separate
construction, including constants whose literal occurrence types are empty.

## Exact blocker and attempted repair

The first missing inference is the following **proposed sufficient lemma**,
not a production assumption or a claimed theorem:

```text
(hr : ReducibleL f g a x) →
  ∀ z : At U C,
    a.ascend .left z = some (At.here C Θ) → z = x
```

There is a separately typed right version. InjectiveAscend proves this
in a restricted class of containing contexts. General reducibility only says
that proper containing *tied* contractions are blocked. It does not state
that ascent is globally injective. Replacing that missing inference by global
injectivity would strengthen the target's hypotheses and is not accepted.

A concrete structural route is to prove, for all seven blocked left cases,
with `t : G P (repeated C gs ++ Θ) Δ`:

```text
BlockedL (G.contractL C gs Θ Δ hn t) →
  EntryFrame .left C t (fun z => z ∈ selectedCopies C gs Θ)
```

and the separately typed right schema. These finite frames must pass through
the actual disjLLast exchanges and source retention conventions. Combining
them with proper-ancestor blockedness and the proved `unique_origins` is the
attempted repair. Only the generic frame calculus is proved; these source
instances and the resulting uniqueness inference remain open.

The second demonstrated obstruction is **not** an unproved compiler goal:
`terminal_right_w4_unblocked` compiles. Put C=A∨B, X=gaps gs, Y=Θ and
I=X++C::Y. The current right W4 new proof contracts after a terminal
`disjR Γ I [] A B`, whose prefix has positive length. BlockedR.disjunction
recognizes `disjR Γ [] (X++C::Y) A B` instead. Equality of endpoints or
denotations cannot identify these proof constructors.

An explicit repair to investigate is to exchange the inner proof's output
`I++[A,B]` to `[A,B]++I`, introduce C at the head with disjR, contract the
head C with the parametric C using gaps `[[],X]` and tail Y, then exchange
the retained C across Y to reach `(X++Y)++[C]`. The middle contraction is
then the actual BlockedR.disjunction pattern. This requires a checked
Reduced comparison with the existing terminal composite and an ancestry
analysis through all explicit exchanges. It is not implemented or assumed.
The outer exchange is not a contraction; its rank cost cannot be erased.
A blocked-frontier descendant argument is needed rather than falsely
asserting that the entire wrapped proof is BlockedR or has a small root rank.

Thus the full target has not been proved and has not been refuted. The
checkpoint establishes where the attempted proof stops. Mixed W5 and logical
W5/W6 remain subordinate missing cases; no new research objective replaces
the governing Reducibility task.

## Verification and evidence

Final sources: **224 Lean files / 8,602 audited project declarations**.
Pinned Lean 4.35.0, Init-only closure and existing Lake manifest unchanged.
Final sequential commands after the last proof edit:

| Command | Exit | Seconds |
| --- | --- | --- |
| strict | 0 | 19.924 |
| audit-boundaries | 0 | 28.958 |
| presentation-boundaries | 0 | 3.039 |
| manuscript | 0 | 0.021 |
| diff-check | 0 | 0.029 |
| cached-diff-check | 0 | 0.016 |

The strict row is `bash scripts/verify.sh`; boundary rows are the two named
Python scripts; manuscript is `(cd manuscript && sha256sum -c SHA256SUMS)`.
Exact command arrays, timestamps, logs and hashes are in `final-20261025T015738139434.json`.
The 75 public type queries passed (exit 0, 2.817s).
The 59 selected axiom prints supplement the complete transitive audit;
permitted axioms remain propext, Quot.sound and Classical.choice.

All five expected controls rejected with Lean exit 1 and the expected diagnostic:
public custom axiom, unused private custom axiom, hidden external axiom
dependency, distinct tagged projections identified by rfl, and zero without
a correctly typed existing-arrow witness. Full local public import closure
passed. Evidence fixtures are deliberately invalid controls, not production proofs.

The first staged whitespace check rejected redundant EOF blank lines in the
two imported files and a worktree listing (exit 2). Originals are archived;
only the imported/captured copies were normalized before repeating that check.
Raw logs, including this diagnostic, are retained byte-for-byte in RAW_LOGS.tar.gz;
extract it in this evidence directory to reproduce their recorded paths.

Six failed exploratory compilations are retained with commands, exits,
timings and diagnostics. They concern dependent pattern parameters, an unused
binder/namespace lookup, composed casts, an observer through transports, and
two root-address endpoint attempts. All were followed by passing checks;
there was no aborted new full build or overlapping heavy process in this phase.
The earlier concurrent checkpoint's failures and interrupted isolated attempt
remain historical evidence and are not relabelled as current success.

Evidence directory: `provenance/wsl-gentzen-reducibility/`.
Key SHA-256 values:

- Checked source/tool inventory: `2e081327271ba6b081f21fe7003e11190f0afdda0699e779cee0d0156bc1e0db`.
- Final strict log: `e053c224d5d2911be833e248576b00c26e2f685baf8260ad2b63efb7389f86e5`.
- Exact public type output: `6cfdc29e5575f88386c06abcc655e5ea9f4417071d557e3876af003192ee1bf9`.
- Preserved reconciliation archive: `0a31fda82438d0defe6a9744682d38636f04e58da53779c47baf75c84cfdbb20`.

`EVIDENCE_SHA256SUMS` inventories the retained evidence;
`REPORT_SHA256SUMS` and `RECORD_SHA256SUMS` identify reports and status records.
Post-commit receipts compare source bytes, all scoped committed files, refs and
delivered reports. They are separate from the pre-commit build identity.

## Remaining obligations and delivery

Next: construct the actual blocked-pattern entry frames and prove the
proper-ancestor-to-unique-entry inference, then remove InjectiveAscend from
the addressed left W4 theorem. In parallel dependency order, resolve the
explicit head/terminal right W4 comparison above; do not obtain it by
contravariant arrow negation or invisible exchanges. Both full Reducibility
Lemmata remain the acceptance criterion. Complete missing W1/W2/logical and
mixed W5/W6 cases only as branches of that target.

Blocked-w, arbitrary surrounding-context eligibility transport, cut elimination,
restricted positive coherence, PositiveCoherence, Reduced.Faithful, Boolean
Coherence, remaining congruence/substitution bridges and unconditional
maximality remain open. No manuscript defect follows from an unfinished proof
of a cited theorem. Palomar independent kernels/Comparator/preflight/service,
publication, fresh manuscript layout and independent peer review were not run.

The associated [hostile](reviews/GENTZEN_REDUCIBILITY_HOSTILE.md) and
[writing](reviews/GENTZEN_REDUCIBILITY_WRITING.md) reviews are AI-assisted
author-side reviews. They reject a full Reducibility completion claim.
Repository reports remain under docs/; conflict-preserving copies and the
updated continuation are delivered to `/mnt/c/Users/fleng/Downloads` and
compared byte for byte with committed Git blobs. Final SHA/ref/delivery
receipts are retained in `.codex-work/gentzen-reducibility/`.
