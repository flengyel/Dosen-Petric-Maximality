# Binary-input Reducibility integration — 25 October 2026

## 1. Status and scope

**Both full Reducibility Lemmata remain open.** Every actual contraction over
native `mix`, `conjR` or `disjL` now has a left and a right producer, with internal
positional selection matching and the complete eligible-descendant bound.
`BinaryReducer.left/right` assemble these cases; a binary cut premise is ruled
out by the cut-freeness already contained in reducibility. The right-W4 repair
now includes one parametric copy plus the fresh compound, using a node-free
singleton inner operation. Source W6, native/source repairs and all three
source singleton blockedness exclusions compile. General unary dispatch,
including exchanges crossing selected copies, is still missing. Outside-site
transport, multiset descent, Blocked-w, cut elimination and coherence remain open.

Measured checked sources: **330 Lean source files / 9,737 audited project
declarations** (818 additional audited declarations, including generated
helpers; this is not a count of new mathematical theorems). Exact results:
[GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md](GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md),
[author-side hostile review](reviews/GENTZEN_REDUCIBILITY_INTEGRATION_HOSTILE.md),
[author-side writing review](reviews/GENTZEN_REDUCIBILITY_INTEGRATION_WRITING.md).
The governing instruction is [CODEX_AFTER_1E967BC_REDUCIBILITY.txt](CODEX_AFTER_1E967BC_REDUCIBILITY.txt).
This checked integration does **not** complete that instruction's final target.


Base commit: `1e967bcb913a74ae590dde940f246acaddce1fba`. The task requested both full source-shaped
Reducibility Lemmata. They are not proved here. The obstruction is an unproved
unary selection/routing construction, stated precisely in §7; no counterexample
to the published lemma or claim of mathematical impossibility is asserted.

## 2. Exact proved endpoints and hypotheses

All production statements are in `DosenPetric.Reduced.Gentzen`, for arbitrary
`P : Type u`. `comp f g` executes `f` and then `g`. Equality of denotations
is equality in the existing syntactically generated `Reduced.Hom` quotient.
`ContractionBlock P F K` specifies the actual contracted formula, selected gaps,
fixed tail and endpoint equalities; `d.keep` is its retained typed position.

The general binary producers have these types (implicit contexts suppressed
only in this display; their full exported signatures are retained in the type log):

```lean
BinaryReducer.left
  (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)
  (t : G P F V) (hb : t.ruleKind.Binary)
  (f : G P Φ (d.C :: Ξ)) (g : G P (d.C :: Ω) Ψ) :
  ReducesL f g (d.applyL hn V t) d.keep

BinaryReducer.right
  (d : ContractionBlock P V K) (hn : 2 ≤ d.gs.length)
  (t : G P U V) (hb : t.ruleKind.Binary)
  (f : G P Φ (d.C :: Ξ)) (g : G P (d.C :: Ω) Ψ) :
  ReducesR f g (d.applyR hn U t) d.keep
```

`Binary` is the existing classification of `conjR`, `disjL`, `mix`, `cut`.
The last case is impossible under the subsequent reducibility hypothesis;
there is no new cut-freeness assumption in the displayed interfaces.

`ReducesL f g w x` means, for **every** actual address `a : ProofAddress g w`
and `hr : ReducibleL f g a x`, there exists `h` with exactly the same sequent,
`h.CutFree`, `ofTerm h.denote = ofTerm w.denote`, and for every address `b`
inside `h` and every typed antecedent position `y`,

```lean
ReducibleL f (a.replace h) ((a.inserted h).append b) y →
  v.rho .left y < w.rho .left x
```

The right definition uses addresses inside `f`, succedent positions, and
`ReducibleR (a.replace h) g ...`. These definitions retain the entire target
quantifier; the definitions alone prove nothing. The new producers establish
them for binary inputs. `ProofAddress.replace_denote` supplies the corresponding
equality after rebuilding the containing proof.

Reducibility has its existing meaning: a topmost cut (both premises cut-free),
a tied lower contraction, unblockedness at that node, and blockedness of every
proper containing tied contraction. Entry uniqueness is the previously proved
typed separation theorem, not an injectivity hypothesis. No caller supplies a
candidate, selection split, lower-context equality, rank bound, coherence,
`Nonempty P`, `DecidableEq P`, enumeration, freshness or label disequality.

Principal declarations and their actual source modules:

| Declarations | Proved scope |
| --- | --- |
| `BinaryReducer.left/right`, `selection_left/right` (`GentzenBinaryInputReducers`) | Complete actual binary-input dispatch on both sides, cut case excluded internally. |
| `MixReducer.left/right` (`GentzenMixInputReducer`) | Actual native order `mix f g : (F++U) ⊢ (Λ++Δ)`; empty/one/both selected branches obtained internally. |
| `ConjunctionReducer.left/right` (`GentzenConjunctionAntecedentReducer`, `GentzenConjunctionInputReducer`) | Every selection, with fresh head unselected or selected where that head is on the contracted side. |
| `DisjunctionReducer.left/right` (`GentzenDisjunctionAntecedentReducer`, `GentzenDisjunctionSuccedentReducer`) | Every selection; native/source order and actual blocked source repair handled explicitly. |
| `W4.NonemptyRight.addressed_right` (`GentzenReducibilityNonemptyRight`) | Terminal right-W4 data, at least one parametric copy, arbitrary containing address; singleton handled without a contraction node. |
| `W6.SourceLeft.addressed_left`, `W6.HeadRight.addressed_right`, `W6.NativeLeft.addressed_left` | Constructed W6 families with independent positive arities and full eligible-descendant bounds. |
| `W6.SourceLeft.old_singletons_blocked`; `W6.SourceOne.oldFirst_singleton_blocked`, `oldSecond_singleton_blocked` | Actual source-macro singleton patterns, respectively disjunctionBoth/First/Second; no transfer to native blockedness. |
| `W1.reducesL/R`, `W1.Exchange.reducesL/R`, `W1.Logical.reducesL/R`, `W1.Contraction.reducesL/R` | Full descendant adapters for the existing opposite-side unary families, using their proved strict targeted endpoint decrease. |

`NEW_MODULES.txt` lists all 81 new production modules.
`NEW_DECLARATIONS.tsv` gives source anchors for named declarations.
`verification/PublicTypes.lean` and its log check public exported hypotheses.
The complete transitive audit includes private/generated dependencies as well.

## 3. Published-source correspondence

Pinned source: Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`. Page numbers are printed;
one-based PDF page = printed page + 12. Rendered printed p.252 was inspected.

| Source | Published construction | Lean correspondence and qualification |
| --- | --- | --- |
| §11.2 pp.248–250 | Whole-formula clusters, all-node rank, tied/blocked/reducible contractions, Reducibility statement | Existing `rho`, `ReducibleL/R`, fourteen blocked frames and entry uniqueness are reused unchanged. |
| p.251 W1 | Parametric unary commutations, including exchange absorption | Opposite-side families have full adapters; arbitrary crossing/multigap/absorption exchange dispatch is still open. No Semilattice Coherence assumption is imported. |
| p.251 W4; p.252 right analogue | Contract parametric compounds before logical introduction and use a blocked middle | `W4.NonemptyRight`; n counts parametric copies, and the fresh compound is an additional selected copy. |
| pp.251–252 W5, `(m nat)` | One-branch or two-branch contraction through mix | Internal `Split`, lower-context/old-proof comparison, `MixReducer.left/right`. |
| p.252 paragraphs following W5, `(w γ 2)`, `(w γ 3)`, `(dL nat)` | Binary conjunction and disjunction W5 | `ConjunctionReducer` / `DisjunctionReducer`; actual `Rules.conjRight`, `Rules.disjLeft`, sourceConj/mixedDisj naturality and product/coproduct component laws. |
| p.252 W6, `(w ∨ 1–3)` | Parametric copies in one/both premises plus a fresh disjunction; blocked source middle | Source uses terminal `disjLLast`, with explicit head/input/output exchanges. `SourceLeft`, `NativeLeft`, `OneHeadDisjunction`, separately typed `HeadRight`, and internally matched native dispatch. |
| p.252, final right-analogue paragraph | Right Reducibility construction | Implemented independently with coproduct variance; no contravariant arrow-negation operation is assumed. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants and atomic-zero extension | Existing leaves, empty contexts, syntax/equations and witnessed-zero policy are preserved. No new generator or special empty-sequent leaf. |

The source's strictified concatenation notation is not definitional list
associativity in Lean. `cast`, `reindex`, chain associativity and endpoint
comparison laws carry all necessary transports. No new source discrepancy is
claimed. Earlier discrepancy/access records remain historical evidence.

## 4. Construction and rank checks

`ContractionSelection.Split` jointly identifies the original indexed selection
and its lower context. It distinguishes left-only, right-only and both branches.
`HeadSplit` adds the independently classified unselected/selected principal head,
with six nontrivial regimes. `onlyFresh` has arity one and contradicts the
existing outer-contraction bound. Lists preserve order and multiplicities;
repeated labels are not compared or deduplicated. `CS.blockArity` is a named
public proof so public dependent indices do not leak private elaborator proofs.

Write n for a selected parametric arity and δ(n)=0 if n=1, δ(n)=1 if n≥2.
The singleton-aware `performL/R` operation is a reindexing when n=1.
For right W4, if S is the sum of original selected parametric ranks, the
compiled formulas are inner=S+δ(n), old=S+n+2. Thus the one-parametric old
rank is S+3 and the inner rank is S. `SingletonRightRegression.old_reducible`
is the requested inhabited Empty-variable regression with `some 1` prefix.
The previous two-copy comment now explicitly says two **parametric** copies.

For native W6 with both premises selected, let n,m≥1, and let S be the sum
of the original selected whole-formula ranks in both premises. The native old
rank is S+n+m+2. The separately constructed source old rank is
S+3n+3m+3, where S there uses the terminal-premise coordinates. Its source
repair rank is 9+I+J. These are statements about different syntactic proofs;
they are not identified by denotation equality. For native conjunction-right
the blocked repair rank is 4+I+J; its endpoint bound follows from the two
singleton-aware premise formulas. Native disjunction-left uses actual source
macro exchanges and an exit permutation. `ContractionBound` skips the actual
blocked middle and bounds the surviving parametric premise frontiers strictly
below the native old rank. It does not require the candidate's root rank to
be smaller. One-selected-premise W6 has native old rank S+n+2, and its
surviving inner contraction rank S+δ(n) is strictly smaller.

All categorical equalities use established Reduced laws: terminal/head
rotations, the product/coproduct universal properties, component calculations,
chain/fusion factorization and the actual mixed structural naturality laws.
The proofs do not reflect occurrence equality or inclusion equality. Relation
comparisons, where supplied, are obtained by applying `occurrenceMap` to proved
Reduced equality. Whole-formula ancestry and internal tagged literal occurrences
remain separate. No rank is asserted to descend to quotient arrows.

## 5. Verification results

Pinned Lean 4.35.0 and Init-only dependencies are unchanged. One build/audit
was run at a time. Strict checking screens 330 source files and audits
9,737 project declarations. Permitted axioms are exactly `propext`,
`Quot.sound`, `Classical.choice`; the audit accepts subsets of this list.

| Actual command | Exit | Seconds |
| --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 11.889 |
| `python3 scripts/check-audit-boundaries.py` | 0 | 11.954 |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.738 |
| `sha256sum -c SHA256SUMS` | 0 | 0.031 |
| `git diff --check` | 0 | 0.019 |
| `git diff --cached --check` | 0 | 0.013 |
| `lake env lean -DwarningAsError=true .../PublicTypes.lean` | 0 | 5.845 |

The manuscript checksum command ran in `manuscript/`. All five negative
controls were actually rejected with compiler/audit exit 1: public custom
axiom, unused private custom axiom, hidden external axiom dependency,
reflexive equality of distinct tagged projections, and zero without a typed
existing-arrow witness. Their enclosing scripts exited 0. Production import
closure passed. Public queries and selected axiom prints passed separately.

110 unsuccessful commands with JSON receipts and their complete diagnostic
logs are retained. An interrupted length-copy exploration exited 130 before
its runner wrote a receipt; elapsed time was not captured. The retained log
and `UNRECORDED_INTERRUPTION.md` record this limitation. One exploratory
arithmetic-tactic loop was corrected by finite structural interval lemmas.
A short build-lock rejection is retained as a failed attempt. None is counted
as a successful final verification. `COMMANDS.json` retains actual commands,
exit codes, elapsed times and log hashes, including failures.

No independent clean build/kernel replay, Comparator, official Palomar
preflight/service verification, external peer certification or publication
was performed. The prior baseline's actual receipts are retained; an unchanged
clean baseline was not rebuilt. Manuscript v5/v4 bytes remain unchanged.

## 6. Evidence and immutable-source correspondence

All paths below are under `provenance/wsl-gentzen-reducibility-integration/`:

- `CHECKED_SOURCES.sha256`: all checked Lean bytes, toolchain/manifest,
  verification scripts and manuscript checksum record; checked against the
  strict run's actual source hashes before record generation.
- `FINAL_VERIFICATION.json`, `PUBLIC_TYPES.json`, `COMMANDS.json` and
  `verification/`: actual receipts, logs, exported types and failed attempts.
- `NEW_MODULES.txt`, `NEW_DECLARATIONS.tsv`: production-module and declaration
  anchors. `BASELINE.md` distinguishes baseline, checked candidate and commit.
- `SOURCE_ACCESS.md`: source/cache locations and both verified PDF hashes;
  `incoming/` retains the exact supplied 1e967bc review and instructions.
- `SHA256SUMS`: hashes of retained evidence files. Full PDF caches are not
  copied into the repository. Post-commit checks compare committed bytes with
  `CHECKED_SOURCES.sha256`; delivery compares each report against `git show`.

Strict log SHA-256: `fc41670bf97d9748979512b10ee15633ebd1087e0d199766492ce8ad90decad0`.
Public type log SHA-256: `9cb55b32522802199256050273738a750afe5b13b64c799f9bbca4a21d995d7a`.
The committed-source/delivery receipts are retained in the local work directory
after commit; the final response supplies the resulting commit and live refs.

## 7. Remaining obligations and precise next theorem

The unchanged full targets are `∀ w x, ReducesL f g w x` and its separately
typed right counterpart. They remain unproved. The binary theorem's **Binary**
premise is a scope restriction; it has not been silently removed to claim the
full lemma. The next exact missing branch is arbitrary same-side exchange:

```lean
-- Proposed statements only; no such axiom or theorem is installed.
(d : ContractionBlock P (Γ ++ Y ++ X ++ Θ) K)
(hn : 2 ≤ d.gs.length)
(t : G P (Γ ++ X ++ Y ++ Θ) Δ)
  ⊢ ReducesL cutLeft cutRight
      (d.applyL hn Δ (G.exchangeL Γ X Y Θ Δ t)) d.keep

(d : ContractionBlock P (Δ ++ Y ++ X ++ Λ) K)
(hn : 2 ≤ d.gs.length)
(t : G P Γ (Δ ++ X ++ Y ++ Λ))
  ⊢ ReducesR cutLeft cutRight
      (d.applyR hn Γ (G.exchangeR Γ Δ X Y Λ t)) d.keep
```

Here both cut-premise roots have the existing head cut formula `d.C`.
There is no interval-exclusion condition on selected copies: X/Y may cross
selected copies, span gaps or contain equal fixed labels. The existing
`GapExchange` square requires the entire exchange to lie in one fixed gap or
tail; it cannot be instantiated for this statement. `Split` can divide the
selection, but a swap reverses the two selected sublists. An ordered extraction
and a proved lower-context permutation/factorization are still needed; equality
after inclusion or of occurrence relations cannot supply this categorical
square. Reassociation alone leaves it unproved. No mathematical impossibility
is claimed; this is a missing formal construction, and not a defect of the
published argument.

| Remaining proof | Status / predecessors |
| --- | --- |
| Arbitrary crossing-selected/multigap/absorption exchange producers | Open as typed above; need positional permutation factorization and descendant-bound transport. |
| Other unary input matching, interleaved disjoint contractions and arbitrary-position same-side logical cases | Earlier local theorems remain valid; complete actual-input dispatch is open. Shared W3 fusion is reused but not installed as a complete general dispatcher. |
| Selected-thinning and unary W4 singleton/placement coverage beyond the proved terminal families | Source regimens must be matched internally; no new blanket coverage is claimed. Right terminal one-parametric W4 is now proved. |
| Full left and right Reducibility | Requires every remaining actual unary branch, or a proved blockedness contradiction; no caller rank/coherence/decomposition hypothesis. |
| Outside-occurrence and containing-blocked-contraction transport | General replacement lemmas for denotation/ancestry exist; the needed reducibility-preservation theorem outside the replacement remains open. |
| Finite multiset descent and Blocked-w | Depend on both full producers and outside-site transport; open. |
| Remaining G2 / cut elimination; restricted positive coherence | Open and distinct. |
| PositiveCoherence, Reduced.Faithful, Boolean Coherence, unconditional maximality | Open; only previously proved conditional transfers are reused. |
| Palomar preparation/submission | Not performed or authorized as part of this proof integration. |

## 8. Preservation, reviews and delivery

The stash and older reconciliation archives remain intact. No manuscript,
grammar/equation, dependency, `Positive`, `G`, `Rewire`, `Atomized`, `CutFree`,
`Topmost`, tracing or rank definition was changed. No arbitrary-endpoint zero
was introduced. This is an author-side implementation and review, not independent
certification. Reviews are retained separately under `docs/reviews/`.

The three finalized reports retain repository copies and are delivered to
`/mnt/c/Users/fleng/Downloads` with conflict-preserving names. Each delivered
file must equal the bytes of its committed repository version. The post-commit
delivery receipt and final response identify exact paths and hashes. SSH push
is non-force; main, origin/main and live SSH refs must agree. Repository
visibility is not changed.
