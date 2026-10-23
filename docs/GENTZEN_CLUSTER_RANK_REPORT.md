# Typed Gentzen ancestors, finite clusters, and cut rank

## Proved endpoint

For arbitrary `P : Type u`, contexts `Γ Δ : List (NormalForm P)`,
`C : NormalForm P`, `s : SequentSide`, `g : Reduced.Gentzen.G P Γ Δ` and
`x : Place s Γ Δ C`, the development constructs a finite rooted cluster of
whole-formula positions and proves its correctness. All sixteen unchanged
Gentzen schemas are covered, including proofs containing cuts.

The variables u and n below have types `Upper g s C` and
`TraceNode P s C`, respectively. The principal API proves:

```lean
u ∈ g.predecessors s x ↔ g.IsPredecessor s x u
(g.predecessors s x).length = g.sourceArity s x
n ∈ (g.cluster s x).nodes ↔
  FiniteTrace.Reach TraceNode.Edge (g.traceRoot s x) n
g.rho s x = (g.cluster s x).nodes.length
g.rho s x = 1 ↔ g.Leaf s x
```

It also proves the root/edge/address laws, exhaustive and disjoint source
classification, every contraction branch, positivity, strict child rank
inequalities, exact contraction sums, and both cut ranks. `cutRank f g ≥ 2`,
with equality exactly when both selected cut positions are source leaves.
This completes the cluster/rank prerequisite within G2; it does not complete
G2 transformations, Reducibility, Blocked-w, or cut elimination.

No Nonempty P, DecidableEq P, enumeration, freshness, coherence or denotation
reflection is assumed. Objects permit both signed literals and both constants.
Rank definitions require neither Topmost nor Atomized nor CutFree. Their
application-specific specializations are proved separately.

## Baseline and unchanged interfaces

Main was clean at `045ade65a636ae331f3d635e5e6f4a18e0cb8061` and agreed with
fetched SSH origin. Baseline verification actually reported 89 Lean files and
3,990 audited declarations. No reset, discarded work or other-checkout edit.
Sixteen new modules, root imports and sixty selected axiom prints were added.
All pre-existing DosenPetric Lean modules, historical reports/access records,
manuscript v4, Lean 4.35.0 and the Init-only dependency/manifest policy remain
unchanged. In particular, the 21 reduced constructors, 61 reduced equation
schemas, 19 Positive schemas, sixteen G schemas and the existing AtomicFormula,
Atomized, CutFree and Topmost definitions are byte-identical to baseline.

## Source correspondence

The directly consulted source is Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
Verified SHA-256:
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF n+12, one-based. Printed pp.247–250, 272–273 and 291–292
were read; pp.248–249 were also inspected in rendering. Printed pp.251–252
were read to specify the next Reducibility case. No new source discrepancy
was confirmed, and historical access/error records are preserved.

| Source location | Definition / repository correspondence | Proved declaration |
| --- | --- | --- |
| §11.2 p.247, leaf formulae | Atomic identity leaves both sides. Thinning and logical introduction terminate at the selected principal whole formula. The source's rightmost/leftmost conventions are translated to the explicit list gaps of existing G, rather than matched by formula value. | `G.sourceArity`, `Leaf`; classification/count correctness and principal-leaf lemmas. |
| §11.2 pp.247–248, lower/upper contraction formulae | Lower position is `At.shift (gaps gs) (At.here C Θ)`; upper copies occur after each selected gap in `repeated C gs ++ Θ`. Fixed equal formulas in gaps are not selected copies. | `G.LowerContraction`, `selectedCopies`, `selectedCopies_length/nodup`, `contraction_predecessorsL/R`. |
| §11.2 p.248, parametric sequences | Each fixed position has one upper position in the designated premise, with the same side and whole formula. | `Premise.parent`, `G.predecessors_correct`, `sourceArity_correct`, `parametric_unique`. |
| §11.2 pp.248–249, finite cluster | Root is the selected conclusion position; leaves stop; contractions branch to all selected upper copies; parametric nodes have one successor. Node labels identify proof occurrences. | `TraceNode`, `ProofAddress`, `G.cluster_root`, `cluster_correct`, `cluster_address`, `TraceNode.cluster_children`. |
| §11.2 p.249, ρ | Total number of nodes, including the root and every branch; not longest-path length. | `G.rho_node_list`, `rho_eq`, `rho_one_iff_leaf`, `rho_child_lt`. |
| §11.2 p.249, contraction ranks | Apply ρ to the lower contraction position, for arbitrary proofs. | `contractionRankL/R`, `contractionRankL_eq/R_eq` give 1 plus the sum over every selected copy. |
| §11.2 p.249, left/right cut formulas and ranks | For `f : G P Γ (C::Δ)`, left cut formula is the right-side head of f; for `g : G P (C::Θ) Λ`, right cut formula is the left-side head of g. Sum their ranks. No Topmost premise is required. | `leftCutRank/rightCutRank/cutRank`, `cutRank_ge_two`, `cutRank_two_iff_leaves`. |
| §11.2 pp.249–250, tied contractions | A branching lower contraction node belongs to the chosen cut-formula cluster, on its specified side. | `TiedRight/TiedLeft`, both `tied*_iff_branching` theorems. Blocked forms and rewrites remain open. |
| §11.5 pp.272–273, constants | topI has a genuine target top position and botE a genuine source bot position; these are leaves although their literal-occurrence types are empty. Empty context colours remain distinct. | `topI_rank`, `botE_rank`; unchanged G/denotation/no_empty. |
| §12.5 pp.291–292, atomic zero extension | Both positions of an atomic zero basis term are leaves; later zero cut rewrites are not part of this construction. | `zero_leaf/zero_rank`; old zero grammar/equations unchanged. |


The source's associativity/unit conventions do not make binary NormalForm
objects definitionally strict. This construction uses positions in the exact
existing list contexts; no new strictification or denotation identity is
needed to define the combinatorial ancestry. Earlier denotation comparisons
remain unchanged and are not replaced by literal-occurrence relations.

## Typed positions and independent rule routing

`SequentSide.left/right` specifies antecedent/succedent.
`Place s Γ Δ C` is the existing `At` position in that side's context;
`SidePos Γ Δ C` is also provided as the sum of both sides. `At.compare`
compares two positions in one context structurally. Its same case determines
the formula index as well as the position; it does not decide equality of
arbitrary formulas or variables.

`Premise` names a particular immediate premise occurrence. Unary rules use
branch 0; binary first/second proof arguments use 0/1, even when the proof
values are equal. `Premise.parent` independently maps an upper position to
its lower position, or none for a consumed upper principal component.
It uses actual swapBlocks, Route.thin and copies, plus explicit fixed-block
and binary embeddings. This partial metadata map is not an arrow operation.

`TraceRoute.fiber` computes every inverse image in upper positional order.
`fiber_correct` proves membership iff the separately specified upper-to-lower
map has the selected lower image. `fiber_ordered` prevents reordering by
labels. `G.predecessors_correct` then proves soundness and completeness for
actual rule premises. `sourceArity` is independently defined from G's
constructor, selected side and numerical principal index. Its agreement with
the computed predecessor count is proved by exhaustive cases, using typed
unary/binary/copy fiber laws, not asserted as a field of the desired result.

| Existing G schema | Selected conclusion positions and predecessor routing | Source arity |
| --- | --- | --- |
| identity | Both singleton literal positions are leaves. | 0 |
| zero | Both singleton literal positions are leaves. | 0 |
| topI | Only the target top position exists; it is a leaf. | 0 |
| botE | Only the source bot position exists; it is a leaf. | 0 |
| exchangeL | Source routed by inverse positional block exchange; target fixed. Parent map is the existing swapBlocks. | 1 |
| exchangeR | Target routed by inverse positional block exchange; source fixed. | 1 |
| thinL | Source principal at index Γ.length is a leaf; other positions invert existing Route.thin. | 0 or 1 |
| thinR | Target principal at index Δ.length is a leaf; other positions invert existing Route.thin. | 0 or 1 |
| contractL | Source at index (gaps gs).length branches to selectedCopies; fixed source/target positions have one predecessor. | gs.length or 1 |
| contractR | Dual target selection and every upper copy; fixed positions have one predecessor. | gs.length or 1 |
| conjL | Inserted whole A∧B at the source gap is a leaf. Upper A and B are not ancestors of it; fixed positions retain prefix/tail coordinates. | 0 or 1 |
| disjR | Inserted whole A∨B at the target gap is a leaf; fixed positions retain prefix/tail coordinates. | 0 or 1 |
| conjR | Source Γ++Θ routes to f/g respectively. Target head A∧B is a leaf; residual Δ++Λ routes to the appropriate premise, after its upper principal head. | 0 or 1 |
| disjL | Source head A∨B is a leaf; residual Γ++Θ routes to f/g after their principal heads. Target Δ++Λ routes directly to f/g. | 0 or 1 |
| mix | Conclusion is Θ++Γ and Λ++Δ: first blocks belong to g (branch 1), second to f (branch 0). | 1 |
| cut | Same conclusion order as mix. Surviving source Θ is in g after consumed C; Γ is in f. Surviving target Λ is in g; Δ is in f after consumed C. Neither consumed C is a conclusion position. | 1 |


`position_classification` and `position_classes_disjoint` separate Leaf,
Parametric and the actual indexed `LowerContraction` constructors.
`parametric_unique` supplies the unique upper datum and singleton list.
`selectedCopies` has exactly gs.length distinct positions. Its offsets and
the exact `contraction_predecessorsL/R` equations preserve every separated
copy, including empty gaps and fixed occurrences with the same formula.

## Finite tree and correctness

`TraceNode P s C` stores source and target contexts, the proof at that node,
its proof-occurrence address, and a typed whole-formula position.
The parameters s and C are retained by every predecessor, child and tree node.
`ProofAddress` is an inductive root/premise path; `cluster_address` proves
that every produced node's stored address is a valid occurrence of its exact
proof in the original g. Arbitrary TraceNode records are not presumed valid;
this validity is proved for actual cluster members.

The proof address alone does not identify a node: multiple selected upper
copies share one premise address but have distinct At positions. Conversely,
equal proof values in different binary branches have different addresses.
No comparison of subterm values or formula labels deduplicates the tree.

`TraceTree` is an explicit finite rooted tree with a finite list of children;
nodes are enumerated by a finite List. `FiniteTrace.tree` recursively descends
through actual premises using `G.proofSize`. `Premise.proofSize_lt` proves
strict decrease, including both premises of cuts. This is a checked
termination argument, not a finite-type assumption on P.

The generic FiniteTrace data require a local successor specification and a
decreasing level. `TraceNode.system` supplies both with proved routing and
premise-size laws. No cluster/reachability conclusion is assumed as input.
`cluster_root` gives the selected root exactly. `cluster_children` proves
immediate edge soundness/completeness; `cluster_correct` proves membership
iff finite predecessor reachability, including zero steps at the root.
`cluster_address` excludes spurious subproof addresses; `cluster_closed`
includes every successor of any member. Together with exact source arity and
contraction enumeration, these establish finite, correctly typed ancestry.

`predecessors_reindex`, `cluster_reindex` and `rho_reindex` commute with actual
equality transport of the endpoint contexts. The existing positional maps
are used directly and connected to the proved fiber and count laws.
`cluster_cutFree/cluster_atomized` propagate existing proof predicates to all
node labels. `topmost_cluster_properties` specializes these to the two selected
cut clusters using ht, hf and hg. General construction needs none of them.

## Rank equations and their scope

`G.rho g s x` counts all nodes, not just leaves or the longest branch.
`rho_node_list` proves equality with the length of the explicit node list.
`rho_eq` is the exact structural equation:

```text
rho(g,x) = 1 + sum [rho(u.proof,u.position) | u in predecessors(g,x)].
```

Combined with the complete source classification, this gives every constructor
equation: leaves have rank 1; a parametric position has rank 1 plus its unique
child rank; a contraction has rank 1 plus the sum over all selected copies.
`rho_pos` and `rho_child_lt` prove positivity and a strict inequality for every
actual child, using its independent IsPredecessor condition.

The left contraction formula has the exact equation:

```lean
contractionRankL C gs Θ Δ hn f =
  1 + ((selectedCopies C gs Θ).map
    (fun (x : At (repeated C gs ++ Θ) C) => f.rho .left x)).sum
```

`contractionRankR_eq` is the exact right-side counterpart. No upper copy is
discarded, and all children refer to that particular premise occurrence.

For `f : G P Γ (C :: Δ)` and `g : G P (C :: Θ) Λ`, the left cut rank is
`f.rho .right (At.here C Δ)`, the right cut rank is
`g.rho .left (At.here C Θ)`, and cutRank is their sum.
`cutRank_ge_two` and `cutRank_two_iff_leaves` need no topmost or atomization
hypothesis. `TiedRight/TiedLeft` are linked by proved equivalences to branching
nodes of the corresponding selected cluster, as in source pp.249–250.

`G.proofSize` counts all proof-tree nodes and justifies recursion. It is
distinct from cluster rho, the existing cutCount, and the later cut-elimination
measure. The naming was corrected during writing review; the final sources
were reverified afterward and the first passing run is retained in pre-naming/.
Readdressing a fixed proof/position changes only its address prefix and
preserves its rank. Equality reindexing also preserves rank. Neither theorem
asserts invariance under equal Reduced denotations or descent to quotient
arrows. No decrease under Atomic-k or an unconstructed transformation is claimed.

## Focused checked boundaries

The examples module supplies: distinct repeated-position roots; distinct
addresses for duplicated equal proof subterms; three selected upper offsets
`[0,2,3]` with an equal fixed formula at offset 1; empty-block exchange;
both literal signs; topI/botE/atomic-zero ranks; all four logical principal
leaf families; all four surviving cut-position embeddings and both consumed
cut heads. Binary route identities and partition laws check every residual
block, including empty ones. Constants are whole-formula positions even when
their literal-occurrence types are empty. No relation on literal occurrences
is used to prove ancestry, rank, or syntactic arrow equality.

## Verification and retained evidence

The final required run completed at `2026-10-23T05:10:02.544782+00:00`.
Baseline: **89 Lean files / 3,990 audited declarations**.
Final: **105 Lean files / 4,739 audited declarations**.

| Actual command | Exit | Elapsed |
| --- | --- | --- |
| Baseline: `uname -a` | 0 | 0.003 s |
| Baseline: `free -h` | 0 | 0.005 s |
| Baseline: `bash scripts/verify.sh` | 0 | 2.540 s |
| Final: `bash scripts/verify.sh` | 0 | 31.610 s |
| Final: `python3 scripts/check-audit-boundaries.py` | 0 | 5.988 s |
| Final: `python3 scripts/check-presentation-boundaries.py` | 0 | 1.104 s |
| Final: `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.007 s |
| Final: `git diff --check` | 0 | 0.007 s |

Both boundary scripts passed with all five required Lean exit-1 rejections:
public custom axiom; unused private custom axiom; hidden external axiom;
reflexive identification of distinct tagged projections; zero construction
without a correctly typed existing-arrow witness. Exact commands, diagnostics,
exit codes, fixture and log hashes are retained. Public import closure passed.
Manuscript v4 hashes passed. Whitespace is checked again after documentation
and staging, including new files.

The transitive audit permits only propext, Quot.sound and Classical.choice.
`predecessors_correct`, `cluster_correct` and `rho_eq` print propext/Quot.sound;
sourceArity_correct, rho_one_iff_leaf, contractionRankL_eq and
cutRank_two_iff_leaves additionally print Classical.choice. All sixty selected
prints are retained verbatim in SELECTED_AXIOMS.txt; all 4,739 declarations,
including private project declarations, are checked transitively. There are
no custom mathematical axioms, holes, native_decide, new generating equations,
coherence hypotheses or assumptions restating the construction.

Evidence directory: `provenance/wsl-gentzen-cluster-rank/`. It retains baseline
and final logs, timings, five controls, frozen-interface comparisons, exact
source inventory, 215 explicit new source declaration entries, and source
consultation/render hashes. The source-entry count differs from the audit's
environment count, which includes generated declarations.
Strict log SHA-256: `66288c7fa822d0cfcd470428f3876feceeaf40f2e597297183b20edaf0bcbb1a`.
SOURCE_SHA256SUMS SHA-256: `c7f503f3a1c66a08d3af715eae384a9716a5f16448f81cc8aaae103aaa748b42`.
EVIDENCE_SHA256SUMS SHA-256: `9608cab73ea1b6e4a0253bf6529c9d7b9683780ccb8208e39032eeedab28e0da`.

The strict log records baseline HEAD and hashes of the actual working Lean
sources. Those hashes match the final inventory. Committed-source checks
compare Git objects and working bytes with that same inventory; they are
separate from another build. Final commit/live SSH-ref/Downloads receipts are
in `.codex-work/gentzen-cluster-rank/` and the completion response identifies
the integration SHA and both report locations. Repository copies are retained;
Downloads copies preserve differing existing files and are checked byte for byte.

Required baseline/final checks ran sequentially. One overlap between two
exploratory target compilations of the final example was observed and recorded;
both ended before final verification. Complete exploratory timings/transcripts
are not retained as separate files; required command logs/timings are retained.
No independent kernel replay/source audit, Challenge/Solution or Comparator,
official preflight/service verification, manuscript recompilation/layout
review, publication, license or visibility change ran. The linked
[hostile review](reviews/GENTZEN_CLUSTER_RANK_HOSTILE.md) and
[writing review](reviews/GENTZEN_CLUSTER_RANK_WRITING.md) are author-side,
AI-assisted reviews, not independent certification.

## Next concrete obligation and remaining boundaries

The first concrete reducibility target is the right-thinning instance of
source (W 1), §11.2 printed p.251. For the actual implemented types, let:

```lean
C D : NormalForm P
gs : List (List (NormalForm P))
Θ Δ Λ : List (NormalForm P)
hn : 2 ≤ gs.length
f : G P (repeated C gs ++ Θ) (Δ ++ Λ)
```

Construct the two existing-rule terms:

```lean
h := G.contractL C gs Θ (Δ ++ D :: Λ) hn
       (G.thinR (repeated C gs ++ Θ) Δ Λ D f)
h' := G.thinR (gaps gs ++ C :: Θ) Δ Λ D
        (G.contractL C gs Θ (Δ ++ Λ) hn f)
```

Both have type `G P (gaps gs ++ C :: Θ) (Δ ++ D :: Λ)`.
Prove equality of their Reduced denotations, preservation of CutFree, and
the strict inequality between the **new contraction subterm's**
`contractionRankL C gs Θ (Δ ++ Λ) hn f` and the old contraction rank in h.
The expected difference is gs.length, from the parametric right-thinning
rank equation at every selected upper copy. This is a proposed next theorem,
not a declaration or result of this checkpoint. The denotation calculation
should use actual pre/postcomposition and associativity, not source
Semilattice Coherence as an assumed Lean theorem.

In parallel with these local reducibility instances, define the seven exact
blocked-left patterns (w γ1–3), (w ∧1), (w ∨1–3) on printed p.250 and their
right counterparts. `G.TiedRight/TiedLeft` already identify their candidate
sites in the selected clusters. Blocked predicates, proof replacement at an
address, the remaining (W 1)–(W 6) equations, all-site rank decrease,
Reducibility and Blocked-w remain open. Their constant/zero extensions are
separate checks (§11.5 p.273; §12.5 pp.291–292).


The cluster/rank prerequisite and tied-site characterization are complete.
The remaining G2 transformations, cut elimination, restricted positive
coherence inputs, PositiveCoherence, Reduced.Faithful, Boolean Coherence and
unconditional maximality remain open. Existing conditional transfers are
unchanged. An unformalized cited theorem is a Lean obligation here, not by
itself a mathematical defect in the manuscript or published source.
