# W3 shared-selected contraction fusion

## Exact proved endpoint and hypotheses

Two contractions fuse into one when the outer contraction selects the retained
inner occurrence. The left result and its separately typed right dual are proved
in the unchanged Reduced category. This is source W3, not a disjoint W1 commutation.

Let `P : Type u` be arbitrary, `C : NormalForm P`, `gs hs` gap lists and Θ,Λ
context lists. Put n=gs.length, m=hs.length and

```text
F = repeated C gs ++ Θ
I = gaps gs ++ C :: Θ
K = gaps hs ++ C :: Λ.
```

Inputs are independent bounds n,m≥2, an identification
`hI : repeated C hs ++ Λ = I`, and the positional condition

```text
At.shift (gaps gs) (.here C Θ) ∈
  (selectedCopies C hs Λ).map (At.cast hI).
```

The last condition says that the retained inner position is selected by the
outer contraction. It is not a routing, denotation or rank conclusion. No
atomicity, CutFree, Atomized, nonempty-variable, decidable-equality, enumeration,
coherence or equality-reflection hypothesis is required. Premises may contain cuts.

`W3.SharedContraction.fusion_left/right` quantify over the original data and
these hypotheses. For each existing f:G P F Δ or f:G P Γ F, inner applies the
actual gs/Θ contraction. Old applies the actual hs/Λ contraction to inner,
using hI to reindex the intermediate context. Flat applies one constructed
contraction directly to f. The exact result types and principal equalities are:

```text
left:  oldL,flatL : G P (gaps hs ++ C :: Λ) Δ
right: oldR,flatR : G P Γ (gaps hs ++ C :: Λ)

ofTerm flatL.denote = ofTerm oldL.denote
ofTerm flatR.denote = ofTerm oldR.denote.
```

The left arrows have type `Hom (ante K) (succ Δ)`; the right arrows have type
`Hom (ante Γ) (succ K)`.
Composition a;b applies a first. Actual G.contractL/R and G.reindex implement
both constructions; no arrow-negation operation is invoked for the dual.

## Baseline and preserved interfaces

The clean baseline is main `1ef1c8226ae1d5b3da102c243e4e555525b19bea`, matching
fetched SSH origin. Fresh baseline verification passed: 171 Lean files and
6,705 audited declarations, exit 0, 11.879 seconds. The retained integration
stash is unchanged. No other checkout or unrelated work was modified.

Eight new modules implement the result:

| Module group | Function |
| --- | --- |
| GentzenContractionSelection and Coordinates | Nonempty positional selections, recursive fusion, computed gaps/tail and conversion to the existing ContractionBlock. |
| GentzenRouteFiberSums | Complete composite-fiber permutation and finite weighted-sum law; contraction ranks expressed by actual fibers. |
| GentzenSharedContractionData | Original gs/hs descriptions and hI, positional hypothesis, concrete fused block, full route and selected/fixed-fiber laws. |
| GentzenSharedContractionCommutation | Correctly variant structural equations, both Reduced equalities and preservation. |
| GentzenSharedContractionRanks | Complete selected sums, both exact rank drops and other-position laws. |
| GentzenSharedContractionInstances and Examples | Exact public endpoints and inhabited positional boundaries. |

The new production closure is still Init-only; Init.Data.List.Perm supplies
the finite permutation API. No dependency package or manifest change is needed.
Lean 4.35.0 remains pinned. Every older DosenPetric module, syntax/equation,
denotation, occurrence tag, predecessor/rank definition and analysis predicate
is byte-preserved. Existing Lean edits only add root imports and 98 selected
axiom prints. Manuscript v4/v5, diagrams, references, checksums, AGENTS, earlier
reports/reviews and historical source-access records are preserved.

## Source correspondence

The directly consulted source is Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, cached from
[the full source PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed pp.248–253 are PDF pp.260–265, one-based. Printed p.251 was inspected
in rendering and its W3 statement was checked against the typed inputs.

| Source location | Condition or calculation | Lean result |
| --- | --- | --- |
| §11.2 p.251, W3: two descriptions of the same basic sequence | The lower gs context equals the upper hs context. | Data.identify and the actual outer ContractionBlock cast. |
| p.251, W3: outer selection includes the retained inner occurrence | Select the position, not all occurrences with the same label. | Data.Shared, shared_pattern and the explicit hypothesis of fusion_left/right. |
| p.251, W3: two contractions equal one with suitable subscripts | Construct those subscripts from the original data. | ContractionSelection.fuse; upper/lower/count; Data.flat, square and both principal equalities. |
| pp.248–249 and p.251, W3 ranks | Old retained rank exceeds the fused rank by the outer arity m. | selected_sumsL/R, outer_rankL/R and retained_rankL/R. |
| p.252, right analogue | Same shared-selected configuration on succedent positions. | Separately typed contractR, coproduct, rank and preservation proofs. |

No source coherence appeal is treated as a Lean proof. No new source discrepancy
is asserted. The local fusion does not supply the replacement and multiset
arguments required for Reducibility and Blocked-w on pp.250–253.

## Constructed selection, endpoints and complete fibers

`ContractionSelection C F K` has three coordinate constructors. Last retains
the final selected C and its tail; fixed preserves an unselected head tag;
more deletes an earlier selected C. It is an auxiliary positional syntax,
not a new Gentzen rule or defining equation. Its first gap, remaining gaps and
tail are computed. Upper/lower prove that its existing ContractionBlock has
exactly source F and target K; count identifies its arity.

Every nonempty original gap list converts to this syntax. Conversion back to
ContractionBlock recovers the original gap list, tail, endpoints, route, retained
position and complete selected list. Thus it does not restrict the arbitrary
input gs/hs. Data stores only C,gs,hs,Θ,Λ and hI; Shared is the separately
supplied placement hypothesis. No desired fusion law is stored as a field.

Fusion is structural recursion on the inner selection and the matching outer
selection. Earlier inner selections remain selected. At an inner fixed head,
an outer selected head becomes selected in the fused input, and an outer fixed
head remains fixed. When the inner retained occurrence is reached, the outer
selection supplies the rest. The hypothesis excludes an outer fixed treatment
of the required shared occurrence. The resulting actual gap list satisfies

```text
flat.gs.length + 1 = n + m,
flat.selected.length + 1 = n + m.
```

Consequently both lengths are n+m−1; flat_bound proves the constructor bound.
For inner route r:Route I F, outer route s:Route K I and flat route t:Route K F,
the all-position identity is `t.get a = s.get (r.get a)`. The flat retained
position is exactly the outer retained position. Complete selected membership is

```text
a ∈ flat.selected ↔ r.get a ∈ outer.selected.
```

`selected_originals` identifies this complete ordered family with all original
inner selected positions and the unique fixed originals of the other outer
selected positions. Both the ordering and exact length are proved. Labels are
never searched, identified or deduplicated. For every other final position z,
the outer fixed inverse is distinct from the inner retained position. Taking
the inner fixed inverse then gives original(z). Both complete route fibers
at z are [original(z)]; the retained composite fiber is the entire flat.selected.

The universal component laws give

```text
outer.product ; inner.product = flat.product : ante K → ante F
inner.coproduct ; outer.coproduct = flat.coproduct : succ F → succ K.
```

Actual contraction denotations and associativity then prove Reduced equality.
Neither occurrence equality nor inclusion equality is reflected back into it.

## Exact rank calculation and preservation

For any existing premise f, each inner endpoint rank is one plus the sum over
its complete original fiber. The outer selected family contains the retained
inner position once and m−1 other positions. The retained branch contributes
its inner contraction root; every other branch contributes its parametric
inner node. Thus all m extra intermediate nodes must be counted.

The grouped original fibers can have a different order from the ordered fused
selection. `fiber_comp_perm` proves a permutation, not a false ordered-list
identity. `sum_fiber_comp` therefore proves the complete weighted-sum equality.
Separately on each sequent side:

```text
sum of inner ranks over outer.selected
  = sum of f ranks over flat.selected + m

outer contraction-subterm rank = flat contraction-subterm rank + m
rho(old,retained) = rho(flat,retained) + m
rho(flat,retained) < rho(old,retained).
```

For every other final position z, at the computed common original a:

```text
rho(old,z)  = 2 + rho(f,a)
rho(flat,z) = 1 + rho(f,a).
```

These are local syntactic ranks. They are not quotient invariants or an
arbitrary-context/all-site reducibility or termination proof.

Both old and flat have exactly f.cutCount. Each CutFree predicate and each
Atomized predicate is equivalent to f's, without an atomicity hypothesis.
Complete tagged relations are equal by applying occurrenceMap to the proved
Reduced equalities. Empty literal-occurrence types do not remove whole-formula
constant positions, and no arrow is supplied to an empty hom-set.

## Inhabited boundary examples

For twoThree C, gs=[[],[C]], hs=[[C],[],[]], Θ=[C,C,C], Λ=[C]. All six
source labels equal C, but inner selected indices are [0,2] and outer selected
indices are [1,2,3]. The checked maps are:

```text
inner:    [1,0,1,2,3,4]
outer:    [0,1,1,1,2]
composite and flat: [1,0,1,1,1,2]
flat gaps: [[],[C],[],[]]
flat selected indices: [0,2,3,4].
```

The equal-labelled unselected source tags 1 and 5 are computed as the unique
originals of final fixed tags 0 and 2. Both satisfy the old/flat rank loss of one.

For threeTwo C, n=3,m=2 and the shared inner retained position is the last
outer selected position. Flat has four empty gaps, selected indices [0,1,2,3]
and composite map [0,0,0,0,1]. MiddleThree places the shared position in the
middle of a three-element outer selection; twoThree places it first. Actual
left/right proofs cover all these placements and the n=m=2 empty-gap/tail case.
Nonempty internal gaps and tails are included.

Empty-variable constants inhabit both sides, including the exact retained
drop by three. Compound C with n=3,m=2 also has actual left/right premises.
Literal examples quantify over either sign; actual positive-left and
negative-right cut-containing premises retain cutCount=1. These examples are
not statements over impossible premises.

## Verification, reviews and delivery evidence

The final strict build/transitive audit passes with **179 Lean source files
and 7,069 audited declarations**, adding 364 audited declarations. The 98 new
selected axiom prints supplement the complete audit. Public import closure
passes. Only propext, Quot.sound and Classical.choice are permitted; no
choice-free claim is made.

Final sequential command results are retained in the timestamped final JSON:

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 6.084 |
| python3 scripts/check-audit-boundaries.py | 0 | 20.468 |
| python3 scripts/check-presentation-boundaries.py | 0 | 1.890 |
| sha256sum -c SHA256SUMS, in manuscript/ | 0 | 0.020 |
| git diff --check | 0 | 0.008 |
| git diff --cached --check | 0 | 0.010 |

All five controls reject with expected diagnostics and Lean exit 1: direct
custom axiom, unused private custom axiom, hidden external axiom, identification
of distinct tagged projections by rfl, and zero without a correctly typed
existing-arrow witness. All heavy checks were sequential. Exact public types,
input-record prints, source hashes, declarations, control sources/logs and
baseline/final/version evidence are retained. Failed syntax, dependent rewrite,
At/Place, arity elaboration and exact-argument attempts are preserved. No
heartbeat limit, interface or target was weakened; final example compilation
passed in 85.205 seconds.

Evidence is retained under `provenance/wsl-gentzen-w3-shared-selected-contraction/`
and `.codex-work/gentzen-w3-shared-selected-contraction/`. The
[hostile review](reviews/GENTZEN_W3_SHARED_SELECTED_CONTRACTION_HOSTILE.md) and
[writing review](reviews/GENTZEN_W3_SHARED_SELECTED_CONTRACTION_WRITING.md)
cover actual proofs and current correspondence; they are author-side
AI-assisted reviews, not independent certification. Separate receipts record
checked-versus-committed source, SSH refs and Downloads byte comparisons.
This report does not contain its own final commit hash.

No independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
publication, license or visibility action ran.

## Next concrete proof obligation

Prove source W2 selected thinning at the terminal position and its right dual:
append a new C to F, contract that occurrence together with the original
gs-selected copies, and compare with contracting gs on f and exchanging the
retained C past Θ. The ready-to-paste task is
[CODEX_W2_SELECTED_THINNING.txt](CODEX_W2_SELECTED_THINNING.txt). Keep the
different Atomized boundaries explicit: old requires AtomicFormula C and
f.Atomized; new is equivalent to f.Atomized.

Disjoint interleaving, remaining exchange/W1/W2–W6 cases, arbitrary-context
replacement, Reducibility, Blocked-w, cut elimination, restricted coherence
inputs, PositiveCoherence, Reduced.Faithful, Boolean Coherence and unconditional
maximality remain separate/open. Existing conditional transfers and the three
milestones are unchanged. An unfinished reconstruction of published results
does not establish a manuscript defect.
