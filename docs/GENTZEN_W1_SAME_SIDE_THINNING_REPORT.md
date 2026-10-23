# W1 same-side thinning at fixed positions

## Proved endpoints and hypotheses

Four fixed-parametric-position commutations compile for arbitrary `P : Type u`,
`C E : NormalForm P`, all displayed lists and an arbitrary premise, including
premises with cuts. The only arity hypothesis is `hn : 2 ≤ gs0.length`.
There is no inhabitant, decidable equality, enumeration, freshness, E≠C,
atomicity, CutFree, Atomized, coherence or equality-reflection premise.
Equality is in the existing equation-generated Reduced.Hom quotient.
`a ; b := comp a b` executes a first.

`W1.SameSideThinning.interior_left`, `interior_right`, `terminal_left` and
`terminal_right` prove the bundled output laws LeftLaws/RightLaws. These bundles
are proved results, not assumed interfaces. Their concrete GapInsertion data
constructors prove every context and numerical routing field. No abstract
square, selected-list transport or desired denotation equation is left as an
extra hypothesis of these four theorems.

For the interior gap define:

```lean
gs0 := pre ++ (U ++ V) :: post
gs1 := pre ++ (U ++ E :: V) :: post
tail0 := Θ
tail1 := Θ
upBefore := repeated C pre ++ U
upAfter := V ++ C :: (repeated C post ++ Θ)
loBefore := gaps pre ++ U
loAfter := V ++ (gaps post ++ C :: Θ)
```

For the terminal tail define:

```lean
gs0 := gs
gs1 := gs
tail0 := U ++ V
tail1 := U ++ E :: V
upBefore := repeated C gs ++ U
upAfter := V
loBefore := gaps gs ++ C :: U
loAfter := V
```

For each placement write U₀=upBefore++upAfter, U₁=upBefore++E::upAfter,
K₀=loBefore++loAfter and K₁=loBefore++E::loAfter. The constructors prove:

```text
upper0 : repeated C gs0 ++ tail0 = U₀
upper1 : repeated C gs1 ++ tail1 = U₁
lower0 : gaps gs0 ++ C :: tail0 = K₀
lower1 : gaps gs1 ++ C :: tail1 = K₁
count_eq : gs1.length = gs0.length.
```

These are genuine list equalities, used through G.reindex, At.cast and
Route.cast. No definitional associativity or unitality of binary formulas or
lists is assumed.

| Compiled case | Premise | Both old/new final proof types |
| --- | --- | --- |
| interior_left | G P ((repeated C pre ++ U) ++ (V ++ C :: (repeated C post ++ Θ))) Δ | G P ((gaps pre ++ U) ++ E :: (V ++ (gaps post ++ C :: Θ))) Δ |
| interior_right | G P Γ ((repeated C pre ++ U) ++ (V ++ C :: (repeated C post ++ Θ))) | G P Γ ((gaps pre ++ U) ++ E :: (V ++ (gaps post ++ C :: Θ))) |
| terminal_left | G P ((repeated C gs ++ U) ++ V) Δ | G P ((gaps gs ++ C :: U) ++ E :: V) Δ |
| terminal_right | G P Γ ((repeated C gs ++ U) ++ V) | G P Γ ((gaps gs ++ C :: U) ++ E :: V) |

The shared actual existing-constructor definitions are:

```lean
innerL := (G.contractL C gs0 tail0 Δ hn
  (f.reindex upper0.symm rfl)).reindex lower0 rfl
oldL := (G.contractL C gs1 tail1 Δ (modifiedArity d hn)
  ((G.thinL upBefore upAfter Δ E f).reindex upper1.symm rfl)).reindex lower1 rfl
newL := G.thinL loBefore loAfter Δ E innerL

innerR := (G.contractR Γ C gs0 tail0 hn
  (f.reindex rfl upper0.symm)).reindex rfl lower0
oldR := (G.contractR Γ C gs1 tail1 (modifiedArity d hn)
  ((G.thinR Γ upBefore upAfter E f).reindex rfl upper1.symm)).reindex rfl lower1
newR := G.thinR Γ loBefore loAfter E innerR
```

Here d is the fully constructed interior or terminal coordinate record.
`denoteL/R` prove `ofTerm new.denote = ofTerm old.denote` in all four cases.

## Baseline and preserved constructions

Main at `524cbe0c438ce3bcea8049758687c59d494bd597` was clean and agreed with
fetched SSH origin. Actual baseline strict verification passed: 121 Lean
files / 4,973 audited declarations, exit 0, 3.663 seconds. No unrelated work
or intervening commit was discarded. All preceding presentation, reduction,
normalization, factorization, zero/union, G0/G1, Atomic-k, clusters/rank and
opposite-side W1 constructions are reused unchanged.

Nine letters-only modules add 176 explicit source declarations (including
record declarations but not counting generated projections individually):
GentzenGapInsertionIndices/Data, GentzenInsertionPositions/Routing,
GentzenFixedContractionRanks, GentzenSameSideThinning/Ranks/Instances/Examples.
The root imports and 56 selected axiom prints are integrated. The exhaustive
audit counts 302 additional declarations including generated ones.
All older DosenPetric module bytes, manuscript v4, historical reports/reviews,
AGENTS, toolchain, manifest and dependency policy are preserved. Reduced has
21 term and 61 equation schemas, Positive 19, Gentzen 16; none changed.
Rewire, AtomicFormula, Atomized, CutFree, Topmost, predecessors and ranks are
unchanged. Lean remains 4.35.0 with an Init-only dependency closure.

## Source correspondence

The pinned source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA-256
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
including rendered p.251; pp.272–273 and 291–292 supply constant/zero context.
The verified caches and access artifacts are recorded in source-consultation.json.
Historical access records are preserved. No new source discrepancy was confirmed.

| Source location | Scope / positional condition | Lean construction and actual proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ=kL | Every displayed contracted copy remains parametric; insertion is in a specified fixed gap or terminal tail. | `GapInsertion.interior/terminal`; `W1.SameSideThinning.interior_left/terminal_left`, using the proved copies/thinning product square. |
| §11.2 p.252, right analogue of Reducibility, applied to W1 | Dual fixed-position kR/wR instance. | `interior_right/terminal_right`; independently typed coproduct square, with reversed route variance. |
| §11.2 pp.248–249, parametric cluster / all-node rank | An old position crosses thinning once; contraction sums all selected copies. | Complete singleton predecessors, `rho_thinL/R_embedded`, `selected_transport`, existing contractionRankL_eq/R_eq and selectedCopies_length. |
| §11.2 p.251 (W 2) | Inserted occurrence is selected for contraction. | Excluded here: `selected1_parametric` proves its index absent, even E=C. W2 remains open. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants/atomic zeros remain admitted; empty contexts retain their colours. | Existing unchanged syntax; actual constant proofs over Empty and arbitrary cut-containing premises are checked. |

The broader Semilattice Coherence invocation is replaced for these instances
by proved product/coproduct universal extensionality. Binary context folds,
generating equations and syntactic equality remain unchanged.

## Positional routing and categorical equality

`liftIndex k i` retains i below the specified gap and adds one otherwise.
The concrete numeric copyIndex lemmas prove the square by structural recursion
on the gap lists, with separate inserted-index and retained-index calculations.
Typed At extensionality then proves:

```text
c₀ : Route K₀ U₀       c₁ : Route K₁ U₁
u := tUpper : Route U₁ U₀
l := tLower : Route K₁ K₀
∀ A (a : At U₀ A), c₁.get (u.get a) = l.get (c₀.get a).
```

Both c routes are actual copies routes cast by lower/upper equalities.
Route.get selects a source position for each target position. Product p(w)
has type ante(source w)→ante(target w); coproduct q(w) has the reversed
object direction succ(target w)→succ(source w). Thus the proved equations are:

```text
p(c₁) ; p(u) = p(l) ; p(c₀) : ante K₁ → ante U₀
q(u) ; q(c₁) = q(c₀) ; q(l) : succ U₀ → succ K₁.
```

`product_positions` with `Route.product_get`, and `coproduct_positions` with
`Route.coproduct_get`, prove these equations component by component in
Reduced.Hom. These are previously derived universal properties, not occurrence
faithfulness or an assumed Semilattice Coherence theorem. Associativity alone
would not prove the square. Rewire has not been extended.

For arbitrary f, the left paths, with every intermediate type, are:

```text
old: ante K₁ --p(c₁)--> ante U₁ --p(u)--> ante U₀ --f.denote--> succ Δ
new: ante K₁ --p(l) --> ante K₀ --p(c₀)--> ante U₀ --f.denote--> succ Δ.
```

The right paths are:

```text
old: ante Γ --f.denote--> succ U₀ --q(u) --> succ U₁ --q(c₁)--> succ K₁
new: ante Γ --f.denote--> succ U₀ --q(c₀)--> succ K₀ --q(l) --> succ K₁.
```

`contractL_cast_denote/contractR_cast_denote` handle the actual transports;
`denoteL/R` apply the product/coproduct square and Reduced associativity.
No equality after inclusion or equality of relations is reflected to Reduced.

## Ordered positions, retained copy and inserted fixed fiber

The selected lists are exactly the original selectedCopies mapped by
At.cast upper0/upper1. The complete ordered equation is:

```text
selected1 = selected0.map tUpper.get.
```

`selected_transport` proves both membership directions and order, using
thin_old_position, injectivity, strict order of lifted indices and ordered_ext.
It does not deduplicate equal labels. `selected0_length/selected1_length`
retain every selected copy. `selected1_parametric` proves, for every entry,
its index differs from upBefore.length. E=C is allowed.

The retained positions are explicitly:

```text
keep0 = (At.shift (gaps gs0) (At.here C tail0)).cast lower0
keep1 = (At.shift (gaps gs1) (At.here C tail1)).cast lower1.
```

`retained` proves tLower.get keep0=keep1. Separately, for the new positions
zUpper=At.shift upBefore(here E upAfter) and
zLower=At.shift loBefore(here E loAfter), `inserted` proves c₁.get zUpper=zLower.
The old-position square alone does not cover zUpper.

`interior_inserted_before` proves zLower.index<keep1.index;
`terminal_inserted_after` proves keep1.index<zLower.index. The general
inserted_distinct includes the explicit formula transport if E=C.
`canonical_inserted_fiber` proves exactly the singleton [zUpper.cast upper1.symm]
in the canonical copies route above zLower.cast lower1.symm. It uses
fiber_copies_fixed after proving that this lower position is not retained;
it does not use an opposite-side contraction lemma.

## Exact local rank equations

Complete singleton predecessor lists at embedded old positions prove:

```text
rho(thinL f,left,tUpper.get a) = 1 + rho(f,left,a)
rho(thinR f,right,tUpper.get a) = 1 + rho(f,right,a).
```

The formula A and position a are arbitrary; exact At positions survive the
casts. Reindex rank lemmas transport the actual proof and position together.
Let n=gs0.length=gs1.length, Rnew be the existing contractionRankL/R of the
inner contraction, and Rold that of the modified contraction above thinning.
At x=keep1, each of the four concrete cases proves:

```text
Rold = Rnew + n
rho(new,x) = Rnew + 1
rho(old,x) + 1 = rho(new,x) + n
Rnew < Rold
rho(new,x) < rho(old,x).
```

`rankNewL/R_sum` and `rankOldL/R_sum` apply the complete existing contraction
sums to the casted selected lists. Ordered transport adds one thinning node
per selected copy; sum_map_one_add and selected0_length give the exact n.
The selected endpoint in old has rank Rold. Strict decrease uses n≥2.
The contraction subterm loses n nodes and the whole selected endpoint loses
n−1; these are different comparisons.

At zLower, `inserted_oldL/R_rank` and `inserted_newL/R_rank` give 2 and 1.
The old fixed-position fiber has the sole predecessor zUpper, whose thinning
rank is 1. The new thinning root is itself a leaf. These calculations apply
to either placement, including constants and compound E.
They are local syntactic cluster ranks, not cut rank, cutCount, proof size,
quotient invariants or all-site decrease under arbitrary replacement.

## Preservation and boundary checks

cutCountL/R, cutFreeL/R, atomizedL/R and relationL/R prove exact cutCount
equality, both predicate equivalences and equality of complete tagged
relations. Both Atomized predicates are exactly AtomicFormula E ∧ f.Atomized,
as separately proved by newL/R_atomized_iff and oldL/R_atomized_iff.
Constructing an atomized result from f.Atomized additionally needs AtomicFormula E;
the equality, rank theorems and equivalence do not. No premise is duplicated.
Relation equality is congrArg occurrenceMap of Reduced equality, never reversed.
Empty literal-occurrence types and repeated signed tags stay in its full types.
No unwitnessed zero or empty-sequent proof is added.

| Checked example | Exact boundary tested |
| --- | --- |
| repeated_left/right; repeated_selected_indices | Three selected copies, fixed equal gap and E=C. Original selected indices [0,2,3], modified [0,3,4], new upper index 2, new lower index 1, retained lower index 2. Whole selected endpoint loss is exactly 2. |
| before_left / between_right | Two copies, insertion before the first or between selected copies; empty gap halves and surrounding lists. |
| after_left/right; end_left/right | Insertion immediately after last copy or at the context end after an additional equal fixed tail formula. |
| gap_middle_left/right; tail_middle_left/right | Both halves of a fixed gap/tail are nonempty; all equal labels remain positional. |
| compound_left / compound_not_atomized | Compound E has unconditional denotation/rank laws; the resulting proof is correctly not Atomized. |
| emptyP_interior_left/right / emptyP_terminal_left/right | Four genuinely inhabited constant proof types over Empty, including bot-left and top-right thinning; no inhabitant assumption. |
| both_signs_actual_cut | Positive and negative literals in actual premises containing a G.cut; cutCount remains 1. |

The four unconditional laws bundles also include inserted 2→1, strict selected
rank decrease and full tagged relation preservation for each example.

## Verification and retained evidence

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 3.663 | `baseline.log` |
| `bash scripts/verify.sh` | 0 | 5.646 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 5.931 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 0.867 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.014 | `manuscript.log` |
| `git diff --check` | 0 | 0.01 | `diff-check.log` |

Final strict result: **130 Lean files / 5,275 audited declarations**; public
import closure passes. All five negative controls are rejected with Lean exit 1
and expected diagnostics:

| Fixture | Expected rejection | Outcome |
| --- | --- | --- |
| direct-axiom | Public custom axiom is unpermitted. | Rejected, exit 1. |
| private-axiom | Even unused private custom axiom is unpermitted. | Rejected, exit 1. |
| hidden-dependency | External hidden axiom dependency is unpermitted. | Rejected, exit 1. |
| identified-projections | Distinct tagged projections cannot be identified by rfl. | Rejected, exit 1. |
| zero-without-arrow-witness | Zero construction lacks a correctly typed existing-arrow witness. | Rejected, exit 1. |

Permitted axioms remain propext, Quot.sound and Classical.choice. The complete
transitive audit and 56 selected axiom prints are retained; no choice-free
claim is made. Production contains no proof holes, custom mathematical axioms
or native_decide. Negative fixtures stay outside production imports.
All heavy processes, including exploratory compilations, ran sequentially.
Failed numeric/list/dependent-position elaborations, the explicit hn binder
repair, fixed-position rewriting correction and example conjunction arity
correction retain original logs, exits and timings. No target was weakened.
The last strict run followed all final Lean changes; later edits are records only.

Evidence directory: `provenance/wsl-gentzen-w1-same-side-thinning/`.
DECLARATIONS.txt gives all 176 explicit declaration signatures with source
line anchors. SOURCE_SHA256SUMS inventories every checked Lean file, pinned
configuration and scripts. EVIDENCE_SHA256SUMS inventories logs, control
sources/results, source-access artifacts and boundary records. REPORT_SHA256SUMS
and RECORD_SHA256SUMS inventory final reports and current maps/README.

- Strict log: `54772ed9d83904a76b29d71e97122e16a555de6c602e8fba1add344bcb32e72b`.
- Checked source inventory: `c891b846d7952e8303379ee73f0b60dcb6a84e70f9e3fc94330b7cea06a8e2fa`.
- Evidence inventory: `3438394fcccae7d4dbf8fb8237f751ed08b02897195e56af2af098d1013b8286`.

Baseline, checked working sources and final committed sources are distinct
records. Committed-source.json, delivery.json and remote-final.json under
.codex-work/gentzen-w1-same-side-thinning/ hold post-commit inventory/ref and
Downloads checks, avoiding a circular commit hash inside its own reports.
Copies preserve differing existing filenames using dates/commit suffixes and
are compared byte-for-byte with committed Git objects.

Both reviews apply to actual code, statements and correspondence and are
AI-assisted author-side reviews, not independent certification. The writing
review consulted the verified Knuth–Larrabee–Roberts cache directly. Manuscript
v4 and historical access records remain unchanged; no review/process prose
was added to manuscript text or LaTeX comments.
Independent kernel replay, exhaustive independent source audit,
Challenge/Solution/Comparator, official preflight/service verification,
manuscript recompilation/layout review, publication, license and visibility
changes were not performed. The repository remains private. See the
[hostile review](reviews/GENTZEN_W1_SAME_SIDE_THINNING_HOSTILE.md) and
[writing review](reviews/GENTZEN_W1_SAME_SIDE_THINNING_WRITING.md).

## Next concrete obligation

Next prove same-side exchange within a specified fixed parametric gap,
together with its right dual (§11.2 p.251 W1, γ=cL; p.252 dual).
For arbitrary C, pre,post,U,X,Y,V,Θ, set:

```text
gs0 = pre ++ (U ++ X ++ Y ++ V) :: post
gs1 = pre ++ (U ++ Y ++ X ++ V) :: post
upperPrefix = repeated C pre ++ U
upperTail = V ++ C :: (repeated C post ++ Θ)
lowerPrefix = gaps pre ++ U
lowerTail = V ++ (gaps post ++ C :: Θ).
```

Require 2≤gs0.length. With `f : G P (upperPrefix ++ X ++ Y ++ upperTail) Δ`,
compare left contraction at gs1 after
`G.exchangeL upperPrefix X Y upperTail Δ f` against
`G.exchangeL lowerPrefix X Y lowerTail Δ` after contraction at gs0,
using proved list equalities and G.reindex. The final antecedent is
`lowerPrefix ++ Y ++ X ++ lowerTail`. The right dual starts with
`f : G P Γ (upperPrefix ++ X ++ Y ++ upperTail)` and uses exchangeR/contractR.
Every selected copy must lie outside the exchanged X/Y blocks; here the blocks
are inside the fixed gap, so this must be proved from positions, not assumed
from formula labels. Empty blocks and fixed equal copies are allowed.
Use actual exchange comparison directions: exchangeL precomposes invTerm,
exchangeR postcomposes toTerm. Prove the copies/exchange component square,
complete ordered selected-position transport, exact local rank equations and
preservation. The existing At.swapBlocks and exchangeBack_component are
available; no new Route/Rewire constructor or coherence assumption is supplied.
Include the analogous fixed terminal-tail placement if extending that scope.

Other same-side W1 contractions/logical parametric cases, W2–W6, arbitrary
proof-context replacement/all-site decrease, Reducibility, Blocked-w and cut
elimination remain open. Positive coherence inputs, PositiveCoherence,
Reduced.Faithful, Boolean Coherence and unconditional maximality are separate
obligations. Existing conditional transfers remain unchanged. An unformalized
published theorem is not by itself an established manuscript defect.
