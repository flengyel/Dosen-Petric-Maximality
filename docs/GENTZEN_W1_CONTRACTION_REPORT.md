# W1 opposite-side contraction commutation and directed ranks

## Proved endpoint and exact hypotheses

For arbitrary `P : Type u`, `C D : NormalForm P`,
`gs hs : List (List (NormalForm P))`, `Θ Λ : List (NormalForm P)`,
`hn : 2 ≤ gs.length`, `hm : 2 ≤ hs.length` and:

```lean
f : G P (repeated C gs ++ Θ) (repeated D hs ++ Λ)
```

one commuting pair is constructed in
`DosenPetric.Reduced.Gentzen.W1.Contraction`:

```lean
innerL := G.contractL C gs Θ (repeated D hs ++ Λ) hn f
innerR := G.contractR (repeated C gs ++ Θ) D hs Λ hm f
outerL := G.contractL C gs Θ (gaps hs ++ D :: Λ) hn innerR
outerR := G.contractR (gaps gs ++ C :: Θ) D hs Λ hm innerL
```

Both outer proofs have exactly type:

```lean
G P (gaps gs ++ C :: Θ) (gaps hs ++ D :: Λ)
```

`denote` proves `ofTerm outerR.denote = ofTerm outerL.denote` in the existing
syntactic Reduced.Hom quotient. `denote_reverse` is its symmetry, not a second
construction. Composition `a ; b := comp a b` executes a first.
No inhabitant, decidable equality, enumeration, freshness, atomicity,
Atomized, CutFree, equality reflection, coherence or arrow-negation hypothesis
is needed. C=D and independent arities are permitted, with arbitrary premises
including cuts. Zero arrows still require an existing-arrow witness.

## Baseline and preserved interfaces

Main was clean at `5c0a77f1e1ebf893e1aeda1fbb208f2a4a90e8de` and agreed with
fetched SSH origin. Actual baseline strict verification exited 0 in 3.423
seconds: 113 Lean files / 4,850 audited declarations. No newer or unrelated
work was reset/discarded. All earlier presentation, reduction, factorization,
zero/union, G0/G1, Atomic-k, cluster/rank and W1 thinning/exchange results are
reused unchanged.

Four letters-only modules are added: GentzenOppositeContractionRank,
GentzenContractionCommutation, GentzenContractionCommutationRank and
GentzenContractionCommutationExamples, with root imports and 32 selected
axiom prints. Every older DosenPetric module is byte-identical, including the
21 reduced constructor/61 equation/19 Positive/16 Gentzen schemas, all proof
predicates, predecessor definitions and existing rank definitions. leftRank
and rightRank below are aliases for the existing contraction ranks, not
replacements. Lean 4.35.0, Init-only dependencies/manifest, audit scripts,
AGENTS, manuscript v4 and historical reports/access records are preserved.
Boundaries.json records all byte comparisons.

## Source correspondence

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n corresponds to PDF page n+12, one-based. Printed pp.248–253 were
consulted, with p.251 also inspected in rendering. Constant and atomic-zero
extensions on pp.272–273 and 291–292 were checked against the existing
syntax. Access artifacts/hashes are retained; historical access records are
unchanged. No new source discrepancy was confirmed.

| Source location | Precisely used construction / condition | Lean correspondence / proof |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = wR | Move a left contraction through an opposite-side right contraction: wL wR f = wR wL f, with independent selected-copy lists. | `W1.Contraction.innerL/innerR/outerL/outerR`; `denote` uses actual pre/postcomposition and Reduced.Laws.assoc, not Semilattice Coherence. |
| §11.2 p.252, right-directed analogue of Reducibility | The same equality is used in reverse when targeting the right contraction. | `denote_reverse` is symmetry of denote; separate `right_directed_balance/decrease` prove the targeted right rank claim. No duplicate pair or arrow-negation construction. |
| §11.2 p.248, parametric sequences / clusters | A contraction has one proof premise. A position on its opposite side has one predecessor; its own lower contraction position branches to all selected upper copies. | `G.predecessors_contractR_left/contractL_right`, `rho_contractR_left/contractL_right`; existing parent/fiber and complete contraction-sum APIs. |
| §11.2 p.249, contraction rank; pp.251–252, directed rank requirement | Count all ancestry nodes, independently for the n selected left copies and m selected right copies. | `outerL_left/outerR_left/outerL_right/outerR_right`, inner-rank inequalities, two directed balances/decreases and named other-side increases. |
| §11.2 p.253, multiset-ordering argument for Blocked-w | Later elimination concerns contractions tied to a chosen cut and all affected sites; the displayed two-rank sum is not a supplied decreasing measure. | Only `endpointSum_balance` and equality for equal arities are proved. No all-site replacement, multiset measure, Reducibility or Blocked-w result is claimed. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants have whole-formula positions; atomic-zero bases are permitted and thinnings retained. | Arbitrary C,D/f in the theorem, actual constantTop/constantBot at Empty P, unchanged zero grammar and witnessed-zero policy. No new zero-specific equation is needed. |

The source's broader Semilattice Coherence appeal is not a Lean proof input.
These local instances follow from existing categorical equations and typed
ancestry. Context folds remain binary and explicitly typed; no strictification
or relation-kernel quotient is introduced.

## Denotation and intermediate types

The actual denotations use this path:

```text
ante (gaps gs ++ C :: Θ)
  -- a := (copies C gs Θ).product --> ante (repeated C gs ++ Θ)
  -- f.denote --> succ (repeated D hs ++ Λ)
  -- b := (copies D hs Λ).coproduct --> succ (gaps hs ++ D :: Λ).
```

OuterL denotes `a ; (f ; b)` and outerR `(a ; f) ; b`. Expanding actual
G.denote and ofTerm_comp reduces the equality to Reduced.Laws.assoc.
Its reverse is equality symmetry. No source coherence theorem, relational
calculation or inclusion equality is used to establish this quotient equality.

## Opposite-side predecessors and four rank equations

The helpers `G.predecessors_contractR_left` and
`G.predecessors_contractL_right` quantify every opposite-side At position
of every formula, not just the two selected positions used later. They
unfold the actual branches/parent route and apply TraceRoute.fiber_identity
to prove complete singleton predecessor lists storing the same At.
Applying rho_eq gives:

```text
rho(contractR f,left,x)  = 1 + rho(f,left,x)
rho(contractL f,right,y) = 1 + rho(f,right,y).
```

A contraction has one proof premise. Its own selected ancestry branches,
while an opposite-side position has one predecessor; that contribution is
not multiplied by the opposite contraction's arity.

Let n = gs.length and m = hs.length, independently. Define:

```lean
x := At.shift (gaps gs) (At.here C Θ)
y := At.shift (gaps hs) (At.here D Λ)
L := G.contractionRankL C gs Θ (repeated D hs ++ Λ) hn f
R := G.contractionRankR (repeated C gs ++ Θ) D hs Λ hm f
```

The new aliases leftRank/rightRank name L/R respectively. The exact checked
equations are:

| Declaration | Equation |
| --- | --- |
| outerL_left | `rho(outerL,left,x) = L + n` |
| outerR_left | `rho(outerR,left,x) = L + 1` |
| outerL_right | `rho(outerL,right,y) = R + 1` |
| outerR_right | `rho(outerR,right,y) = R + m` |

For outerL_left, use contractionRankL_eq and map every selected left upper
copy through the opposite-side right-contraction equation. Sum one extra
node for each selectedCopies C gs Θ entry, using sum_map_one_add and its
exact length gs.length. For outerR_right, do the independent calculation on
selectedCopies D hs Λ of length hs.length. The other two equations cross
only one outer proof constructor. No n=m assumption or product n*m appears.
Fixed equal formulas in gaps remain distinct from selected upper copies.

## Two directed comparisons and the sum boundary

The checked consequences are:

```text
innerL_rank_lt_outerL: L < rho(outerL,left,x)
innerR_rank_lt_outerR: R < rho(outerR,right,y)
left_directed_balance:
  rho(outerL,left,x) + 1 = rho(outerR,left,x) + n
right_directed_balance:
  rho(outerR,right,y) + 1 = rho(outerL,right,y) + m
left_directed_decrease:
  rho(outerR,left,x) < rho(outerL,left,x)
right_directed_decrease:
  rho(outerL,right,y) < rho(outerR,right,y).
```

The left-directed move outerL → outerR lowers the targeted left endpoint
by n−1 and raises the displayed right endpoint by m−1. The reverse move
outerR → outerL targets the right endpoint, lowering it by m−1 and raising
the left by n−1. `left_directed_right_increase` and
`right_directed_left_increase` explicitly name the other-side increases.
The addition equations avoid truncated subtraction. All strictness follows
from the two arity lower bounds. Inner contraction ranks lose n or m nodes
relative to the corresponding old outer selected rank; the whole selected
endpoint comparisons lose n−1 or m−1.

Define endpointSum g as the sum of just these two selected final-position
ranks. `endpointSum_balance` proves:

```text
S(outerL) + m = S(outerR) + n.
```

`endpointSum_eq_of_lengths_eq` proves equality when n=m. For n=2,m=3 the
left-directed move raises S by one, as checked in two_three_effects. Thus S
is not asserted to be a general decreasing measure. Neither reverse
orientation is registered as an unrestricted terminating rewrite system.
Ranks remain attached to syntax; no quotient invariance, arbitrary-context
replacement or all-site decrease is claimed. Cluster rank, contraction rank,
cut rank, cutCount and proofSize remain distinct.

## Preservation, occurrences and checked examples

`cutCount`, `cutFree`, `atomized` and `relation` prove:

```text
outerR.cutCount = outerL.cutCount
outerR.CutFree ↔ outerL.CutFree
outerR.Atomized ↔ outerL.Atomized
outerR.relation = outerL.relation.
```

The first three are definitional: both contractions retain the same premise
once, and both atomization predicates reduce to f.Atomized. There is no
new AtomicFormula condition. The complete tagged relation equality follows
by congrArg occurrenceMap from the proved Reduced equality, never conversely.
No literal-occurrence inhabitant is needed for constants; whole-formula
ancestry is not confused with the literal-occurrence interpretation.

| Boundary | Checked construction and statement |
| --- | --- |
| Independent n=2,m=3, empty gaps/tails, C=D, actual cut | twoThreePremise/L/R and two_three_effects prove denotation equality, left endpoint loss 1, right endpoint rise 2, S rise 1 and cutCount 1. |
| Equal n=m=3 and fixed equal gaps on both sides | repeatedPremise/L/R have source and target four equal literal formulas; gs=hs=[[],[lit l],[]]. repeated_sum_unchanged proves exact sum equality; repeated_left_decreases_right_increases checks both strict comparisons at the explicit selected lower positions. |
| Selected versus fixed equal positions | selected_indices computes [0,2,3]; fixed_equal_not_selected excludes the actual upper index 1 from that complete list. The same typed list applies to both sides of the repeated example, without label-based deduplication. |
| Empty variable type and constants | constantTop : G Empty [top,top] [top,top,top] and constantBot : G Empty [bot,bot] [bot,bot,bot] are actual inhabited proof types. emptyP_top checks denotation equality; emptyP_bot checks the directed left rank inequality. |
| Both signs and actual cuts | All literal examples quantify any Literal P. both_signs_with_cut instantiates a positive and a negative literal and retains cutCount 1. Their premises contain G.cut of two atomic identities. |

## Verification and evidence

| Command | Exit | Elapsed seconds | Evidence log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 4.335 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 9.204 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.515 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.011 | `manuscript.log` |
| `git diff --check` | 0 | 0.014 | `diff-check.log` |

Final verification completed at 2026-10-23T12:37:59.126131+00:00: **117 Lean
files / 4,906 audited project declarations**. The new modules have
47 explicit source declarations; generated/environment declarations are a
different count. All heavy builds/audits, including exploratory compilation,
were sequential. Final verification followed the last proof changes.

All five expected negative controls were rejected with Lean exit 1 and the
expected diagnostics: public custom axiom, unused private custom axiom,
hidden external axiom dependency, reflexive identification of distinct tagged
projections, and zero construction without a correctly typed existing-arrow
witness. Exact fixtures, logs, commands and hashes are retained in the two
control directories. Public import closure passed; its letters-only parser
and all generating equations are unchanged.

The first exploratory build compiled the general theorems but rejected two
example proof scripts: an unfolded endpointSum proof alias was treated as a
separate arithmetic expression, and List.mem_map_of_mem needed its function
as an implicit named argument. Explicit endpointSum terms and `(f := At.index)`
resolved these. Failed and passing attempt logs, exits and times are retained;
no failed attempt is described as a pass.

Permitted axioms remain propext, Quot.sound and Classical.choice. denote,
denote_reverse and relation print propext and Quot.sound; rank results also
print Classical.choice via existing fiber infrastructure. cutCount/CutFree/
Atomized comparisons print no axioms. SELECTED_AXIOMS.txt retains 32 complete
prints, including wrapped lines. No choice-free claim is made. Production
contains no proof holes, custom mathematical axioms, native_decide, new
presentation equations or coherence premises. Deliberately invalid controls
remain outside production imports.

Evidence is retained in `provenance/wsl-gentzen-w1-contraction/`:
summary.json, baseline.json, verify.json and exploratory records retain
commands, exits, timings and hashes; DECLARATIONS.txt lists all added
statements; SOURCE_SHA256SUMS records checked Lean/toolchain/dependency/script
bytes; EVIDENCE_SHA256SUMS hashes supporting material. REPORT_SHA256SUMS and
RECORD_SHA256SUMS separately hash final reports and current maps/README.

- Strict log: `3633471766b5bdeabe81e0d917de9623365b14d9de5a95c659b6d0495aa02a4d`.
- Checked source inventory: `ae0b43ccb49428cd958da38f5e0a8e2374989f600b037c56d1f5ba4b1c125234`.
- Evidence inventory: `161b9e72f55a3387c28153147b9a8d003cbcaaa9ada8b4619c4e19afa40c33f1`.

Baseline, checked working sources and committed source bytes are separate
records. After committing, sources/evidence/reports are compared against
these inventories. Runtime committed-source.json, delivery.json and
remote-final.json are retained in .codex-work/gentzen-w1-contraction/;
these avoid a self-referential commit hash. Downloads copies preserve differing
existing files with dated/commit suffixes and are compared with committed bytes.

Both reviews apply to the actual construction and source correspondence and
are explicitly author-side, not independent certification. The verified
cached Knuth–Larrabee–Roberts text was directly consulted. Historical reports,
source-access records and manuscript v4 are preserved. No independent kernel
replay, exhaustive independent source audit, Challenge/Solution/Comparator,
official preflight/service verification, manuscript recompilation/layout
review, publication, license or repository-visibility change ran. See
[the hostile review](reviews/GENTZEN_W1_CONTRACTION_HOSTILE.md) and
[the writing review](reviews/GENTZEN_W1_CONTRACTION_WRITING.md).

## Next concrete unproved W1 case

The next concrete unproved W1 case is left contraction commuting with right
disjunction introduction (p.251, γ = ∨R), and the dual right contraction
commuting with left conjunction introduction. For arbitrary A,B,C,
gs, Θ,Δ,Λ and hn : 2 ≤ gs.length, take:

```lean
f : G P (repeated C gs ++ Θ) (Δ ++ A :: B :: Λ)
```

Compare:

```lean
G.contractL C gs Θ (Δ ++ .disj A B :: Λ) hn
  (G.disjR (repeated C gs ++ Θ) Δ Λ A B f)
G.disjR (gaps gs ++ C :: Θ) Δ Λ A B
  (G.contractL C gs Θ (Δ ++ A :: B :: Λ) hn f)
```

Both have type `G P (gaps gs ++ C :: Θ) (Δ ++ .disj A B :: Λ)`.
Prove Reduced denotation equality, proof-property preservation and the
selected left rank equations using the unchanged-side singleton predecessor.
For the dual use `f : G P (Γ ++ A :: B :: Θ) (repeated C gs ++ Λ)` and
compare contractR(conjL f) with conjL(contractR f), at exactly
`G P (Γ ++ .conj A B :: Θ) (gaps gs ++ C :: Λ)`.
The logical principal formula on the changed side is a new whole-formula
leaf; do not trace it into A/B or infer that side's rank from denotation.

Other W1 cases, W2–W6, blocked-contraction transformations, arbitrary proof
replacement/all-site decrease, Reducibility, Blocked-w, the rest of G2 and
cut elimination remain open. Positive coherence inputs, PositiveCoherence,
Reduced.Faithful, Boolean Coherence and unconditional maximality remain
separate/open; reuse the existing conditional transfers. A missing Lean
construction of a cited theorem does not by itself establish a manuscript defect.
