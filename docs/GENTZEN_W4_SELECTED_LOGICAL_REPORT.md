# W4 terminal selected logical introduction

## Exact proved endpoint and hypotheses

Terminal conjunction-left followed by contraction of the original copies and
the new principal conjunction equals direct contraction of the original copies,
conjunction-left and a final two-copy contraction. The separately typed
disjunction-right dual is also proved. These are the two terminal W4 cases.

For arbitrary P, A,B:NormalForm P, gap list gs and tail Θ, let n=gs.length.
On the left C=conj A B; on the right C=disj A B. Define

```text
R = repeated C gs ++ Θ       S = gaps gs ++ C :: Θ
F = R ++ [A,B]               I = S ++ [A,B]
U = R ++ [C]                 J = S ++ [C]
K = (gaps gs ++ Θ) ++ [C].
```

The only hypotheses are n≥2 and an existing f:G P F Δ on the left or
f:G P Γ F on the right. Premises may contain cuts. No atomicity, CutFree,
Atomized, freshness, DecidableEq, variable inhabitant, coherence or equality-
reflection premise is imposed.

Old applies actual terminal G.conjL/disjR on f, then contracts with gaps
gs++[Θ], tail []. New contracts gs with tail Θ++[A,B], introduces the
terminal logical formula, then contracts with exactly two gaps [gaps gs,Θ],
tail []. ContractionBlock.extend proves and uses the first reassociations;
lastSource/lastTarget prove the final ones. Every bound is derived.
W4.SelectedLogical.terminal_left/right quantify over original inputs.
Both outputs have exact types G P K Δ / G P Γ K, and both equations are
ofTerm new.denote=ofTerm old.denote. The corresponding Hom types are
Hom (ante K) (succ Δ) and Hom (ante Γ) (succ K). Composition a;b applies a first.

## Baseline, implementation and preservation

Clean main b89167f7b9d37476464d5826f06dd9de2ffb3d9a matched fetched SSH
origin. Fresh strict baseline: 185 files / 7,299 audited declarations,
exit 0, 9.950s. The integration stash is preserved.

| New module | Function |
| --- | --- |
| GentzenContractionAppend | Actual contraction extension through a fixed suffix; prefix/suffix routes, retained position and complete selected transport. |
| GentzenSelectedLogicalData | Original A,B,gs,Θ with operation parameter; all contexts, contraction blocks, positions and partial square. |
| GentzenSelectedLogicalComponents | Surviving and both consumed component calculations; correctly variant structural identities. |
| GentzenSelectedLogicalFibers | Complete selected survival/transport, both principal empty fibers, retained/fixed fibers and common originals. |
| GentzenSelectedLogicalRules | Actual old/new G proofs, exact public endpoints and denotation/count/predicate/relation laws. |
| GentzenSelectedLogicalRanks | Complete selected sums, source contraction loss, endpoint balance/tie/strictness and other-position increases. |
| GentzenSelectedLogicalExamples | Inhabited constants, compounds, equal labels, partial routes, ties/increases and signed cuts. |

Every older DosenPetric module and grammar/equation/denotation/tag/predecessor/
rank/predicate interface is byte-preserved. Existing Lean edits only add root
imports and 134 selected axiom prints. Lean 4.35.0 and Init-only dependencies/
manifest are unchanged. Manuscript v4/v5, diagrams, references/checksums,
AGENTS, historical reports/access records and other checkouts are preserved.
No new G primitive, generating equation, mathematical axiom or arbitrary zero.

## Source correspondence

The directly consulted source is Došen–Petrić, Proof-Theoretical Coherence,
September 2007, cached from
[the full PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Printed pp.248–253 are PDF pp.260–265, one-based. Printed p.251 was inspected
in rendering; p.252 states the right analogue. No new discrepancy is asserted.

| Source location | Exact correspondence | Actual Lean proof |
| --- | --- | --- |
| p.251 W4 | Newly introduced terminal conjunction is selected; move the n-copy contraction above introduction, retaining a two-copy outer contraction. | Data.last, actual oldL/newL and terminal_left. |
| p.250 (w ∧ 1), p.251 W4 | The new final two-copy pattern is the displayed blocked shape. | Actual last gaps [gaps gs,Θ], terminal conjL, selected retained and principal positions. No general Blocked-w claim. |
| pp.248–249 | Logical principal C has no whole-formula predecessor; each old selected path survives and gains a node. | consumed_a/b, selected_survives/transport, both principal empty fibers and selected_sumL/R. |
| p.251 W4 ranks | New inner contraction is lower than old outer contraction by n+1. | contraction_lossL/R and contraction_decreasesL/R. |
| p.252 right analogue | Actual disjR/contractR and independently typed coproduct equality. | terminal_right, denoteR and right ranks/preservation. |

The blocked shape is identified by actual constructors, without an unproved
general blocked/reducible interface. The source's Semilattice Coherence appeal
is replaced by component calculations in the original Reduced category.
No relation or inclusion equality is reflected.

## Complete ancestry, selection and categorical calculation

Write c:Route I F for inner contraction, o:Route K U for old contraction,
and b:Route K J for the final two-copy contraction. Logical whole-formula
ancestry is uParent:At F E→Option (At U E) and
iParent:At I E→Option (At J E), for every E. Both A/B slots are consumed.
For every original position a, the proved all-position partial square is

```text
(uParent a).map o.get = (iParent (c.get a)).map b.get.
```

The construction reuses W2's numerical old-position square and exchange
coordinates. It reuses positional facts; actual W4 introduction uses conjL/
disjR. Every comparison is derived from original inputs.

The complete inner selection has length n, every entry survives uParent,
and its ordered image followed by the old logical principal z equals the
outer selection of length n+1. The new final list is exactly [k,q]:
k is the inner retained C surviving introduction, and q the new principal.
Both map to retained x. Equal-labelled fixed positions retain their tags.

Both logical principal fibers are empty. Full old outer retained fiber has
n+1 members; full final retained fiber has two. Both composite partial routes
from original F have retained fiber exactly inner.selected, with n entries.
Neither A/B slot is falsely assigned a total C parent. Every other final
position z' has a computed common original a:At F E. Actual outer/inner/
last fixed fibers and both composite fibers are complete singletons.

Let L_U,L_J be the actual terminal logical structural arrows on each side.
The component calculations give

```text
o.product ; L_U = b.product ; L_J ; c.product
L_U ; o.coproduct = c.coproduct ; L_J ; b.coproduct.
```

Both sides have type ante K→ante F in the first equation and succ F→succ K
in the second, with L_U,L_J denoting that side's logical arrows.
Surviving components use the partial square. Consumed A and B components
are checked separately using fst/snd, or the corresponding inl/inr through
the opposite product category, and the proved principal images. The partial
whole-formula square is not treated as a full denotation proof. Associativity
and actual constructor denotations give both principal equalities.

## Exact ranks and preservation

On each side, let LC be the new inner n-ary contraction rank on f, one plus
the full original selected rank sum. Old introduction adds a node to each
of n old selected paths; its new selected leaf has rank one. Thus the old
outer selected sum adds n+1. New middle retained rank is LC+1, middle
principal rank one, and final two-copy contraction adds its root.

| Quantity | Old | New |
| --- | --- | --- |
| Source-comparison contraction rank | LC+n+1 (outer) | LC (inner) |
| Final retained endpoint rank | LC+n+1 | LC+3 |
| Every other final same-side rank | 2+rho(f,a) | 3+rho(f,a) |

The source contraction loss is exactly n+1 and strict. Endpoint balance is
rho(old,x)+2=rho(new,x)+n: a tie for n=2 and strict decrease for n≥3.
Every other fixed rank increases by one at its proved common original a.
These local syntax ranks supply no quotient invariant, all-position decrease,
arbitrary-context replacement, termination, Reducibility or Blocked-w theorem.

Both cut counts equal f.cutCount; both CutFree predicates equal f.CutFree;
both Atomized predicates equal f.Atomized. Compound logical principals require
no AtomicFormula restriction. Full tagged relation equality follows from
Reduced equality. Existing-arrow premises and empty hom-sets are preserved.

## Inhabited examples

For gs=[[C],[C]], Θ=[C,C], inner selected indices are [1,3], outer
[1,3,6], and final [2,5]. Old seven-C route is [0,4,1,4,2,3,4]; new
final six-C route is [0,1,4,2,3,4]. Both composite partial routes send the
six original C positions to [some 0,some 4,some 1,some 4,some 2,some 3].
The two A/B slots are separately consumed; when A=B their indices 6 and 7
are still distinct. Both original retained fibers have indices [1,3].
Fixed final position 0 has original 0 despite both being labelled C.

Actual atomized Empty P constant premises prove both n=2 endpoint ties,
both fixed-rank increases and both Atomized assertions for compound principal
formulas. Empty/nonempty tails/gaps, empty literal-occurrence sets and compound
A/B occur. Existing signed cut premises with explicit compound-prefix thinning
inhabit both n=3 types, retain cutCount=1 and give strict endpoint decreases.
Both signs are checked. No example uses an impossible empty sequent.

## Verification, reviews and evidence

Final strict verification passes: 192 files / 7,543 audited declarations,
an increase of 244. All 134 new theorems have selected axiom prints and exact
public-type queries, supplementing full transitive audit/import closure.
Public-type queries pass in 2.133s. Only propext, Quot.sound and Classical.choice
are permitted; no choice-free claim is made.

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 4.020 |
| python3 scripts/check-audit-boundaries.py | 0 | 9.940 |
| python3 scripts/check-presentation-boundaries.py | 0 | 2.335 |
| manuscript SHA256SUMS | 0 | 0.023 |
| git diff --check | 0 | 0.009 |
| git diff --cached --check | 0 | 0.010 |

All five controls reject with expected diagnostics and Lean exit 1: direct,
private and hidden external custom axioms; rfl-identification of distinct tagged
projections; zero without a correctly typed existing-arrow witness. Heavy
checks were sequential after the last proof edit.

Failed elaborations are retained: semireducible field/endpoint aliases,
composition unfolding, unused simp arguments, arithmetic association,
Option-map normalization, scalar sums and dependent elimination at a compound
label. Generic typed parent lemmas resolve the last issue without changing the
target. No theorem/interface, source equation or heartbeat limit was weakened.
The final example build command passed in 14.161s.

Evidence is retained under provenance/wsl-gentzen-w4-selected-logical/ and
.codex-work/gentzen-w4-selected-logical/: baseline/final commands, exits/timings,
versions, exact types/axioms, declaration/source inventories, source-access
material, controls and failed attempts. The
[hostile review](reviews/GENTZEN_W4_SELECTED_LOGICAL_HOSTILE.md) and
[writing review](reviews/GENTZEN_W4_SELECTED_LOGICAL_WRITING.md) inspect actual
proofs/maps. They are author-side AI-assisted reviews, not independent
certification. Separate receipts compare checked/committed bytes, SSH refs and
Downloads copies; no self-referential commit hash appears here.

Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
publication, licensing and visibility changes did not run.

## Next concrete proof obligation

Prove source W5 single-premise mix, selecting only g in G.mix f g, and its
right dual; see [the continuation](CODEX_W5_SINGLE_PREMISE_MIX.txt).
Actual mix puts g's contexts first. Both-premise selection, other placement
and binary logical W5/W6 remain separate.

Remaining W1/W2/W5–W6 cases, disjoint interleaving/exchange, arbitrary-context
replacement, Reducibility, Blocked-w, cut elimination, restricted coherence,
PositiveCoherence, Reduced.Faithful, Boolean Coherence and unconditional
maximality remain open. The three milestones and conditional transfers are
unchanged. Unfinished reconstruction of published work does not establish
a manuscript defect.
