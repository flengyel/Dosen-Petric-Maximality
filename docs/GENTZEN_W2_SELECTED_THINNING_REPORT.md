# W2 terminal selected thinning

## Exact proved endpoint and hypotheses

Appending a selected thinning occurrence and contracting it with the original
copies denotes the same Reduced arrow as contracting the original copies and
exchanging the retained occurrence past the tail. The separately typed right
dual is also proved. These are the two terminal W2 instances.

For arbitrary `P : Type u`, `C : NormalForm P`, gap list gs and tail Θ, put
n=gs.length and

```text
F = repeated C gs ++ Θ
I = gaps gs ++ C :: Θ
U = F ++ [C]
K = (gaps gs ++ Θ) ++ [C].
```

The only hypotheses are n≥2 and an existing f:G P F Δ (left) or f:G P Γ F
(right). There is no atomicity, CutFree, Atomized, nonempty-variable,
decidable-equality, freshness, enumeration, coherence or equality-reflection
hypothesis. Premises may contain cuts.

`W2.SelectedThinning.terminal_left/right` quantify over the original inputs.
Thin appends C at the terminal gap using actual G.thinL/R. Old then contracts
the n original selected copies and the new occurrence using gaps gs++[Θ],
tail []. Inner contracts gs/Θ directly on f. New applies actual exchange to
inner, with prefix gaps gs, blocks [C] and Θ, and empty tail. Every context
reassociation is proved and used through genuine G/At/Route casts. The exact
output types are G P K Δ and G P Γ K. Both principal equations are
`ofTerm new.denote = ofTerm old.denote`.

The left arrows have type `Hom (ante K) (succ Δ)`; the right arrows have type
`Hom (ante Γ) (succ K)`. Composition a;b applies a first. An empty exchange
block remains an actual exchange node when computing proof ranks.

## Baseline, implementation and preservation

The clean baseline is main `31922370e7ce5ffa0286a88e8cffe6e232aa824f`, matching
fetched SSH origin. Fresh strict baseline verification passed: 179 source
files / 7,069 audited declarations, exit 0, 10.311s. The retained integration
stash and all other checkouts are preserved.

Six new modules implement the result:

| Module | Function |
| --- | --- |
| GentzenUnaryCasts | Actual thinning/exchange constructors and their casted denotation and rank laws; correctly variant exchange routes. |
| GentzenSelectedThinningData | Original C,gs,Θ only; contexts, bounds, concrete numerical square and inserted/retained positions. |
| GentzenSelectedThinningFibers | Complete ordered selected transport, retained/fixed fibers, unique original positions and structural squares. |
| GentzenSelectedThinningRules | Both exact public endpoints, Reduced equalities and preservation, including asymmetric atomicity. |
| GentzenSelectedThinningRanks | Complete selected sums and exact contraction/endpoint/fixed-position tables. |
| GentzenSelectedThinningExamples | Inhabited equal-label, constant, compound, empty-exchange and signed-cut boundaries. |

Every older DosenPetric module, primitive grammar, equation, denotation,
occurrence tag, predecessor/rank definition and analysis predicate remains
byte-preserved. Existing Lean edits only add root imports and 137 selected
axiom prints. The pinned Lean 4.35.0 toolchain and Init-only package closure
are unchanged; no dependency or manifest changes are needed. Manuscript v4/v5,
diagrams, references, checksums, AGENTS and all earlier reports/access records
are preserved. No new G rule, source equation, mathematical axiom or
arbitrary-endpoint zero is introduced.

## Source correspondence

The directly consulted source is Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, cached from
[the full source PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed pp.248–253 are PDF pp.260–265, one-based; p.251 was inspected in
rendering, including W2 and the next W4 case. The right analogue is stated
on printed p.252. No source discrepancy is asserted.

| Source location | Exact local condition | Lean proof |
| --- | --- | --- |
| §11.2 p.251, W2 | The new terminal C is selected together with all original gs copies; after contraction, exchange the retained C past Θ. | Original Data, actual old/new constructors and terminal_left. |
| p.252, right analogue | The same configuration in the succedent. | Actual G.thinR/contractR/exchangeR and separately typed terminal_right. |
| pp.248–249, cluster ancestry | The new thinning occurrence is a rank-one leaf, whereas every embedded old selected copy gets one extra node. | selected_transport, thin_principalL/R and thin_embeddedL/R. |
| p.251, W1 versus W2 | Fixed-parametric insertion excludes the inserted position from contraction; this selected insertion includes it. | inserted_selected and the appended singleton in the complete selected list. |

The source's Semilattice Coherence appeal is replaced by a concrete positional
square and the existing product/coproduct universal component laws in Reduced.
No occurrence or inclusion equality is reflected back to Reduced equality.

## Complete positional calculation

The old contraction's upper context is U and its lower context is K, by
proved repeated/gaps append identities. Its arity is n+1 and satisfies the
constructor bound. The direct contraction has contexts F/I. The exchange
upper and lower contexts are explicitly identified with I/K.

Write t:Route U F for the old-position thinning embedding and e:Route K I
for exchange. Old positions retain their source indices through t. The inserted
z:At U C has index F.length. The final retained x:At K C has index
(gaps gs).length+Θ.length. For every formula A and a:At F A,

```text
outer.route.get (t.get a) = e.get (inner.route.get a).
```

The numerical proof is bounded by the actual source length; a separate last-
position lemma covers z. The exchange sends inner.keep to x, and the old
contraction sends z to x. Both t and e are injective on typed positions;
exchange has the proved inverse back.

The complete ordered list identity is

```text
outer.selected = inner.selected.map t.get ++ [z].
```

Its length is n+1, with n original members. Each embedded original index is
strictly less than z.index, even when every formula label equals C. No tag is
discarded or deduplicated. Complete fibers through t are singleton. The full
old outer retained fiber contains all n+1 positions. In contrast, either
composite route from original F has retained fiber inner.selected, containing
only n positions: the new thinning leaf has no original predecessor.

For every other final position z', back z' avoids the inner retained index.
Taking the direct contraction's unique fixed inverse gives original(z'). The
old outer fiber is [t.get original(z')], and both composite fibers are
[original(z')]. These are complete fiber equations, not just membership.

The universal components give the correctly variant equations

```text
outer.product ; t.product = e.product ; inner.product
t.coproduct ; outer.coproduct = inner.coproduct ; e.coproduct.
```

Both sides have type ante K→ante F in the first equation, and succ F→succ K
in the second.

Actual casted constructor denotations and associativity then give both principal
Reduced equalities. Whole-formula constant positions remain present even when
their literal-occurrence types are empty.

## Exact ranks and preservation

Separately for each sequent side, let LC be the direct n-ary contraction rank
on f. It is one plus the complete original selected rank sum. Every one of
those n selected paths receives one thinning node; the new selected leaf
contributes rank one. Thus the old outer selected sum is the original sum+n+1.
The proved table is:

| Quantity | Old | New |
| --- | --- | --- |
| Contraction-subterm rank | LC+n+1 | LC |
| Final retained endpoint rank | LC+n+1 | LC+1 |
| Any other final same-side rank | 2+rho(f,a) | 2+rho(f,a) |

Here a is the proved common original of that fixed final position. Exact
losses are n+1 for the contraction subterm and n for the retained endpoint;
both strict decreases compile for n≥2. The final exchange contributes its
node even when Θ is empty. These are local syntax ranks, not quotient
invariants or an all-site/arbitrary-context termination argument.

Both cut counts equal f.cutCount; both CutFree predicates are equivalent to
f.CutFree. The exact atomicity statements differ:

```text
old.Atomized ↔ AtomicFormula C ∧ f.Atomized
new.Atomized ↔ f.Atomized.
```

Old Atomized therefore implies new Atomized. The reverse direction is proved
with AtomicFormula C; it is false without that boundary, as the compound
examples demonstrate. Atomicity is not imposed on equality or rank theorems.
Complete tagged relation equality follows from the proved Reduced equality.
Existing-arrow premises are retained; no empty hom-set is filled.

## Inhabited examples

For tagged C, gs=[[C],[C]] and Θ=[C,C], all original six source formulas and
the appended seventh formula have the same label. Checked data are:

```text
inner selected indices: [1,3]
outer selected indices: [1,3,6]
inserted index 6; final retained index 4
inner map: [0,2,1,2,3,4]
thinning map: [0,1,2,3,4,5]
exchange map: [0,1,4,2,3]
outer map: [0,4,1,4,2,3,4]
both composite maps from F: [0,4,1,4,2,3].
```

Retained-fiber calculations distinguish [1,3,6] above U from [1,3] above F.
Fixed final tags 0 and 2 have computed original indices 0 and 4; actual
left/right fixed-rank equalities compile despite their equal C labels.

Actual Empty P constants check both sides and the rank contribution of an
empty-block exchange. Both n=2 and n=3 and empty/nonempty tails/internal gaps
occur. For C=top∧bot, actual atomized premises are obtained using the existing
atomization theorem; new is Atomized and old is not, separately on both sides.
Equality still holds. Literal examples quantify over either sign, and actual
positive-left/negative-right cut-containing premises retain cutCount=1 and
the exact n=3 endpoint loss. No example relies on an impossible premise.

## Verification, reviews and evidence

Final sequential verification completed at
`2026-10-24T19:42:19.278561+00:00`: **185 source files / 7,299 audited project
declarations**, an increase of 230 audited declarations. All new theorems have
137 selected axiom prints and exact public-type queries, supplementing the
complete transitive audit and public import closure. Only propext, Quot.sound
and Classical.choice are permitted; no choice-free claim is made.

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 19.596 |
| python3 scripts/check-audit-boundaries.py | 0 | 23.899 |
| python3 scripts/check-presentation-boundaries.py | 0 | 2.215 |
| sha256sum -c SHA256SUMS, in manuscript/ | 0 | 0.051 |
| git diff --check | 0 | 0.020 |
| git diff --cached --check | 0 | 0.026 |

All five controls reject with expected diagnostics and Lean exit 1: direct
custom axiom, unused private custom axiom, hidden external axiom, rfl
identification of distinct tagged projections, and zero without a correctly
typed existing-arrow witness. Heavy checks were sequential. Failed numeric
normalizations, alias rewrites, scalar sum elaboration and the initially
wrong-sized literal premise are retained with diagnostics. The latter was
replaced by the existing four-copy cut premise at the unchanged required
type. No statement, source equation or heartbeat limit was weakened. Final
example compilation passed in 14.533s.

Evidence is retained under `provenance/wsl-gentzen-w2-selected-thinning/` and
`.codex-work/gentzen-w2-selected-thinning/`, including baseline/final commands,
exits/timings, source/declaration inventories, exact types, selected axioms,
source-access evidence and controls. The
[hostile review](reviews/GENTZEN_W2_SELECTED_THINNING_HOSTILE.md) and
[writing review](reviews/GENTZEN_W2_SELECTED_THINNING_WRITING.md) inspect actual
proofs and current correspondence. They are author-side AI-assisted reviews,
not independent certification. Separate receipts compare checked and committed
source, SSH refs and Downloads bytes; this report does not include its own
final commit hash.

Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
publication, license selection and visibility changes did not run.

## Next concrete proof obligation

Prove source W4 terminal logical introduction selected by contraction and its
right dual, as specified in
[CODEX_W4_SELECTED_LOGICAL.txt](CODEX_W4_SELECTED_LOGICAL.txt). Its source
comparison concerns the new inner contraction rank. Do not demand a general
strict final-endpoint decrease: the proposed exact table has an n=2 tie.

Remaining disjoint interleaving/exchange/W1/W2/W4–W6 cases, arbitrary-context
replacement, Reducibility, Blocked-w, cut elimination, restricted coherence
inputs, PositiveCoherence, Reduced.Faithful, Boolean Coherence and unconditional
maximality remain separate/open. Existing conditional transfers and the three
milestones are unchanged. Unfinished reconstruction of cited published work
does not establish a manuscript defect.
