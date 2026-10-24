# W1 terminal-tail disjoint same-side contractions

## Exact proved endpoint and hypotheses

Left contraction commutes with a disjoint left contraction in its fixed terminal
tail. The separately typed right commutation is also proved. These are two local
instances of W1, not general reducibility or cut elimination.

For arbitrary `P : Type u`, `C E : NormalForm P`, gap lists `gs hs`, and context
lists `H U V`, define:

```text
es       = H :: hs
n        = gs.length
m        = es.length
upBefore = repeated C gs ++ U
loBefore = gaps gs ++ C :: U
F        = upBefore ++ repeated E es ++ V
FE       = upBefore ++ gaps es ++ E :: V
FC       = loBefore ++ repeated E es ++ V
K        = loBefore ++ gaps es ++ E :: V
tailC0   = U ++ repeated E es ++ V
tailC1   = U ++ gaps es ++ E :: V
eUpper   = (upBefore ++ H) :: hs
eLower   = (loBefore ++ H) :: hs.
```

The hypotheses are independent bounds `2 ≤ n`, `2 ≤ m`, and an existing
`f : G P F Δ` for the left case or `f : G P Γ F` for the right case. There is
no equal-arity, `C ≠ E`, atomicity, CutFree, Atomized, nonempty-variable,
decidable-equality, enumeration, coherence or equality-reflection hypothesis.
Premises may contain cuts.

The public theorems are
`DosenPetric.Reduced.Gentzen.W1.DisjointContraction.terminalTail_left` and
`terminalTail_right`. In each case innerE contracts E directly on f using
eUpper/V; innerC contracts C directly using gs/tailC0. Old contracts C on
innerE using gs/tailC1. New contracts E on innerC using eLower/V. Their exact
types are:

```text
left:  old,new : G P ((gaps gs ++ C :: U) ++ gaps es ++ E :: V) Δ
right: old,new : G P Γ ((gaps gs ++ C :: U) ++ gaps es ++ E :: V).
```

Both principal equations are `ofTerm new.denote = ofTerm old.denote` in
Reduced.Hom. Composition `a;b` applies a first. The left denotations have type
`ante K → succ Δ`; the right denotations have type `ante Γ → succ K`.
Neither retained position is a newly introduced principal leaf.

## Baseline, implementation and preservation

The baseline is main `14c0f7dad53ef2267a99afe11d76f1612f5b9836`, including
the corrected manuscript v5 and sentence audit. The recorded fresh baseline
verification passed on 23 October 2026: 162 Lean files and 6,310 audited
declarations, exit 0, 7.089 seconds. On resumption, Git status was inspected,
the SSH origin was fetched, and the same baseline was confirmed.

Nine new modules add 307 explicit source declarations and 395 audited
declarations including generated ones:

| Modules | Function |
| --- | --- |
| GentzenContractionFrame, GentzenContractionFrameFibers | Reusable raw contraction endpoints, derived ordered transports and complete fixed fibers. |
| GentzenContractionFrameCommutation, GentzenContractionFrameRanks | Actual left/right contraction pairs, structural equality and independent rank calculations. |
| GentzenContractionFrameInterior | Instantiates the interface in the completed fixed-gap case; four proof-term comparisons are rfl. |
| GentzenTerminalContractionData, GentzenTerminalContractionRouting | Original terminal inputs, all eight endpoint equalities, concrete square and positional separation. |
| GentzenTerminalContractionInstances, GentzenTerminalContractionExamples | Two public terminal endpoints, preservation/ranks and inhabited boundary examples. |

`TerminalContraction.Data` stores only C,E,gs,hs,H,U,V. The generic frame
stores contraction descriptions, endpoint equalities and arity identifications;
it does not store a routing square, denotation equality or rank conclusion.
The terminal constructor proves those data and every required law. Conditional
generic helpers are not substituted for the concrete terminal theorems.

Every older DosenPetric module is byte-preserved. The only changes to existing
Lean files are root imports and selected axiom prints. Reduced syntax/equations,
Positive/G/Rewire, denotations, tags, predecessor/rank definitions and analysis
predicates are unchanged. Lean 4.35.0 and the Init-only manifest remain pinned.
Both manuscript versions, diagrams, references, checksums, AGENTS, historical
reports and the retained integration stash are preserved. No new dependency,
equation, arbitrary-endpoint zero or interpretation-kernel quotient is added.

## Source correspondence

The directly consulted source is Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, cached from
[the full source PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed pp.248–253 are PDF pp.260–265, one-based; printed p.251 was inspected
in rendering. Access and page evidence are retained. No source erratum is asserted.

| Source location | Local condition | Actual proof |
| --- | --- | --- |
| §11.2 p.251, W1, γ=wL | All C-selected positions lie in the lower parametric prefix of the inner E contraction; E-selected positions occupy the terminal block. | Terminal Data, selectedC_before/selectedE_inside and selected_separated. |
| §11.2 p.252, right analogue | Same terminal placement in the succedent. | Actual G.contractR pair and separately typed coproduct-square proof. |
| pp.248–249, clusters and ranks | A fixed position contributes one node; a retained contraction position has all selected predecessors. | Complete singleton fibers and ContractionBlock.rankL/R_sum/fixed. |
| p.251, W3 | The retained inner contraction position is itself selected by the outer contraction. | Excluded by terminal separation; still open. |
| pp.250–253, Reducibility and Blocked-w | Replacement at cut-tied sites with control of all affected reducible subterms. | Not a consequence claimed for these local results. |

The source's Semilattice Coherence appeal is replaced here by concrete positional
equalities and existing product/coproduct universal component laws. No coherence
premise or reflection of occurrence equality is used.

## Endpoint transports, selected copies and fixed fibers

The eight proved identities are:

```text
repeated C gs ++ tailC0 = F        gaps gs ++ C :: tailC0 = FC
repeated C gs ++ tailC1 = FE       gaps gs ++ C :: tailC1 = K
repeated E eUpper ++ V = F         gaps eUpper ++ E :: V = FE
repeated E eLower ++ V = FC        gaps eLower ++ E :: V = K.
```

Both E gap-list lengths equal m; the two C descriptions have length n.
ContractionBlock uses actual G.reindex, At.cast and Route.cast transports.
The routes are `c0 : Route FC F`, `e0 : Route FE F`, `c1 : Route K FE`,
`e1 : Route K FC`. A Route's get map acts from positions in its second
context to positions in its first context.

`copy_splice_tail` proves the numerical square recursively, without a bound
on the substituted block map. Specialization to the actual E copyIndex gives,
for every formula A and `a : At F A`,
`c1.get (e0.get a) = e1.get (c0.get a)`. Universal components then prove the
correctly variant categorical equations, with `p(w)=ofTerm w.product` and
`q(w)=ofTerm w.coproduct`:

```text
p(c1);p(e0) = p(e1);p(c0) : ante K → ante F
q(e0);q(c1) = q(c0);q(e1) : succ F → succ K.
```

Actual casted contraction denotations and associativity give the two principal
Reduced equalities. Occurrence equality is a consequence, not a proof input.

Both complete ordered lists are transported:
`selectedC1 = selectedC0.map e0.get` and
`selectedE1 = selectedE0.map c0.get`. Their lengths are n,n,m,m. Every C-selected
source index is less than `(repeated C gs).length`; every E-selected index lies
between `upBefore.length` and `upBefore.length+(repeated E es).length`, with
the upper bound strict. Analogous intermediate bounds are proved. Thus C copies
precede E copies even when C=E. Order/injectivity is used only on fixed or
specified selected positions, not asserted globally for contraction routes.

All selected C copies have singleton fibers through E, and all selected E
copies have singleton fibers through C. Their images avoid the opposite
retained index. Intermediate keepC0/keepE0 map to final xC/xE, with complete
fibers [keepC0]/[keepE0] through the other contraction. The zero-based indices are:

```text
xC.index = (gaps gs).length
xE.index = (gaps gs).length + 1 + U.length + (gaps es).length
xC.index < xE.index.
```

This ordering is proved for the terminal construction; it reverses the interior
case. Both composite routes send each complete selected family to its retained
position. For every other final position, `original` constructs the same unique
original position through both routes; `other_fiber` proves both complete
composite fibers are its singleton. Constants retain whole-formula positions
even when their literal-occurrence types are empty.

## Exact ranks and preservation

Separately for each sequent side, let LC and LE be the ranks of innerC and
innerE directly on f. They are one plus the respective complete selected-copy
rank sum. The proved table is:

| Proof | Rank at xC | Rank at xE |
| --- | --- | --- |
| old: C after E | LC+n | LE+1 |
| new: E after C | LC+1 | LE+m |

The outer C contraction-subterm rank is LC+n; the outer E contraction-subterm
rank is LE+m. Old→new lowers the C endpoint by n−1 and raises the E endpoint
by m−1. Both exact balances, strict comparisons for independent n,m≥2 and
the inequalities LC<rho(old,xC), LE<rho(new,xE) compile on each side.

For the sum S of just these two endpoint ranks,
`S(old)+m = S(new)+n`. Equal arities give equal sums; an inhabited n=2,m=3
example gives `S(new)=S(old)+1`. This sum is not a decreasing termination
measure, and ranks are not asserted to descend to Reduced.Hom. Every other
final same-side rank in either proof is `2+rho(f,a)` at the proved common
original position a.

Both cut counts equal f.cutCount. Each CutFree predicate and each Atomized
predicate is equivalent to the corresponding predicate of f, without a new
atomicity hypothesis. Complete tagged relations are equal by applying
occurrenceMap to the proved Reduced denotation equality.

## Inhabited examples

For C=E=T, gs=[[],[]], es=[[T],[],[]] and U=V=[], the checked source has six
T positions. The selected indices C0/E0 are [0,1]/[3,4,5], and C1/E1 are
[0,1]/[2,3,4]. The actual route index maps are:

```text
c0 = [0,0,1,2,3,4]     e0 = [0,1,2,3,3,3]
c1 = [0,0,1,2]         e1 = [0,1,2,2,2]
both composite maps = [0,0,1,2,2,2].
```

Retained C/E indices are 0/2. The unselected equal-labelled source index 2
maps to final index 1; its computed original is proved to be that exact tag.
Actual literal premises inhabit both sides. Positive and negative literals
occur in actual cut-containing examples, each with cutCount=1.

Actual Empty-variable constant premises check both sides and the unequal-arity
sum increase. Compound C/E with independent n=3,m=2, nonempty internal gaps,
U,V, and an equal-arity n=m=2 empty-context specialization also compile. The
fixed equal-labelled position satisfies the stated common-original rank law.

## Verification, reviews and evidence

Fresh sequential verification completed on 24 October 2026 at
`2026-10-24T16:44:27.831850+00:00`. The strict result is **171 Lean files and
6,705 audited project declarations**. Commands and exits:

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 11.795 |
| python3 scripts/check-audit-boundaries.py | 0 | 10.980 |
| python3 scripts/check-presentation-boundaries.py | 0 | 2.678 |
| sha256sum -c SHA256SUMS, in manuscript/ | 0 | 0.034 |
| git diff --check | 0 | 0.014 |
| git diff --cached --check | 0 | 0.013 |

The full transitive audit permits only propext, Quot.sound and Classical.choice;
122 selected axiom prints supplement it. Public import closure passes. All
five controls reject with the expected diagnostic and Lean exit 1: direct
custom axiom, unused private custom axiom, hidden external axiom, identification
of distinct tagged projections by rfl, and zero without a correctly typed arrow
witness. Heavy checks were sequential. No choice-free claim is made.

Evidence is retained in `provenance/wsl-gentzen-w1-terminal-tail-contraction/`
and `.codex-work/gentzen-w1-terminal-tail-contraction/`: original baseline,
initial and resumed verification, commands/exits/timings, exact public types,
declaration and source inventories, selected axioms, source-access evidence,
and negative-control sources/logs. Exploratory compilation failures are retained:
proof-only variable inclusion, transport argument grouping, arithmetic/alias
normalization, typed At/Place rewriting and an unsupported pp.width query were
repaired without weakening interfaces or raising heartbeat limits.

The [hostile review](reviews/GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_HOSTILE.md)
and [writing review](reviews/GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_WRITING.md)
are author-side AI-assisted reviews of these actual proofs and records.
They are not independent certification. Current maps, correspondence, README,
validation and continuation identify exactly these two new terminal cases.
Separate receipts record committed-source, SSH-ref and Downloads comparisons;
this report does not attempt to include its own final commit hash.

Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight, service verification, fresh manuscript compilation/layout review,
publication, license selection and repository-visibility changes have not run.

## Next concrete proof obligation

Prove source W3 shared-selected contraction fusion and its right dual: when
the outer selected list contains the retained inner position, construct one
contraction whose ordered original selected family has n+m−1 positions. Prove
the exact endpoint and composite-route identity, both Reduced denotation
equalities and the source rank drop by m. The ready-to-paste continuation is
[CODEX_W3_SHARED_SELECTED_CONTRACTION.txt](CODEX_W3_SHARED_SELECTED_CONTRACTION.txt).

Disjoint interleaved cases, remaining exchange configurations, other W1/W2–W6,
arbitrary-context replacement/all-site decrease, Reducibility, Blocked-w,
cut elimination, restricted positive-coherence inputs, PositiveCoherence,
Reduced.Faithful, Boolean Coherence and unconditional maximality remain open.
The existing conditional transfers and three milestone boundaries are unchanged.
An unfinished reconstruction of cited published results does not establish a
defect in the manuscript.
