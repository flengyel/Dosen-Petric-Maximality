# W1 fixed-parametric unary logical commutations

## Proved scopes and exact hypotheses

For arbitrary P : Type u, A,B,C : NormalForm P and all context lists, the four
concrete theorems `W1.SameSideLogical.interior_left`, `interior_right`,
`terminal_left`, `terminal_right` compile with only hn : 2≤gs0.length and an
existing arbitrary premise f. No Nonempty P, DecidableEq P, enumeration,
freshness, atomicity, CutFree, Atomized, coherence or equality-reflection
hypothesis is needed. Both signs, constants, compound formulas and premises
with cuts are allowed. Equality is in the existing syntactic Reduced.Hom.
Composition a;b executes a first.

Let D=conj A B for the left cases and D=disj A B for the right cases.
The fully constructed interior data is:

```text
gs0 = pre ++ (U ++ A :: B :: V) :: post
gs1 = pre ++ (U ++ D :: V) :: post
tail0 = tail1 = Θ
upBefore = repeated C pre ++ U
upAfter = V ++ C :: (repeated C post ++ Θ)
loBefore = gaps pre ++ U
loAfter = V ++ (gaps post ++ C :: Θ).
```

The fully constructed terminal data keeps gs0=gs1=gs and uses:

```text
tail0 = U ++ A :: B :: V
tail1 = U ++ D :: V
upBefore = repeated C gs ++ U
upAfter = V
loBefore = gaps gs ++ C :: U
loAfter = V.
```

Write U0=upBefore++A::B::upAfter, U1=upBefore++D::upAfter,
K0=loBefore++A::B::loAfter and K1=loBefore++D::loAfter. Both constructors prove:

```text
upper0 : repeated C gs0 ++ tail0 = U0
upper1 : repeated C gs1 ++ tail1 = U1
lower0 : gaps gs0 ++ C :: tail0 = K0
lower1 : gaps gs1 ++ C :: tail1 = K1
count_eq : gs1.length = gs0.length.
```

G.reindex, At.cast and Route.cast use these actual equalities. No definitional
reassociation is assumed. Modified arity follows from count_eq. The four exact
common old/new proof types are:

| Case | Premise | Common outer proof type |
| --- | --- | --- |
| interior_left | G P U0 Δ | G P ((gaps pre ++ U) ++ conj A B :: (V ++ (gaps post ++ C :: Θ))) Δ |
| interior_right | G P Γ U0 | G P Γ ((gaps pre ++ U) ++ disj A B :: (V ++ (gaps post ++ C :: Θ))) |
| terminal_left | G P U0 Δ | G P ((gaps gs ++ C :: U) ++ conj A B :: V) Δ |
| terminal_right | G P Γ U0 | G P Γ ((gaps gs ++ C :: U) ++ disj A B :: V) |

Inner contracts at gs0/tail0 after the upper0 reindexing, then reindexes by
lower0. Old first applies G.conjL upBefore upAfter Δ A B (left), or
G.disjR Γ upBefore upAfter A B (right), then contracts at gs1/tail1 using
upper1/lower1. New applies the corresponding existing logical constructor at
loBefore/loAfter to inner. No Gentzen constructor or generating equation is
added. The four LeftLaws/RightLaws bundles are proved outputs; no routing,
denotation or rank conclusion is assumed as a concrete theorem premise.

## Baseline and unchanged construction

Clean main at c66c36c95f315b07c1840bd2dd375be21a62a242 agreed with fetched SSH
origin. Actual baseline strict verification passed: 139 files / 5,569 audited
declarations, exit 0, 3.29 seconds. No newer commit or unrelated work was
removed. All completed presentation/reduction/factorization/Gentzenization/
atomization/tracing/rank/W1 constructions are reused.

Thirteen new letters-only modules add 192 explicit source declarations and
373 audited declarations including generated ones. They cover logical indices,
positions, derived comparison/components, concrete data/positions/routing,
predecessors/sums, commutations/ranks/fixed ranks, instances and examples.
DECLARATIONS.txt lists every explicit declaration with source path/line and
signature. Root imports and 80 selected axiom prints are integrated.
All older DosenPetric module bytes, grammars/equations/Positive/G/Rewire,
AtomicFormula/Atomized/CutFree/Topmost, predecessors/ranks, AGENTS, pinned
Lean 4.35.0, Init-only manifest, manuscript v4 and historical reports/reviews/
access records are preserved. Reduced remains 21 term/61 equation schemas,
Positive 19 and G 16. No unwitnessed zero or empty-sequent proof is introduced.

## Source correspondence

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA-256
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also rendered; constant/zero extensions pp.272–273 and 291–292 were
checked against the existing syntax. Verified caches/access artifacts are in
source-consultation.json; historical access records are preserved. No new
source discrepancy was confirmed.

| Source location | Exact local scope / condition | Lean counterpart and actual proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ=∧L | Left conjunction introduction wholly inside one fixed gap or terminal tail; every selected contraction copy is parametric. | `GapLogical.interior/terminal .conj`; `W1.SameSideLogical.interior_left/terminal_left`. Actual conjLeft.toTerm square, not a coherence assumption. |
| §11.2 p.252, right analogue | Right disjunction introduction at the dual fixed positions. | Concrete .disj data and interior_right/terminal_right; actual disjRight.toTerm coproduct square. |
| §11.2 pp.248–249, cluster and rank | Consumed whole-formula A/B positions have no descendant; introduced D is a leaf; surviving positions have one predecessor; sum every selected copy. | At.fixed partial map/reverse, complete ordered selected transport, exact predecessor singleton, existing principal-leaf theorems and contraction sums. |
| §11.2 p.251 W4 / broader configurations | A contraction involving the logical principal formula is a different case. | Excluded here by concrete gap/tail placement and positional distinctions even D=C; W4 and remaining W1/W2–W6 stay separate. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants/atomic zeros remain admitted; whole-formula constants still have positions. | Unchanged syntax, genuine Empty P constant proofs, arbitrary cut-containing premises and witnessed-zero policy. |

The source's broader Semilattice Coherence appeal is replaced for these four
instances by derived component calculations and universal properties. No
strictified equality or new presentation equation is assumed.

## Partial whole-formula ancestry and complete transport

The actual casted copies routes are c0 : Route K0 U0 and c1 : Route K1 U1.
uParent and kParent are At.fixed on the two consumed slots and the single
introduced slot. The all-position theorem is:

```text
Option.map c1.get (uParent a) = kParent (c0.get a).
```

Numeric parentIndex is only the shadow of this partial map. The typed maps
send both consumed A/B positions to none; no total formula-preserving map
from either A or B to D is invented. Data.first/second/principal compute the
copies images of the two consumed slots and the newly introduced compound
separately. At.fixed_reverse supplies the partial inverse on survivors.

selected0/selected1 are exactly selectedCopies cast by upper0/upper1.
selected0_outside excludes both consumed indices; selected1_outside excludes
the compound principal index. These positional facts allow A=C, B=C and D=C.
selected0_survives separately proves that every selected entry has a some
image. The complete ordered statement is:

```text
selected0.flatMap (fun a => (uParent a).toList) = selected1.
```

Both lengths equal n=gs0.length. The proof establishes order on actual
survivors and both membership directions; no copy is silently filtered out,
deduplicated or chosen by its label. Option.get computes selected images
only after survival is proved; it requires no inhabitant of P.

Canonical retained positions keep0/keep1 are At.shift (gaps gs0/gs1)
(here C tail0/tail1), transported by lower0/lower1. retained proves
kParent keep0=some keep1. The separately defined zUpper/zLower are the
introduced D positions at the upper/lower gaps. principal proves c1.get
zUpper=zLower; principal_distinct separates its index from keep1 even D=C.
principal_fiber proves the full canonical singleton fiber above zLower.
For every final nonprincipal/nonretained fixed position, lowerBack is the
partial inverse; fixedCopyAt gives its original upper position otherUpper.
otherMiddle computes its surviving intermediate position and proves its
copies image. These constructions cover every such final position.

## Categorical calculations, including both consumed components

The partial ancestry theorem alone does not prove arrow equality. The actual
Rules.conjLeft comparison has type Iso (ante U1) (ante U0); Rules.disjRight
has type Iso (succ U0) (succ U1). Both denotations use toTerm.
logicalCompare is derived from under and existing associators, and proved
equal to conjLeft, and inverse to disjRight. It is not a primitive rule or
new equation. logicalSide packages conjunction and the opposite disjunction
category for the uniform component calculation.

For a surviving whole-formula a with parent b, logical_survives proves the
corresponding projection/injection law. For the two consumed positions the
separate logical_first/second theorems prove, in left-first notation:

```text
lUpper ; projection(aUpper) = projection(zUpper) ; fst A B
lUpper ; projection(bUpper) = projection(zUpper) ; snd A B
injection(aUpper) ; rUpper = inl A B ; injection(zUpper)
injection(bUpper) ; rUpper = inr A B ; injection(zUpper).
```

These follow from associator inverse laws, projection/injection naturality,
and context induction, with explicit comparison casts. They do not trace a
whole formula into the principal compound. The c0 images of aUpper/bUpper
are aLower/bLower, and c1 maps zUpper to zLower. Product/coproduct universal
extensionality then proves:

```text
p(c1) ; lUpper = lLower ; p(c0) : ante K1 → ante U0
rUpper ; q(c1) = q(c0) ; rLower : succ U0 → succ K1.
```

Prefix/suffix components use the surviving partial square; the two consumed
components use the explicit fst/snd and inl/inr calculations above.
The full paths are:

```text
oldL: ante K1 --p(c1)--> ante U1 --lUpper--> ante U0 --f--> succ Δ
newL: ante K1 --lLower--> ante K0 --p(c0)--> ante U0 --f--> succ Δ
oldR: ante Γ --f--> succ U0 --rUpper--> succ U1 --q(c1)--> succ K1
newR: ante Γ --f--> succ U0 --q(c0)--> succ K0 --rLower--> succ K1.
```

contractL_cast_denote/contractR_cast_denote and Reduced associativity give
ofTerm new.denote=ofTerm old.denote in all four concrete instances.
No occurrence equality, inclusion equality or conditional faithfulness is
reflected to Reduced equality; no Semilattice/Positive/Boolean Coherence is
assumed.

## Exact local rank and preservation theorems

Complete same-side surviving predecessor singletons give rank one plus the
original premise rank. The principal predecessor list is empty and rank is
one, by the existing conjL/disjR principal-leaf theorems. Let Rnew/Rold be
the existing contraction ranks of inner/old, n=gs0.length=gs1.length and
x=keep1. All four concrete results prove:

```text
Rold = Rnew + n
rho(old,x) = Rold
rho(new,x) = Rnew + 1
rho(old,x) + 1 = rho(new,x) + n
Rnew < Rold
rho(new,x) < rho(old,x).
```

The full contraction sums and ordered partial transport count every selected
copy, with none discarded. Contraction-subterm loss is n; whole retained
endpoint loss is n−1. Strictness uses n≥2. At zLower the old/new ranks are
2/1: old has a fixed singleton contraction above the logical leaf; new has
the logical principal leaf at the root. Every other final same-side position
has equal old/new rank 2+rho(f,otherUpper). The two consumed slots receive no
final whole-formula position. Internal literal tags are still present in the
separate occurrence interpretation.

Exact cutCount equality, CutFree and Atomized equivalences, and complete
unchanged-endpoint tagged relation equality compile. Both old/new Atomized
predicates are exactly f.Atomized, with no new AtomicFormula condition.
Relation equality is congrArg occurrenceMap of proved Reduced equality.
There is no premise duplication, quotient rank invariance, arbitrary-context
decrease, general Reducibility, Blocked-w or terminating rewrite-system claim.

## Compiled boundary examples

| Boundary | Checked declaration / actual witness |
| --- | --- |
| Three copies; A=B=C; distinct consumed slots | repeated_left/right and equal_labels_consumed_slots: consumed tags 1/2 are distinct; selected indices [0,3,4] become [0,2,3], with all three retained. |
| Exact n−1 loss and both signs with cuts | repeated_endpoint_loss proves loss 2; both_signs_actual_cut retains actual G.cut and cutCount 1. |
| Two copies; all four Empty P placements | emptyP_interior_left/right and emptyP_terminal_left/right use actual recursive constantLeft/constantRight proof trees, with nonempty gap halves/tails. |
| D=C principal versus retained copy | compound_is_retained_label_left/right: same compound label, distinct actual At positions, full laws including principal 2→1. Empty surrounding blocks are permitted. |
| Compound A/B | compound_components_left/right use conjunction/disjunction components in the two consumed slots with genuine constant premises. |
| Other repeated equal fixed positions | other_fixed_example checks equal old/new ranks at a fixed prefix occurrence distinct from principal and retained positions. |

## Verification, evidence and review scope

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 3.29 | `baseline.log` |
| `bash scripts/verify.sh` | 0 | 5.359 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 7.651 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.308 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.011 | `manuscript.log` |
| `git diff --check` | 0 | 0.014 | `diff-check.log` |

Final result: **152 Lean files / 5,942 audited declarations**; public import
closure passed. All five controls reject with expected diagnostics and Lean
exit 1: direct-axiom (public custom axiom), private-axiom (unused private
custom axiom), hidden-dependency (external axiom), identified-projections
(distinct tagged projections by rfl), zero-without-arrow-witness (missing
correctly typed existing arrow). Their exact sources/logs/hashes are retained.
Permitted axioms remain propext, Quot.sound and Classical.choice. The complete
transitive audit and 80 selected axiom prints are retained; no choice-free
claim is made. Production has no proof holes, custom mathematical axioms or
native_decide. Negative fixtures remain outside production imports.

Every heavy run was sequential. Failed Option/Nat, partial-order, comparison-
cast, explicit component/side-category and At/Place predecessor elaborations,
plus unused-simp and list-normalization diagnostics, retain commands, original
logs, exit codes and timings. The staged diff check also rejected an extra EOF blank line in the new
comparison module (exit 2). That blank line was removed without changing any
declaration; the complete required checks then reran and passed. The exact
diagnostic, command, exit and timing are retained in staged-diff-rejection.json.
No target or frozen interface was weakened. Final required verification
followed this last source-byte correction; later changes are documentation only.

Evidence directory: provenance/wsl-gentzen-w1-same-side-logical/.
DECLARATIONS.txt gives all 192 explicit signatures/anchors. SOURCE_SHA256SUMS
inventories checked Lean/configuration/scripts; EVIDENCE_SHA256SUMS inventories
logs, source access, controls and boundary records. REPORT_SHA256SUMS and
RECORD_SHA256SUMS inventory final reports and current maps/README.

- Strict log: `bf4c21983437fe0a1bfaf4f9a937c11f4f9946ac1f20879e2e628ce32a3d4ba3`.
- Checked source inventory: `714d8d573e3acf3f2d3c93f4bee73b476a9a05f76b58c37fa7d61eede004c5be`.
- Evidence inventory: `a30fd6b04620b820be5e68e936c9a341820f0eca93289e4ce8c25b432656bc7a`.

Baseline, checked working sources and committed bytes are distinct records.
Post-commit inventory checks, live SSH refs and Downloads byte comparisons
are retained in committed-source.json, remote-final.json and delivery.json
under .codex-work/gentzen-w1-same-side-logical/. Differing existing Downloads
files are preserved using dated/commit-suffixed names; every delivered byte
is compared against committed Git objects. The final response supplies the
commit and delivery paths, avoiding a circular commit hash inside its report.

The [hostile review](reviews/GENTZEN_W1_SAME_SIDE_LOGICAL_HOSTILE.md) and
[writing review](reviews/GENTZEN_W1_SAME_SIDE_LOGICAL_WRITING.md) are author-side,
AI-assisted reviews of actual code/statements/correspondence, not independent
certification. The hash-verified Knuth–Larrabee–Roberts cache was consulted
directly. Historical access/review records and manuscript v4 remain unchanged;
no review/process commentary entered manuscript text or LaTeX comments.
Independent kernel/source replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
Palomar submission preparation, publication, licensing and visibility changes
were not performed.

## Next concrete obligation and remaining scope

Next prove same-side contraction through contraction when the inner E copies
lie entirely inside one fixed gap of the outer C contraction, together with
its right dual (§11.2 p.251 W1, γ=wL, with all outer C copies parametric).
This is a proposed obligation, not a production axiom or completed theorem.

For arbitrary P,C,E, lists pre/post, H,U,V,Θ,Δ and hs, put:

```text
es = H :: hs
outer0 = pre ++ (U ++ (repeated E es ++ V)) :: post
outer1 = pre ++ (U ++ (gaps es ++ E :: V)) :: post
upBefore = repeated C pre ++ U
upAfter = V ++ C :: (repeated C post ++ Θ)
loBefore = gaps pre ++ U
loAfter = V ++ (gaps post ++ C :: Θ).
```

Require 2≤outer0.length and 2≤es.length. Take
`f : G P (upBefore ++ repeated E es ++ upAfter) Δ`.
Old first contracts E with gaps `(upBefore ++ H) :: hs` and tail upAfter,
then contracts C using outer1/Θ. New first contracts C using outer0/Θ,
then contracts E with gaps `(loBefore ++ H) :: hs` and tail loAfter.
Use actual G.contractL constructors after proved list reindexings. Both final
types must be exactly:

```text
G P (loBefore ++ gaps es ++ E :: loAfter) Δ.
```

The dual starts with `f : G P Γ (upBefore ++ repeated E es ++ upAfter)`,
uses G.contractR and has final type
`G P Γ (loBefore ++ gaps es ++ E :: loAfter)`.
Every selected E position lies in the designated fixed outer gap, outside all
selected C positions. Every selected C position must remain parametric through
the E contraction and differ from its retained E position. Derive these from
indices, even C=E; do not assume freshness. Prove the copies/copies square,
complete selected transport, Reduced equality and correctly directed rank
comparisons. Shared-selected-copy configurations (W3) are separate; no general
all-site decrease follows from a local commutation.

Remaining crossing-selected, multi-gap and absorption exchange configurations,
other unfinished W1 cases, W2–W6, arbitrary-context replacement, Reducibility,
Blocked-w, cut elimination, PositiveCoherence, Reduced.Faithful, Boolean Coherence,
unconditional maximality and Palomar submission preparation remain separate.
Existing conditional transfers are unchanged. An unformalized cited theorem
does not by itself establish a manuscript defect.
