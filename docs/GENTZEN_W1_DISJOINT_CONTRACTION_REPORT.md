# W1 fixed-gap disjoint same-side contractions

## Exact proved endpoint and hypotheses

Two concrete commutations compile: left contraction through left contraction
inside one fixed gap, and its separately typed right dual. For arbitrary
P : Type u, C,E : NormalForm P, pre,post,hs : List (List (NormalForm P)),
H,U,V,Θ and Δ/Γ : List (NormalForm P), put:

```text
es = H :: hs
outer0 = pre ++ (U ++ (repeated E es ++ V)) :: post
outer1 = pre ++ (U ++ (gaps es ++ E :: V)) :: post
upBefore = repeated C pre ++ U
upAfter  = V ++ C :: (repeated C post ++ Θ)
loBefore = gaps pre ++ U
loAfter  = V ++ (gaps post ++ C :: Θ)
eUpper = (upBefore ++ H) :: hs
eLower = (loBefore ++ H) :: hs
F  = upBefore ++ repeated E es ++ upAfter
FE = upBefore ++ gaps es ++ E :: upAfter
FC = loBefore ++ repeated E es ++ loAfter
K  = loBefore ++ gaps es ++ E :: loAfter.
```

The independent bounds are hn : 2≤outer0.length and hm : 2≤es.length;
n=outer0.length and m=es.length need not be equal. The premise is an existing
arbitrary f : G P F Δ (left) or f : G P Γ F (right), including premises with
cuts. There is no inhabitant, DecidableEq P, enumeration, freshness, C≠E,
atomicity, CutFree, Atomized, coherence or equality-reflection hypothesis.

`W1.DisjointContraction.fixedGap_left/right` prove the full LeftLaws/RightLaws
output bundles. They do not take a routing, denotation or rank conclusion as
a hypothesis. `Disjoint.Data` stores only the original formulas/lists; every
coordinate and routing theorem is constructed from those fields. The exact
common final types are:

```text
left:  G P ((gaps pre ++ U) ++ gaps es ++ E ::
            (V ++ (gaps post ++ C :: Θ))) Δ
right: G P Γ ((gaps pre ++ U) ++ gaps es ++ E ::
              (V ++ (gaps post ++ C :: Θ))).
```

InnerC contracts C directly on f using outer0/Θ; innerE contracts E directly
on f using eUpper/upAfter. Old contracts C at outer1/Θ after innerE. New
contracts E at eLower/loAfter after innerC. Both pairs use actual G.contractL
or G.contractR plus proved G.reindex transports. In Reduced.Hom:

```text
ofTerm new.denote = ofTerm old.denote.
```

Composition a;b applies a first. Neither retained position is a newly
introduced principal leaf; there is no thinning/logical 2→1 claim.

## Baseline and preserved interfaces

Clean main at 6192328eccde5e4aa912017409289255bc8c5cb1 agreed with fetched SSH
origin. Actual baseline strict verification passed: 152 Lean files / 5,942
audited declarations, exit 0, 3.918 seconds. No unrelated work or
newer commit was reset/discarded.

Ten letters-only modules add 245 explicit declarations and 368 audited
declarations including generated ones. DECLARATIONS.txt retains every explicit
signature/source anchor. Root imports include every production module; 95
selected axiom prints supplement the complete transitive audit. All older
DosenPetric bytes, grammars/equations/Positive/G/Rewire, AtomicFormula,
Atomized/CutFree/Topmost, predecessors and rank definitions are unchanged.
Reduced remains 21 term/61 inherited equation schemas, Positive 19 and G 16.
Lean 4.35.0, Init-only manifest/dependency policy, AGENTS, manuscript v4 and
historical reports/reviews/access records are preserved. No arbitrary-endpoint
zero, empty-sequent proof, interpretation-kernel quotient or new generating
equation is introduced.

An intervening SSH-origin commit, 2d240b2aa578b84277f59524d9f8819a41273a0d,
added manuscript v5 while retaining v4, with no Lean-source change. Verified
checkpoint work was preserved in local stash dedfd8fc8cd49930e9a162d5be585215b062a43c;
main fast-forwarded, then the work was reapplied. The README conflict was
resolved by retaining both the upstream v5/literature/review links and the new
proof-stage links. The statement map retained its upstream v5 header and the
new proof row. All other upstream changed/new files, including AGENTS, both
manuscript versions, checksums and v5 reports/evidence, were verified byte-for-
byte against that commit. No manuscript prose was edited by this checkpoint.
All required checks were repeated on the integrated tree; their new results
are the final verification record. The backup stash is retained locally.

## Source correspondence

The directly consulted source is Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed pp.248–253 correspond to PDF pp.260–265, one-based. Printed p.251
was also inspected in rendering. Source-access artifacts and hashes are
retained; historical access records are unchanged. No new source discrepancy
was confirmed.

| Source location | Typed local condition | Lean construction / actual proof input |
| --- | --- | --- |
| §11.2 p.251 (W1), γ=wL | Inner E contraction is entirely inside one fixed outer C gap; every outer selected C occurrence is parametric through it. Independent n,m≥2. | `Disjoint.fixedGap`, all eight `Data.upper/lowerC0/C1/E0/E1` equalities, `W1.DisjointContraction.fixedGap_left`. |
| §11.2 p.252, right analogue | Same fixed-gap placement in the succedent, actual G.contractR constructor order. | `fixedGap_right`; separately typed coproduct square and denotation calculation, without arrow negation. |
| §11.2 p.248, clusters / upper parametric sequences | Selected copies of one family have singleton fibers through the other contraction, with all equal-label tags retained. | `selectedC/E_transport`, `selectedC/E_singleton`, `xC/xE_fiber`, `other_fiber`. |
| §11.2 p.249, rank counts all cluster nodes | Sum all n or m selected copies; count a single node on the other retained/fixed path. | Actual `ContractionBlock.rankL/R_sum/fixed`; four table entries for each side, both balances, strict comparisons and other-position 2+rho. |
| §11.2 p.251 (W3) | Shared-selected-copy contraction, where a retained inner position is itself selected by the outer contraction. | Separate/open; excluded here by the proved fixed-gap separation and distinct retained indices, including C=E. |
| §11.2 pp.250–253, Reducibility/Blocked-w | Later applications tie a contraction to a cut and control replacement at all affected sites. | Not supplied by these two local commutations or the displayed two-position sum. |

The source's Semilattice Coherence appeal is replaced for these instances by
a concrete positional square and the already proved product/coproduct universal
component laws in Reduced.Hom. No source citation is treated as a Lean proof.
Constants and atomic-zero bases remain available through the unchanged Gentzen
syntax; no new constant/zero equation or empty-context identification is used.


## Eight context equalities and four actual routes

The coordinate theorems prove, without definitional reassociation:

| Declaration in Disjoint.Data | Actual equality |
| --- | --- |
| upperC0 | repeated C outer0 ++ Θ = F |
| lowerC0 | gaps outer0 ++ C :: Θ = FC |
| upperC1 | repeated C outer1 ++ Θ = FE |
| lowerC1 | gaps outer1 ++ C :: Θ = K |
| upperE0 | repeated E eUpper ++ upAfter = F |
| lowerE0 | gaps eUpper ++ E :: upAfter = FE |
| upperE1 | repeated E eLower ++ loAfter = FC |
| lowerE1 | gaps eLower ++ E :: loAfter = K |

countC proves outer1.length=outer0.length; countE0/countE1 prove both inner
copy-list lengths equal es.length. Constructor bounds are derived from these
identities. ContractionBlock packages the actual copies construction with
upper/lower context equalities. It adds derived helpers, not a new Gentzen
constructor or presentation equation. Its casts use G.reindex, At.cast and
Route.cast. The four routes have precisely these directions:

```text
c0 : Route FC F     e0 : Route FE F
c1 : Route K FE     e1 : Route K FC.
```

The all-position square is c1.get(e0.get a)=e1.get(c0.get a) for every formula
and a : At F A. A bounded numerical splice lemma proves copies naturality
for a map of one fixed block; the inner map is the actual copyIndex es,
whose bound and terminal behavior are proved recursively. This covers both
selected families and fixed prefix, gap and suffix positions. It is not an
assumed square or an association-only argument.

With p(w)=ofTerm w.product and q(w)=ofTerm w.coproduct, universal component
extensionality and Route.product_get/coproduct_get prove:

```text
p(c1);p(e0) = p(e1);p(c0) : ante K → ante F
q(e0);q(c1) = q(c0);q(e1) : succ F → succ K.
```

Thus oldL has path ante K→ante FE→ante F→succ Δ and newL has path
ante K→ante FC→ante F→succ Δ. OldR has path ante Γ→succ F→succ FE→succ K;
newR has path ante Γ→succ F→succ FC→succ K. Actual casted contraction
denotations and Reduced associativity give both required equalities.
No occurrence equality or inclusion equality is reflected to Reduced equality;
no coherence or contravariant arrow-negation operation is assumed.

## Complete selected transport and fixed fibers

All four selected lists are exactly selectedCopies transported by their actual
upper context equalities. The complete ordered statements are:

```text
selectedC1 = selectedC0.map e0.get
selectedE1 = selectedE0.map c0.get
lengths(selectedC0,selectedC1,selectedE0,selectedE1) = (n,n,m,m).
```

Every selected E position lies inside the designated fixed outer gap. Every
selected C position lies outside that entire gap; selected_disjoint compares
indices even when C=E. Required order preservation and injectivity are proved
on these particular lists, using the fixed-position exclusions. The maps are
not declared globally injective or globally monotone. The injectivity helpers
actually need membership of only the second argument: its nonretained image
already has a singleton fiber.

Every selected C copy has a complete singleton fiber through E contraction;
every selected E copy has one through C. Their images avoid the other
retained position. No selected copy is discarded, reordered or deduplicated
by formula equality. The retained intermediate positions keepC0 in FC and
keepE0 in FE have the proved images e1.get keepC0=xC and c1.get keepE0=xE.
The entire fibers above those final positions through the other contraction
are respectively [keepC0] and [keepE0]. The indices satisfy:

```text
xE.index = loBefore.length + (gaps es).length
xC.index = xE.index + 1 + V.length + (gaps post).length
xE.index < xC.index.
```

Both composite routes send each original selected family to its own retained
final position. For every other final At position z, with indices distinct
from xC and xE, middleE/middleC and originalViaE/originalViaC compute the
fixed inverse positions through each route. original_agree proves the two
original positions equal. other_fiber proves the complete singleton fiber
of each composite; there are no extra original predecessors. Equal labels
are never substituted for equality of positions.

## Exact ranks and preservation

For each sequent side separately, LC and LE name the existing contraction
ranks of innerC and innerE, respectively, directly on f. They require no
CutFree or Atomized premise. Complete selected sums and the genuine same-side
fixed singleton fibers prove:

| Proof | Rank at xC | Rank at xE |
| --- | --- | --- |
| old: C after E | LC+n | LE+1 |
| new: E after C | LC+1 | LE+m |

oldC_contractionL/R gives the outer C contraction rank LC+n;
newE_contractionL/R gives the outer E contraction rank LE+m. These are
contraction-subterm comparisons to LC/LE. The retained endpoint statements are:

```text
rho(old,xC)+1 = rho(new,xC)+n
rho(new,xE)+1 = rho(old,xE)+m
rho(new,xC) < rho(old,xC)
rho(old,xE) < rho(new,xE)
LC < rho(old,xC)
LE < rho(new,xE).
```

Old→new lowers the targeted C endpoint by n−1 and raises the E endpoint by
m−1. For the sum S of only these two displayed endpoint ranks:

```text
S(old)+m = S(new)+n.
```

Equal arities give equal sums. The checked n=2,m=3 example, including an
actual Empty P constant premise, gives S(new)=S(old)+1. This sum is not a
supplied decreasing measure. Both ranks at every other final same-side
position are 2+rho(f,originalViaE z hc he), with explicit common original
coordinate. The earlier opposite-side contraction lemmas are not used for
these same-side fibers. Existing all-node rho is unchanged; no quotient rank
invariance, arbitrary-context decrease, general Reducibility, Blocked-w or
unrestricted terminating rewrite system is claimed.

Both cutCounts equal f.cutCount. CutFree and Atomized equivalences compile;
both old/new Atomized predicates equal f.Atomized with no extra atomicity
condition. Complete tagged occurrence equality follows by congrArg occurrenceMap
from proved Reduced equality, never conversely. Constants retain whole-formula
positions even when their literal-occurrence types are empty.

## Compiled boundary examples

- twoThree T implements C=E=T, pre=[[]], post=[], U=V=Θ=[], es=[[T],[],[]].
  equal_label_indices checks C0=[0,5], E0=[2,3,4], C1=[0,3], E1=[1,2,3],
  retained E/C indices 1/2, and both composite index maps [2,0,1,1,1,2].
  equal_label_fixed_tag checks the original fixed index 1 is unselected and
  becomes final fixed index 0. These calculations use the actual typed routes.
- literal_left/right use actual six-formula premises containing G.cut;
  both_signs_actual_cuts specializes to positive and negative literals,
  retaining cutCount 1. No global inhabitant hypothesis is imposed on P.
- emptyP_two_three_left/right use genuinely inhabited constantLeft/constantRight
  proofs over Empty. emptyP_sum_increases and emptyP_fixed_rank check the
  unequal-arity sum increase and other-fixed rank equality for an actual premise.
- emptyP_compound_left/right use compound C/E, nonempty fixed gap/tail context,
  and independent n=3,m=2. emptyP_equal_arity uses n=m=2 with empty surrounding
  gaps and tails. Every example is in the audited import closure.

## Verification and evidence

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` (baseline) | 0 | 3.918 | baseline.log |
| `bash scripts/verify.sh` | 0 | 11.231 | strict.log |
| `python3 scripts/check-audit-boundaries.py` | 0 | 12.885 | audit-boundaries.log |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 2.281 | presentation-boundaries.log |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.03 | manuscript.log |
| `git diff --check` | 0 | 0.025 | diff-check.log |


Final actual result: **162 Lean files / 6,310 audited project declarations**,
with complete public import closure and transitive axiom audit. Permitted
axioms remain propext, Quot.sound and Classical.choice; 95 selected prints
are retained. No choice-free claim. All five negative controls reject with
expected diagnostics and Lean exit 1: public custom axiom, unused private
custom axiom, hidden external axiom, distinct tagged projections by rfl, and
zero without a correctly typed existing-arrow witness. Their exact sources,
commands, diagnostics and hashes are retained outside production imports.

All heavy builds/audits were sequential, including exploratory checks. Failed
splice/Nat/list calculations, unused/non-progress simp diagnostics, typed
position abbreviations, explicit arity binding and rank sum/At/Place
normalization are retained. A combined coordinate example hit the default
200000-heartbeat limit in a 68-second Lean run; small selected-index and
route-component lemmas replaced the expensive repeated expansion without
raising the limit. A List.mem_map argument placement was corrected. No
statement, presentation equation or frozen interface was weakened. Final
required verification followed every final proof change; later edits concern
reports/current records only. The staged diff whitespace check also passed.

Evidence: provenance/wsl-gentzen-w1-disjoint-contraction/.
SOURCE_SHA256SUMS inventories the checked Lean/configuration/script bytes;
EVIDENCE_SHA256SUMS covers logs, failures, controls, access artifacts, complete
signatures and boundary records. REPORT_SHA256SUMS and RECORD_SHA256SUMS cover
final reports and current maps/README.

- Strict log: `670c74b89fa1173ecdfdda6698ef230f08d04532a3e4c0ede7e49b82e3f48541`.
- Checked source inventory: `fa060fac608c7f551d08ee2957cfb13e8eb674b40aa71ce7843a2566792dba13`.
- Evidence inventory: `56addc2e809764a55e92c9852470070efbe98c4f63bbe4e5ad10b2536fec0908`.

Baseline, checked working sources and final committed bytes are distinct.
Post-commit source/evidence checks, live SSH ref agreement and byte-for-byte
Downloads comparisons have separate committed-source.json, remote-final.json
and delivery.json receipts in .codex-work/gentzen-w1-disjoint-contraction/.
The final response gives the commit and delivery paths without a circular
commit hash inside its own report. Differing existing Downloads files are
preserved using dated/commit-suffixed names.

The [hostile review](reviews/GENTZEN_W1_DISJOINT_CONTRACTION_HOSTILE.md) and
[writing review](reviews/GENTZEN_W1_DISJOINT_CONTRACTION_WRITING.md) are
AI-assisted author-side reviews of the actual proofs/statements/correspondence,
not independent certification. The verified governing KLR cache was consulted
directly. Historical access records and manuscript v4 are unchanged. No
review/process commentary entered manuscript prose or LaTeX comments.
Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
Palomar preparation/submission, publication, licensing and visibility changes
were not performed.

## Next concrete obligation

Next prove terminal-tail disjoint same-side contraction and its right dual.
For arbitrary P,C,E, gs,hs,H,U,V and Δ/Γ, set es=H::hs and require independent
2≤gs.length and 2≤es.length. Define:

```text
upBefore = repeated C gs ++ U
loBefore = gaps gs ++ C :: U
F  = upBefore ++ repeated E es ++ V
FE = upBefore ++ gaps es ++ E :: V
FC = loBefore ++ repeated E es ++ V
K  = loBefore ++ gaps es ++ E :: V.
```

For f : G P F Δ, old first applies E contraction with gaps
`(upBefore ++ H)::hs` and tail V, then C contraction with gaps gs and tail
`U ++ gaps es ++ E :: V`. New first applies C contraction with gaps gs and
tail `U ++ repeated E es ++ V`, then E contraction with gaps
`(loBefore ++ H)::hs` and tail V. Both results must have type G P K Δ.
The right dual starts with f : G P Γ F and must finish at G P Γ K using
G.contractR. All endpoint identifications must be proved and used explicitly.
Every selected E occurrence lies in the fixed terminal tail; every selected
C occurrence lies before that tail and remains parametric through E. Prove
these positional conditions even C=E, the copies/copies square, complete
ordered transports, fixed fibers, exact denotation and independently directed
rank table. The retained C position precedes retained E here; the completed
interior-gap index ordering cannot simply be copied. No terminal construction
or conclusion is assumed by this checkpoint.

Interleaved/shared-selected contractions, including source W3, crossing-selected,
multi-gap and absorption exchange configurations, remaining W1, W2–W6,
arbitrary-context replacement/all-site decrease, Reducibility, Blocked-w,
cut elimination, required positive coherence inputs, PositiveCoherence,
Reduced.Faithful, Boolean Coherence, unconditional maximality and Palomar
preparation remain separate/open. Existing conditional transfers are unchanged.
An unfinished formalization of cited published work does not establish a
manuscript defect.
