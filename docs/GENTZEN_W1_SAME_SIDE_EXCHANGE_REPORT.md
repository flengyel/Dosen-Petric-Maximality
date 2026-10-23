# W1 same-side exchange inside fixed gaps and tails

## Proved endpoints and hypotheses

For arbitrary `P : Type u`, `C : NormalForm P`, context lists and premise f,
with only `hn : 2 ≤ gs0.length`, four concrete commutations compile in
`DosenPetric.Reduced.Gentzen.W1.SameSideExchange`:
`interior_left`, `interior_right`, `terminal_left`, `terminal_right`.
There is no inhabitant, decidable equality, enumeration, freshness, atomicity,
CutFree, Atomized, coherence or equality-reflection premise. Both literal
signs, constants, compound formulas, empty blocks and premises with cuts are
permitted. Equality is in the existing generated Reduced.Hom quotient.
`a ; b := comp a b` executes a first.

These theorems construct LeftLaws/RightLaws results. The coordinate record's
concrete interior/terminal constructors prove every field, including numerical
routing and positional exclusion. The concrete results do not assume a square,
selected transport, denotation equality or rank conclusion.

For the interior placement:

```text
gs0 = pre ++ (U ++ X ++ Y ++ V) :: post
gs1 = pre ++ (U ++ Y ++ X ++ V) :: post
tail0 = tail1 = Θ
upBefore = repeated C pre ++ U
upAfter = V ++ C :: (repeated C post ++ Θ)
loBefore = gaps pre ++ U
loAfter = V ++ (gaps post ++ C :: Θ).
```

For the terminal placement:

```text
gs0 = gs1 = gs
tail0 = U ++ X ++ Y ++ V
tail1 = U ++ Y ++ X ++ V
upBefore = repeated C gs ++ U
upAfter = V
loBefore = gaps gs ++ C :: U
loAfter = V.
```

For either, write U0=upBefore++X++Y++upAfter, U1=upBefore++Y++X++upAfter,
K0=loBefore++X++Y++loAfter and K1=loBefore++Y++X++loAfter.
The actual list equalities are proved:

```text
upper0 : repeated C gs0 ++ tail0 = U0
upper1 : repeated C gs1 ++ tail1 = U1
lower0 : gaps gs0 ++ C :: tail0 = K0
lower1 : gaps gs1 ++ C :: tail1 = K1
count_eq : gs1.length = gs0.length.
```

They are used through G.reindex, At.cast and Route.cast, rather than assumed
as definitional associativity. modifiedArity derives the required gs1 bound.
The exact common old/new endpoints are:

| Concrete case | Arbitrary premise | Both outer proof types |
| --- | --- | --- |
| interior_left | G P U0 Δ | G P ((gaps pre ++ U) ++ Y ++ X ++ (V ++ (gaps post ++ C :: Θ))) Δ |
| interior_right | G P Γ U0 | G P Γ ((gaps pre ++ U) ++ Y ++ X ++ (V ++ (gaps post ++ C :: Θ))) |
| terminal_left | G P U0 Δ | G P ((gaps gs ++ C :: U) ++ Y ++ X ++ V) Δ |
| terminal_right | G P Γ U0 | G P Γ ((gaps gs ++ C :: U) ++ Y ++ X ++ V) |

The shared definitions use only existing G constructors:

```lean
innerL := (G.contractL C gs0 tail0 Δ hn
  (f.reindex upper0.symm rfl)).reindex lower0 rfl
oldL := (G.contractL C gs1 tail1 Δ (modifiedArity d hn)
  ((G.exchangeL upBefore X Y upAfter Δ f).reindex upper1.symm rfl)).reindex lower1 rfl
newL := G.exchangeL loBefore X Y loAfter Δ innerL

innerR := (G.contractR Γ C gs0 tail0 hn
  (f.reindex rfl upper0.symm)).reindex rfl lower0
oldR := (G.contractR Γ C gs1 tail1 (modifiedArity d hn)
  ((G.exchangeR Γ upBefore X Y upAfter f).reindex rfl upper1.symm)).reindex rfl lower1
newR := G.exchangeR Γ loBefore X Y loAfter innerR
```

Here d is the constructed coordinate record. In all four cases,
`denoteL/R` prove `ofTerm new.denote = ofTerm old.denote`.
Exchanges crossing selected positions, spanning several gaps, and the source's
exchange-absorption configurations are outside this checkpoint.

## Baseline and unchanged interfaces

Clean main at `cae55c378d6e42adcac61f38c5ea12cea4bd98b3` agreed with fetched
SSH origin. Actual strict baseline passed: 130 Lean files / 5,275 audited
declarations, exit 0. Baseline.json retains measured time and hashes. No
intervening commit or unrelated working change was discarded. All preceding
presentation, reduction, factorization, zero/union, G0/G1, atomization, tracing,
rank and W1 infrastructure is reused.

Nine letters-only modules add 162 explicit source declarations: GapExchange
Indices/Data/Routing, ExchangeEmbeddings and SameSideExchange core/Ranks/
FixedRanks/Instances/Examples (each with the Gentzen prefix). The exhaustive
audit counts 294 new declarations including generated projections/constructors.
Root imports and 70 selected axiom prints are added. DECLARATIONS.txt gives
exact source names, line anchors and declaration signatures.
All older DosenPetric module bytes, frozen syntax/equations/Positive/G/Rewire/
predicates/predecessors/ranks, manuscript v4, AGENTS, historical reports and
access records are preserved. Reduced remains 21 constructor/61 equation
schemas, Positive 19 and G 16. Lean remains 4.35.0; Init-only dependencies and
manifest are unchanged. No arbitrary-endpoint zero is introduced.

## Source correspondence

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also in rendering. The verified existing cache was used. Constant and
zero extensions on pp.272–273 and 291–292 remain compatible with the unchanged
syntax. Source-consultation.json records caches, hashes and access artifacts;
historical access records remain intact. No new source discrepancy was confirmed.

| Source location | Precise local correspondence / side conditions | Lean declarations and actual proof inputs |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ=cL | Left exchange entirely inside one fixed gap or the fixed terminal tail commutes with left contraction. Every selected copy stays outside the exchanged interval. | `GapExchange.interior/terminal`; `W1.SameSideExchange.interior_left/terminal_left`; proved copies/exchange product square and associativity. |
| §11.2 p.252, right analogue | Right exchange at the corresponding fixed positions commutes with right contraction. | `interior_right/terminal_right`; independently typed coproduct square. |
| §11.2 pp.248–249, parametric ancestry and all-node rank | Exchange routes every whole-formula position bijectively; complete selected-copy sum counts one exchange node per copy. | At.swapBlocks inverse/injectivity; complete same-side predecessor singleton, rho_exchangeL/R_embedded; selected_transport and existing contraction sums. |
| §11.2 p.251, broader cL cases and absorption alternative | Exchanges across selected positions, across several gaps, or absorbed by contraction are not covered here. | No such theorem is supplied. The source's Semilattice Coherence appeal is replaced only for the four fixed-position cases by derived universal component laws. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants and atomic zero leaves remain admitted; empty sequent folds remain differently coloured. | Actual constant examples over Empty; generic premises including cuts/zeros. No new zero equation or arrow constructor. |

Composition is left-first throughout. The binary folds are not strictified;
all needed list equalities and endpoint transports are explicit.

## Routing and categorical equality

The actual copies routes are c0 : Route K0 U0 and c1 : Route K1 U1, cast with
the four list equalities. swapUpper : At U0 A→At U1 A and
swapLower : At K0 A→At K1 A use the existing At.swapBlocks. For every A and a:

```text
c1.get (swapUpper a) = swapLower (c0.get a).
```

copyIndex_interior and copyIndex_tail prove the numerical square by induction
on the surrounding gap lists. exchangeIndex splits prefix, X, Y and suffix;
typed At.index_injective gives the square for every position, not only selected
copies. At.swapBlocks_inverse and injectivity are derived explicitly, including
empty blocks and equal labels.

For p(w)=ofTerm w.product and q(w)=ofTerm w.coproduct, the structural squares are:

```text
p(c1) ; eUpperL = eLowerL ; p(c0) : ante K1 → ante U0
eUpperR ; q(c1) = q(c0) ; eLowerR : succ U0 → succ K1.
```

The eL arrows are the actual `.conj` exchange comparison invTerm; the eR arrows
are the `.disj` comparison toTerm. exchangeBack_component specializes to
exchangeL_projection and exchangeR_injection. product_positions and
coproduct_positions, with the established route component laws, prove both
squares in Reduced.Hom. These are derived universal properties; no occurrence
faithfulness, inclusion reflection or Semilattice Coherence is assumed.

The full typed execution paths are:

```text
oldL: ante K1 --p(c1)--> ante U1 --eUpperL--> ante U0 --f--> succ Δ
newL: ante K1 --eLowerL--> ante K0 --p(c0)--> ante U0 --f--> succ Δ
oldR: ante Γ --f--> succ U0 --eUpperR--> succ U1 --q(c1)--> succ K1
newR: ante Γ --f--> succ U0 --q(c0)--> succ K0 --eLowerR--> succ K1.
```

contractL_cast_denote/contractR_cast_denote discharge the reindexings;
denoteL/R use the proved squares and Reduced associativity. Associativity
alone would not prove the squares. No new Route/Rewire constructor is added.

## Selected and fixed positional correspondence

selected0/selected1 are the complete selectedCopies lists cast by upper0/upper1.
The proved equation is an equality of ordered lists:

```text
selected1 = selected0.map swapUpper.
```

selected0_outside and selected1_outside prove that every selected index lies
before the upper exchange interval or at/after its end. This is derived from
the fixed gap/tail decomposition even if X or Y contains further copies of C.
The block swap is not globally monotone. selected0_index_fixed proves index
preservation only for selected entries using interval exclusion. Together
with the existing ordered selected lists, two-sided membership and swap
invertibility, this proves selected_transport. No occurrence is deduplicated.

The retained positions are the canonical retained C positions cast by lower0
and lower1; retained proves swapLower keep0=keep1. For any formula A and fixed
lower a : At K0 A with a.index≠keep0.index, fixed0 a ha is the unique original
upper position supplied by fixedCopyAt. fixed0_get proves its copies image.
fixed_canonical_image and fixed_transport_fiber prove that the modified
contraction's complete singleton fiber is precisely the transported swapUpper
of that original upper position. Both use fiber_copies_fixed and concrete
casts, not an opposite-side contraction lemma. The inverse lower swap
originalLower covers every final lower position; original_fixed preserves
exclusion of the retained position. Equal labels never identify positions.

## Exact predecessor and rank equations

For every original typed position a, predecessors_exchangeL/R_embedded prove
a complete singleton predecessor list at swapUpper a using the actual
Premise.parent and fiber definitions. Therefore:

```text
rho(exchangeL f,left,swapUpper a) = 1 + rho(f,left,a)
rho(exchangeR f,right,swapUpper a) = 1 + rho(f,right,a).
```

An explicit exchange contributes a node even when either or both blocks are
empty, or its denotation is identity. Rank is attached to the proof syntax.
Let n=gs0.length=gs1.length, let Rnew/Rold be the existing contraction ranks
of inner/old with their canonical casts, and set x=keep1. For all four cases:

```text
Rold = Rnew + n
rho(old,x) = Rold
rho(new,x) = Rnew + 1
rho(old,x) + 1 = rho(new,x) + n
Rnew < Rold
rho(new,x) < rho(old,x).
```

The complete ordered selected transport and contractionRankL_eq/R_eq sums
count one exchange node per selected upper copy. selectedCopies length and
sum_map_one_add give n; strictness uses n≥2. The contraction subterm loses n
nodes, while the whole retained endpoint loses n−1.

For every other same-side position a : At K0 A, put b=fixed0 a ha.
fixed_oldL/R_rank and fixed_newL/R_rank prove both old and new ranks at
swapLower a equal `2 + rho(f,b)`. Each path has one exchange node and one
fixed contraction node. fixed_rankL/R_at states this for every final fixed
z : At K1 A using originalLower z; no position is omitted. Exchange introduces
no principal leaf and there is no thinning-style inserted-position 2→1 result.
These are local cluster equations, not cut rank, cutCount, proof size, quotient
invariance, arbitrary-context decrease or a general termination measure.

## Preservation and compiled boundaries

Both pairs preserve cutCount exactly, CutFree/Atomized equivalently, and the
complete tagged occurrence relation. Both old.Atomized and new.Atomized are
proved equivalent to f.Atomized, with no new AtomicFormula condition. Neither
premise is duplicated. relationL/R applies congrArg occurrenceMap to the
already proved Reduced equality; it never reflects occurrence equality.
Both signs, empty occurrence types and repeated tags remain in the full types.

| Compiled boundary | Concrete evidence |
| --- | --- |
| Three copies and repeated equal fixed formulas | repeated_left/right use three selected copies and two equal fixed gap copies. selected indices remain [0,3,4]. repeated_endpoint_loss proves retained endpoint loss exactly 2. |
| `[C]` exchanged with `[C]` | equal_label_transposition and fixed_equal_positions_swap show the fixed tags 0/1 transpose despite identical context lists; retained tag 2 is separate. repeated_fixed_rank checks unchanged rank at an exchanged fixed tag. |
| X empty, Y empty, both empty | one_empty_left/right and both_empty_left/right instantiate the full laws with actual cut-containing premises. Empty exchange nodes remain counted. |
| Nonempty gap halves/tails and unequal lengths | All four Empty P constant examples have nonempty U,V, interior tail Θ where applicable, and block lengths 1 and 2. topPremise/botPremise provide genuinely inhabited proof types. |
| Compound formulas | compound_left/right use an actual compound fixed formula with arbitrary premise; equality/rank and predicate equivalence require no new atomicity. |
| Both signs and actual cuts | both_signs_actual_cut instantiates positive/negative literals and retains cutCount 1. |

## Verification and evidence

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 7.746 | `baseline.log` |
| `bash scripts/verify.sh` | 0 | 9.874 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 9.945 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.592 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.025 | `manuscript.log` |
| `git diff --check` | 0 | 0.019 | `diff-check.log` |

Actual final result: **139 Lean files / 5,569 audited declarations**.
Public import closure passed. All five expected negative controls reject with
Lean exit 1 and expected diagnostics:

| Fixture | Tested rejection | Result |
| --- | --- | --- |
| direct-axiom | Public custom axiom. | Rejected, exit 1. |
| private-axiom | Unused private custom axiom. | Rejected, exit 1. |
| hidden-dependency | Hidden external axiom dependency. | Rejected, exit 1. |
| identified-projections | Distinct tagged projections identified by rfl. | Rejected, exit 1. |
| zero-without-arrow-witness | Missing correctly typed existing-arrow witness. | Rejected, exit 1. |

Permitted axioms remain propext, Quot.sound and Classical.choice. All project
declarations are transitively audited; 70 complete selected axiom prints are
retained. No choice-free claim is made. Production contains no proof holes,
custom mathematical axioms or native_decide. Negative fixtures stay outside
production imports. Every heavy verification process was sequential.

All failed numerical/list, unused-simp, At/Place predecessor, typed-sum and
fixed-rank elaborations, and quantified bundle-lambda attempts retain logs,
commands, exit statuses and timings. They were corrected without weakening
any target or frozen interface. Final required verification followed the last
proof changes; subsequent changes are documentation only.

Evidence: `provenance/wsl-gentzen-w1-same-side-exchange/`. DECLARATIONS.txt lists
all 162 explicit source signatures. SOURCE_SHA256SUMS inventories checked
Lean/configuration/scripts; EVIDENCE_SHA256SUMS inventories commands, logs,
source-access artifacts, negative fixtures and boundary records. Finalized
reports/current records have REPORT_SHA256SUMS and RECORD_SHA256SUMS.

- Strict log: `42598fef11ef3ef2a821d7c2a2a86fd1aebf659a8a35cb56cd5cb93f8aee18c9`.
- Checked source inventory: `0294dc30796285006ca5b7baaf9dd13044349b65756adcd1641dae0169a31310`.
- Evidence inventory: `ce0c7abf78a9f089b36af079afe3c7a5308afc633f82a68744bca2b480403fc8`.

Baseline, checked working sources and committed sources are distinct records.
Post-commit source/report/evidence comparisons, SSH refs and Downloads delivery
are retained in committed-source.json, remote-final.json and delivery.json
under .codex-work/gentzen-w1-same-side-exchange/. Reports are compared against
committed Git objects; differing existing Downloads files are preserved with
dated/commit-suffixed names. These receipts avoid a circular commit hash in its
own report. The final response supplies the commit and delivered paths.

The [hostile review](reviews/GENTZEN_W1_SAME_SIDE_EXCHANGE_HOSTILE.md) and
[writing review](reviews/GENTZEN_W1_SAME_SIDE_EXCHANGE_WRITING.md) are
AI-assisted author-side reviews of actual proofs and correspondence, not
independent certification. The verified Knuth–Larrabee–Roberts cache was
directly consulted. Manuscript v4 and historical access records remain
unchanged; no review/process prose entered manuscript text or LaTeX comments.
Independent kernels/source replay, Challenge/Solution/Comparator, official
preflight/service verification, fresh manuscript compilation/layout review,
publication, licensing and visibility changes were not performed.

## Remaining scope and next concrete obligation

Next prove same-side unary conjunction-left introduction through contraction
at a specified fixed interior gap, and its disjunction-right dual (§11.2 p.251
W1 with γ=∧L; p.252 dual). This is a proposed proof obligation, not a production
axiom or completed theorem.

For arbitrary P : Type u, A,B,C : NormalForm P,
pre,post : List (List (NormalForm P)) and U,V,Θ,Δ : List (NormalForm P), put:

```text
gs0 = pre ++ (U ++ A :: B :: V) :: post
gs1 = pre ++ (U ++ .conj A B :: V) :: post
upBefore = repeated C pre ++ U
upAfter = V ++ C :: (repeated C post ++ Θ)
loBefore = gaps pre ++ U
loAfter = V ++ (gaps post ++ C :: Θ).
```

Require 2≤gs0.length and take
`f : G P (upBefore ++ A :: B :: upAfter) Δ`.
Construct old by `G.conjL upBefore upAfter Δ A B f`, then contraction at
gs1/Θ after the proved upper reindexing; construct inner by contraction at
gs0/Θ and new by `G.conjL loBefore loAfter Δ A B inner`.
Both outer proofs must have exact type
`G P (loBefore ++ .conj A B :: loAfter) Δ`.
Prove all context equalities, the actual copies/conjLeft.toTerm structural
square and Reduced denotation equality. All selected upper contraction copies
must avoid the two fixed premise slots of A/B, and all selected lower copies
must avoid the introduced principal compound slot, even if its label equals C.
Prove complete selected transport, targeted n/n−1 rank laws and correct
whole-formula principal ancestry/predicate/tagged-relation preservation.

The dual starts with `f : G P Γ (upBefore ++ A :: B :: upAfter)`, replaces
conj by disj in gs1, and uses `G.disjR` and `G.contractR`; its final type is
`G P Γ (loBefore ++ .disj A B :: loAfter)`.
Use actual Rules.conjLeft/disjRight directions, not an assumed arrow-negation
functor. Terminal-tail variants and other W1 configurations remain additional
work unless their constructions are also supplied.

Remaining exchange configurations include crossing selected contraction
positions, spanning several fixed gaps, and exchange absorption by contraction.
Other same-side W1 contractions/logical cases, W2–W6, arbitrary-context proof
replacement/all-site decrease, Reducibility, Blocked-w and cut elimination
remain open. Positive coherence inputs, PositiveCoherence, Reduced.Faithful,
Boolean Coherence and unconditional maximality are separate/open. Existing
conditional transfers remain unchanged. Missing formalization of a cited
published theorem does not by itself establish a manuscript defect.
