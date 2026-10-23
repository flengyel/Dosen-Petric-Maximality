# W1 opposite-side exchange commutations

## Proved endpoints and hypotheses

For arbitrary `P : Type u`, `C : NormalForm P`,
`gs : List (List (NormalForm P))` and `hn : 2 ≤ gs.length`, both local
commutations compile in `DosenPetric.Reduced.Gentzen.W1.Exchange`.
This fresh namespace leaves the established W1 thinning names unchanged.
Equality of arrows is in the existing syntactic Reduced.Hom quotient;
`a ; b` means comp a b, executing a first. No inhabitant of P, decidable
equality, enumeration, freshness, atomicity, Atomized, CutFree, coherence or
occurrence-faithfulness hypothesis is needed in the denotation/rank results.

For `Θ Δ X Y Λ : List (NormalForm P)` and:

```lean
f : G P (repeated C gs ++ Θ) (Δ ++ X ++ Y ++ Λ)
```

define:

```lean
oldL := G.contractL C gs Θ (Δ ++ Y ++ X ++ Λ) hn
  (G.exchangeR (repeated C gs ++ Θ) Δ X Y Λ f)
innerL := G.contractL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f
newL := G.exchangeR (gaps gs ++ C :: Θ) Δ X Y Λ innerL
```

Both outer terms have exactly type
`G P (gaps gs ++ C :: Θ) (Δ ++ Y ++ X ++ Λ)`.
`W1.Exchange.denoteL` proves `ofTerm newL.denote = ofTerm oldL.denote`.

For `Γ X Y Θ Λ : List (NormalForm P)` and:

```lean
f : G P (Γ ++ X ++ Y ++ Θ) (repeated C gs ++ Λ)
```

define:

```lean
oldR := G.contractR (Γ ++ Y ++ X ++ Θ) C gs Λ hn
  (G.exchangeL Γ X Y Θ (repeated C gs ++ Λ) f)
innerR := G.contractR (Γ ++ X ++ Y ++ Θ) C gs Λ hn f
newR := G.exchangeL Γ X Y Θ (gaps gs ++ C :: Λ) innerR
```

Both outer terms have exactly type
`G P (Γ ++ Y ++ X ++ Θ) (gaps gs ++ C :: Λ)`.
`W1.Exchange.denoteR` proves `ofTerm newR.denote = ofTerm oldR.denote`.
These are derived combinations of existing constructors.

## Baseline and preserved construction

Clean main started at `0cee16207484a43a2759c87beb67e0ba5ebc00d1`.
Git status and fetched SSH origin agreed; there were no newer commits or
unrelated changes to preserve. Actual baseline strict verification passed
with 109 Lean files / 4,794 audited project declarations; baseline.json
retains its measured elapsed time and exit 0. All presentation, normalization,
reduction, common factorization, zero/union, G0/G1, Atomic-k, cluster/rank and
W1 thinning constructions are reused unchanged.

Four letters-only modules are added: GentzenOppositeExchangeRank,
GentzenExchangeCommutation, GentzenExchangeCommutationRank and
GentzenExchangeCommutationExamples, with root public imports and 35 selected
axiom prints. All pre-existing DosenPetric modules are byte-identical to the
baseline, including 21 reduced constructor schemas, 61 reduced equation
schemas, 19 Positive schemas, 16 G schemas, all proof predicates, predecessors
and rank definitions. Lean 4.35.0, Init-only dependencies, manifest, audit
scripts, AGENTS, manuscript v4 and historical reports/access records are
preserved. boundaries.json inventories the unchanged bytes.

## Source correspondence

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted;
p.251 was also inspected in rendering. The constant/zero extensions on
pp.272–273 and 291–292 were checked against the existing treatment.
Source-consultation.json records caches, hashes and access artifacts.
Historical source-access records are preserved; no new source discrepancy
was confirmed for these instances.

| Source location | Typed correspondence / scope | Lean declaration and actual proof input |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = cR | wL cR f = cR wL f; right exchange swaps the specified X,Y blocks and leaves antecedent contraction positions unchanged. | `W1.Exchange.oldL/innerL/newL`, `denoteL`; actual G.denote, ofTerm_comp, Reduced.Laws.assoc. |
| §11.2 p.252, right analogue of Reducibility | wR cL f = cL wR f; left exchange swaps X,Y and leaves succedent contraction positions unchanged. | `oldR/innerR/newR`, `denoteR`; separate checked associativity proof in the opposite direction. |
| §11.2 p.248, parametric sequences and predecessor definition | On the side opposite exchange, the exact typed At has one predecessor in the unique premise; no formula-label search. | `G.predecessors_exchangeR_left/exchangeL_right` from existing Premise.parent and TraceRoute.fiber_identity. |
| §11.2 p.249, rho and contraction rank; pp.251–252, rank requirement | Count all cluster nodes. Every selected upper copy contributes an exchange node. | `G.rho_exchangeR_left/exchangeL_right`; existing contractionRankL_eq/R_eq, selectedCopies_length and sum_map_one_add; `contraction_lossL/R`, `endpoint_lossL/R`, strict inequalities. |
| §11.5 pp.272–273, constants | Constants have whole-formula positions even with no literal occurrences. Empty folds are top/bot and remain differently coloured. | `emptyP_constantsL/R` use actual G Empty constant premises. Both-empty exchange still adds a node via rho equations. |
| §12.5 pp.291–292, atomic zero extension | Atomic zero leaves and arbitrary premises, including cuts, are allowed. No special zero law is needed for these two associativity calculations. | Generic results impose no restriction on f; atomic-zero constructor/zero equations are unchanged. No unwitnessed zero is added. |

The source invokes Semilattice Coherence for the larger W1 family. These two
local denotation equations are derived directly; the coherence theorem is
neither assumed nor claimed as a result. Binary context folds remain explicit,
with the actual exchange comparison arrows rather than strictified equality.

## Typed categorical calculations

The left path uses:

```text
ante (gaps gs ++ C :: Θ)
  -- (copies C gs Θ).product --> ante (repeated C gs ++ Θ)
  -- f.denote --> succ (Δ ++ X ++ Y ++ Λ)
  -- (exchange .disj Δ X Y Λ).toTerm --> succ (Δ ++ Y ++ X ++ Λ).
```

NewL denotes `(a ; f) ; b`, while oldL denotes `a ; (f ; b)`.
Expand the actual G.denote and ofTerm_comp, then apply Reduced.Laws.assoc.

The independent right path uses the inverse exchange comparison at the source:

```text
ante (Γ ++ Y ++ X ++ Θ)
  -- (exchange .conj Γ X Y Θ).invTerm --> ante (Γ ++ X ++ Y ++ Θ)
  -- f.denote --> succ (repeated C gs ++ Λ)
  -- (copies C gs Λ).coproduct --> succ (gaps gs ++ C :: Λ).
```

NewR denotes `a ; (f ; b)` and oldR `(a ; f) ; b`, so the proof uses
associativity in the reverse direction. No unproved structural-coherence law,
relation reflection, inclusion reflection or arrow-negation operation enters.

## Exact predecessors and ranks

For every selected position x on the unchanged side, the complete predecessor
list of the exchange proof is a singleton storing the exact same typed At in
its unique premise. `G.predecessors_exchangeR_left` and
`G.predecessors_exchangeL_right` derive this by unfolding existing branches
and parent routing and applying TraceRoute.fiber_identity. The proofs do not
search for an equal label. Applying rho_eq gives:

```text
rho(exchangeR f, left, x)  = 1 + rho(f, left, x)
rho(exchangeL f, right, x) = 1 + rho(f, right, x).
```

Let n = gs.length. In the left case set:

```lean
x := At.shift (gaps gs) (At.here C Θ)
Rnew := G.contractionRankL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f
Rold := G.contractionRankL C gs Θ (Δ ++ Y ++ X ++ Λ) hn
  (G.exchangeR (repeated C gs ++ Θ) Δ X Y Λ f)
```

The right case uses `x := At.shift (gaps gs) (At.here C Λ)`, right sequent
side, and contractionRankR at source contexts Γ++X++Y++Θ / Γ++Y++X++Θ.
For each direction the declarations prove:

```text
contraction_lossL/R:      Rold = Rnew + n
endpoint_rankL/R:         rho(new,x) = Rnew + 1
endpoint_lossL/R:         rho(old,x) + 1 = rho(new,x) + n
contraction_decreasesL/R: Rnew < Rold
endpoint_decreasesL/R:    rho(new,x) < rho(old,x).
```

The contraction loss proof uses the exact existing contractionRankL_eq/R_eq
sum over selectedCopies. Each entry contributes one exchange node;
sum_map_one_add and selectedCopies_length then give n additional nodes.
Every selected copy is retained, including adjacent equal copies. Fixed equal
formulas in gaps are different positions and are not added to that list.

Rold equals the selected endpoint rank of old by the contractionRank
definition. The new whole proof retains a single exchange root. Thus the
contraction subterm loses n nodes and the whole selected endpoint loses n−1,
with strictness using hn. The addition equation avoids truncated subtraction.
Empty X or Y, including both empty, obey the same equations: the explicit G
exchange is still a proof node, even when its denotation is an identity.
No identity-denotation simplification is applied to rank.

These results concern the selected syntactic cluster only, not every tied
site after replacement inside an arbitrary proof context. Cluster rho,
contraction rank, cut rank, cutCount and proofSize have distinct meanings.
No quotient descent or denotation invariance for rank is asserted.

## Preservation and focused checked boundaries

For each concrete pair, cutCountL/R, cutFreeL/R and atomizedL/R give:

```text
new.cutCount = old.cutCount
new.CutFree ↔ old.CutFree
new.Atomized ↔ old.Atomized.
```

These are definitional proofs: both counts equal f.cutCount, both CutFree
predicates equal f.CutFree, and both Atomized predicates equal f.Atomized.
Unlike thinning, exchange introduces no AtomicFormula condition.
newL_atomized/newR_atomized reuse f.Atomized directly. Premises may contain
cuts; the rewrites do not duplicate them. No count claim is generalized to
Atomic-k or other transformations.

`relationL/R` apply the established well-defined occurrenceMap to denoteL/R.
They prove equality of the entire tagged relations at unchanged endpoints,
including empty occurrence types. This direction never reflects relation
or inclusion equality to Reduced arrow equality. Whole-formula ancestry
and literal-occurrence relations remain separate.

| Checked boundary | Actual construction / result |
| --- | --- |
| Two selected copies, both exchanged blocks empty, constants and Empty P | emptyP_constantsL/R use the earlier actual constantPremiseL : G Empty [top,top] [top] and constantPremiseR : G Empty [bot] [bot,bot]; denotation equality and strict selected-endpoint decrease compile. |
| One exchanged block empty | one_empty_blockL/R retain the actual binary list expressions; empty_exchangeR_rank/empty_exchangeL_rank prove the extra node for both-empty exchanges at every position. |
| Three selected copies, fixed equal gap, repeated nonempty exchanged blocks | repeatedPremiseL/R are actual inhabited proof trees. gs = [[],[lit l],[]] selects three of four equal formula positions; X = [lit l,lit l], Y = [lit l]. repeated_with_cutL/R prove denotation equality, Atomized, cutCount 1 and whole endpoint loss exactly 2 at the explicit selected position. |
| Both signs and actual cuts | The repeated premises contain G.cut (G.identity l) (G.identity l); both_signs instantiates positive and negative literals. General repeated_with_cut results accept every Literal P. |
| Arbitrary formulas and empty occurrences | General proofs quantify NormalForm P and all lists without assumptions on P. Constants have genuine whole-formula positions although their literal-occurrence types are empty. |

## Verification, inventories and review scope

| Command | Exit | Elapsed seconds | Evidence log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 5.194 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 8.585 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.220 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.006 | `manuscript.log` |
| `git diff --check` | 0 | 0.006 | `diff-check.log` |

Final verification completed at 2026-10-23T11:59:37.773506+00:00: **113 Lean
files / 4,850 audited project declarations**. The new modules have
47 explicit source declarations, a different count from generated/environment
declarations. All heavy builds/audits, including exploratory checks, ran
sequentially. Commands, exit codes, timings, source hashes and diagnostics
are retained in `provenance/wsl-gentzen-w1-exchange/`.

All five expected controls were rejected with Lean exit 1 and their expected
diagnostics: public custom axiom, unused private custom axiom, hidden
external axiom dependency, reflexive identification of distinct tagged
projections, and zero construction without a correctly typed existing-arrow
witness. Exact fixtures, logs and the two control reports are retained.
Public import closure passed without modifying its letters-only parser.

The first exploratory attempt compiled all general proofs but rejected the
right one-empty-block example: X++Θ was not definitionally the constructor's
X++[]++Θ. The example now retains the actual list expression; no strictified
object equality was assumed. Both attempt logs and their elapsed-time/exit
records are preserved. No failed attempt is reported as passing.

Only propext, Quot.sound and Classical.choice are permitted. denoteL/R and
relationL/R print propext and Quot.sound; the rank results also print
Classical.choice via existing fiber infrastructure. CutFree, Atomized and
cutCount equivalences print no axioms. Thirty-five selected axiom prints are
retained verbatim; no choice-free claim is made. Production code has no
proof hole, custom mathematical axiom, native_decide, new equation or coherence
premise. Deliberately invalid fixtures remain outside production imports.

Evidence includes summary.json, baseline.json/verify.json, DECLARATIONS.txt,
SELECTED_AXIOMS.txt, SOURCE_SHA256SUMS and EVIDENCE_SHA256SUMS. Separate
REPORT_SHA256SUMS and RECORD_SHA256SUMS hash finalized reports and current
records, including README and the revised SSH setup instructions. Key hashes:

- Strict log: `2df2bb641d28bf433430fcb809beb0e95d2d2aef10ab310ead4d7504df6900fd`.
- Checked source inventory: `b2e488f165781be64857bb52c0544cf156c8af39205db8f2a6e46c9c72259bf3`.
- Evidence inventory: `b3cfd6de0444435358d86df951e707910cd7df45402d9a66aaa052124396ed00`.

Baseline, checked working sources and final committed bytes are distinguished.
After the commit, source/evidence/report bytes are checked against those
inventories; .codex-work/gentzen-w1-exchange/ retains committed-source.json,
delivery.json and remote-final.json receipts. The commit is not inserted
into its own report hash. Differing Downloads filenames are preserved by
dated/commit suffix; every delivered report is compared with the committed bytes.

README now describes the actual constructed presentation/reductions, the
current Gentzen transformation stage and separate coherence obligations.
Its obsolete 645 count is replaced by a maintained validation link; current
review links point to the exchange reviews. README/WSL2 setup use Git over
SSH. Historical reviews and manuscript v4 are preserved.

The hostile and mathematical-writing reviews are author-side, not independent
certification. The verified cached Knuth–Larrabee–Roberts source was directly
consulted. No independent kernel replay, Challenge/Solution comparison,
Comparator, official preflight/service verification, manuscript recompilation/
layout review, publication, license or visibility change ran. The reviews are
[hostile](reviews/GENTZEN_W1_EXCHANGE_HOSTILE.md) and
[writing](reviews/GENTZEN_W1_EXCHANGE_WRITING.md).

## Next concrete unproved W1 case

The next concrete unproved W1 instance is left contraction commuting with
right contraction (p.251, γ = wR). Let C,D : NormalForm P,
gs,hs : List (List (NormalForm P)), Θ,Λ : List (NormalForm P),
hn : 2 ≤ gs.length and hm : 2 ≤ hs.length, with:

```lean
f : G P (repeated C gs ++ Θ) (repeated D hs ++ Λ)
```

Compare the existing-constructor terms:

```lean
G.contractL C gs Θ (gaps hs ++ D :: Λ) hn
  (G.contractR (repeated C gs ++ Θ) D hs Λ hm f)
G.contractR (gaps gs ++ C :: Θ) D hs Λ hm
  (G.contractL C gs Θ (repeated D hs ++ Λ) hn f)
```

Both have type `G P (gaps gs ++ C :: Θ) (gaps hs ++ D :: Λ)`.
Prove Reduced denotation equality, proof-property preservation, exact
opposite-side predecessor/rank equations and the left selected-copy rank
loss; then check the corresponding right-side local comparison. Opposite-side
contraction has a singleton predecessor, although its own selected side
branches. Do not deduce this from denotation equality.

Other W1 cases, W2–W6, blocked-contraction transformations, replacement at
arbitrary ProofAddress, all-site rank decrease, Reducibility, Blocked-w,
the remainder of G2 and cut elimination remain open. Restricted positive
coherence inputs, PositiveCoherence, Reduced.Faithful, Boolean Coherence and
unconditional maximality remain separate/open. Existing conditional transfers
are unchanged. An unfinished Lean proof of a cited theorem does not establish
a defect in the manuscript.
