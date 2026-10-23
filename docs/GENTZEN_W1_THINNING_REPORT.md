# W1 opposite-side thinning commutations

## Proved endpoints and exact hypotheses

For arbitrary `P : Type u`, `C D : NormalForm P`,
`gs : List (List (NormalForm P))` and `hn : 2 ≤ gs.length`, the two derived
local commutations below compile in `DosenPetric.Reduced.Gentzen.W1`.
The constants and both literal signs are permitted. There is no inhabitant,
decidable equality, enumeration, freshness, atomicity, CutFree, Atomized,
coherence or faithfulness premise in either denotation or rank theorem.
Equality of arrows means equality in the existing syntactic Reduced.Hom.
Composition executes its first argument first; `a ; b` denotes `comp a b`.

For `Θ Δ Λ : List (NormalForm P)` and
`f : G P (repeated C gs ++ Θ) (Δ ++ Λ)`, define:

```lean
oldL := G.contractL C gs Θ (Δ ++ D :: Λ) hn
  (G.thinR (repeated C gs ++ Θ) Δ Λ D f)
innerL := G.contractL C gs Θ (Δ ++ Λ) hn f
newL := G.thinR (gaps gs ++ C :: Θ) Δ Λ D innerL
```

The two outer proofs have exactly type
`G P (gaps gs ++ C :: Θ) (Δ ++ D :: Λ)`.
`W1.denoteL` proves `ofTerm newL.denote = ofTerm oldL.denote`.

For `Γ Θ Λ : List (NormalForm P)` and
`f : G P (Γ ++ Θ) (repeated C gs ++ Λ)`, define:

```lean
oldR := G.contractR (Γ ++ D :: Θ) C gs Λ hn
  (G.thinL Γ Θ (repeated C gs ++ Λ) D f)
innerR := G.contractR (Γ ++ Θ) C gs Λ hn f
newR := G.thinL Γ Θ (gaps gs ++ C :: Λ) D innerR
```

The two outer proofs have exactly type
`G P (Γ ++ D :: Θ) (gaps gs ++ C :: Λ)`.
`W1.denoteR` proves `ofTerm newR.denote = ofTerm oldR.denote`.
These definitions combine existing constructors; no constructor is added.

## Baseline and preserved interfaces

Clean main started at `f575b6f41da9a8abf0560a3109d22e7f0e55ada4`.
Git status was inspected and SSH origin fetched; there was no newer commit
or unrelated working change. Actual baseline strict verification passed:
105 Lean source files / 4,739 audited declarations, 12.481 seconds, exit 0.
G0/G1, Atomic-k, tracing, clusters, contraction sums and all earlier
presentation/reduction/zero/union constructions were reused.

Four modules are added, with root imports and 34 selected axiom prints.
Every pre-existing DosenPetric module is byte-identical to baseline, including
the 21 reduced constructor schemas, 61 reduced equation schemas, 19 Positive
schemas, 16 G schemas, AtomicFormula, Atomized, CutFree, Topmost, predecessor
and rank definitions. Lean 4.35.0, Init-only dependency closure, manifest,
build/audit scripts, AGENTS, historical reports and manuscript v4 are unchanged.
The complete preserved-byte list is in boundaries.json.

## Source correspondence

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12, one-based. Printed pp.249–253, 272–273 and
291–292 were consulted; p.251 was also inspected in rendering. The verified
cache and access artifacts are recorded in source-consultation.json.
Historical source-access records are unchanged; no new discrepancy was confirmed.

| Source location | Typed correspondence and exact scope | Lean declarations / proof input |
| --- | --- | --- |
| §11.2 p.251 (W 1), γ = kR | Left contraction after right thinning equals right thinning after left contraction, on the unchanged antecedent copy positions. | `W1.oldL/innerL/newL`, `denoteL`; actual pre/postcomposition and `Reduced.Laws.assoc`. No Semilattice Coherence input. |
| §11.2 p.252, right analogue of Reducibility, applied to p.251 W1 | Right contraction after left thinning equals left thinning after right contraction. | `oldR/innerR/newR`, `denoteR`; separate checked associativity proof, no arrow-negation operation. |
| §11.2 pp.248–249, parametric clusters and rank; pp.251–252, rank condition | Opposite-side thinning has exactly one predecessor at the same At position. Contraction sums every selected upper copy. | `G.predecessors_thinR_left/thinL_right`, `rho_thinR_left/thinL_right`; existing `contractionRankL_eq/R_eq` and `selectedCopies_length`; `contraction_lossL/R`, `endpoint_lossL/R`. |
| §11.5 pp.272–273, constant basis and retained thinnings | Constants remain legitimate selected whole formulas. Left bot and right top thinning are retained operations, not replaced by special constant proofs. | Generic commutations allow all C,D; `emptyP_constantsL/R` at Empty. No literal-occurrence inhabitant is needed. |
| §12.5 pp.291–292, atomic zero basis and extension | Premise f is arbitrary and may contain atomic zero or cuts. These two calculations need no zero-specific rewrite or new zero. | Generic denotation/rank results depend only on constructors and categorical associativity/predecessor laws. Atomic-zero leaf and all existing zero laws are unchanged. |

These are derived local instances. They are not new defining equations,
the full W1 family, or a proof of the source's coherence appeal.

## Typed categorical calculations

The left calculation uses these actual raw arrows:

```text
ante (gaps gs ++ C :: Θ)
  -- (copies C gs Θ).product --> ante (repeated C gs ++ Θ)
  -- f.denote                --> succ (Δ ++ Λ)
  -- (Route.thin Δ Λ D).coproduct --> succ (Δ ++ D :: Λ).
```

Writing their quotient arrows as a,f,b, newL denotes `(a ; f) ; b` and oldL
`a ; (f ; b)`. `ofTerm_comp` followed by Laws.assoc proves their equality.
The right calculation is independently checked:

```text
ante (Γ ++ D :: Θ)
  -- (Route.thin Γ Θ D).product --> ante (Γ ++ Θ)
  -- f.denote                  --> succ (repeated C gs ++ Λ)
  -- (copies C gs Λ).coproduct  --> succ (gaps gs ++ C :: Λ).
```

Here newR denotes `a ; (f ; b)` and oldR `(a ; f) ; b`; use associativity in
the reverse direction. Neither calculation needs naturality, a mixed map,
a coherence theorem, arrow negation, or equality reflection after inclusion.

## Exact rank equations

Let n = gs.length. The reusable `G.rho_thinR_left` and `rho_thinL_right`
theorems assert, for every actual opposite-side At position x:

```text
rho (thinR f) left x  = 1 + rho f left x
rho (thinL f) right x = 1 + rho f right x.
```

Their predecessor lists are proved singletons containing the same x in the
unique premise. They follow from the existing parent/fiber construction and
rho_eq, independently of denotation equality. `G.sum_map_one_add` sums one
extra node per list entry, without deduplication.

In the left case, set `x = At.shift (gaps gs) (At.here C Θ)` and:

```lean
Rnew := G.contractionRankL C gs Θ (Δ ++ Λ) hn f
Rold := G.contractionRankL C gs Θ (Δ ++ D :: Λ) hn
  (G.thinR (repeated C gs ++ Θ) Δ Λ D f)
```

The checked theorems prove:

```text
contraction_lossL:      Rold = Rnew + n
endpoint_rankL:         newL.rho left x = Rnew + 1
contraction_decreasesL: Rnew < Rold
endpoint_lossL:         oldL.rho left x + 1 = newL.rho left x + n
endpoint_decreasesL:    newL.rho left x < oldL.rho left x.
```

The old endpoint rank is Rold by the existing contractionRankL definition.
For the right case use `x = At.shift (gaps gs) (At.here C Λ)`, right sequent
side, and contractionRankR with antecedents `Γ ++ Θ` / `Γ ++ D :: Θ`.
The declarations with suffix R prove exactly the same five equations and
inequalities. Every selected upper copy contributes through the complete
selectedCopies list and its length theorem. Fixed equal formulas in gaps
are not silently included as selected copies.

The contraction subterm loses n nodes. The whole proof's selected endpoint
loses n−1 nodes, stated without subtraction by endpoint_lossL/R. Strictness
uses hn, since n ≥ 2. No rank is defined or inferred from a quotient arrow.
These equations concern cluster rho, not cut rank, cutCount, proofSize or a
future cut-elimination measure. They do not prove all-site decrease under
replacement inside an arbitrary proof context.

## Proof predicates, occurrences and checked boundaries

`cutCountL/R`, `cutFreeL/R`, `atomizedL/R` prove, for each concrete pair:

```text
new.cutCount = old.cutCount
new.CutFree ↔ old.CutFree
new.Atomized ↔ old.Atomized.
```

The count and predicate comparisons reduce directly to the definitions.
Both atomization predicates mean `AtomicFormula D ∧ f.Atomized` for arbitrary
D. `newL_atomized/newR_atomized` require that explicit atomicity hypothesis
when starting only from f.Atomized. It is absent from the equality/rank laws.
These local unary rewrites do not duplicate f; count preservation is not
asserted for Atomic-k or any future branching transformation.

`relationL/R` apply the already well-defined occurrenceMap to the proved
Reduced denotation equality. They give equality of the entire tagged
relations at unchanged endpoints, including empty occurrence types; the
argument never runs from interpretation equality to arrow equality.
Whole-formula cluster positions, including constants, are distinct from
literal-occurrence tags.

| Boundary / exact checked construction | Declaration / coverage |
| --- | --- |
| Two selected copies, empty gaps, C = D, constants and empty P | constantPremiseL/R and emptyP_constantsL/R are actual G Empty proofs, with denotation equality, strict endpoint decrease and Atomized. Top is used on the left/right-thinning case and bot in its dual. |
| Three selected copies with another equal formula in an intervening nonempty gap | three_copy_lossL/R prove contraction loss 3 for gs = [[],[C],[]]; three_copy_endpoint_lossL/R prove whole endpoint loss 2 at the explicitly identified second position. |
| Empty thinning prefix or suffix and arbitrary remaining blocks | General positional theorems allow all lists; constant and cut examples instantiate empty prefixes on the left case / empty suffixes on the right. Three-copy statements retain arbitrary Δ,Λ or Γ,Θ. |
| Both literal signs and a premise actually containing cut | cutPremiseL/R, with_cutL/R prove denotation equality, rank decrease and cutCount 1; both_signs_with_cut instantiates positive and negative literals. No CutFree premise is assumed. |
| Arbitrary compound D and repeated labels | All general theorems quantify arbitrary NormalForm P and never compare formula values; atomized equivalence retains AtomicFormula D on both sides. |

This is two opposite-side W1 thinning instances only. All sixteen G schemas
are preserved rather than replaced or claimed newly normalized here.

## Verification and evidence

| Command | Exit | Elapsed seconds | Evidence log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 8.091 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 9.132 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 1.449 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.011 | `manuscript.log` |
| `git diff --check` | 0 | 0.007 | `diff-check.log` |

Final verification completed at 2026-10-23T05:57:03.913031+00:00: **109 Lean source
files / 4,794 audited project declarations**. The four new modules
contain 46 explicit source declarations; this differs from the generated/environment
audit count. One heavy build/audit ran at a time, including exploratory builds.

All five expected negative controls were rejected with Lean exit 1 and the
expected diagnostic: public custom axiom, unused private custom axiom,
hidden external axiom dependency, reflexive identification of distinct
tagged projections, and zero construction without a correctly typed witness.
The two control report JSON files and exact fixtures/logs retain their
commands, source hashes, diagnostics and outcomes. Public import closure passed.

The initial strict build passed, but its following import-closure check
failed because the existing parser ignores digits in module names. Only the
new module filenames were renamed from W1Thinning to ThinningCommutation;
the audit scripts and theorem namespaces are unchanged. Those first logs
are retained in pre-module-renaming; all required checks were then rerun.
Earlier exploratory errors concerned a doc-comment placement, an At/Place
rewrite, numeral bounds and explicit positional transport. Retained example
attempts and the exploratory note distinguish measured logs from earlier
tool-result-only observations. No failed run is represented as a pass.

Only propext, Quot.sound and Classical.choice are permitted. denoteL/R and
relationL/R print propext and Quot.sound; rank results also print
Classical.choice through established fiber infrastructure. cutCount,
CutFree and Atomized comparisons print no axioms. No choice-free claim is made.
No proof hole, custom mathematical axiom, native_decide, new equation or
assumed coherence instance enters production code. Deliberately invalid
negative-control fixtures remain outside production imports.

Evidence is retained under `provenance/wsl-gentzen-w1-thinning/`:
summary.json and verify.json record commands/exits/times; DECLARATIONS.txt
lists every new declaration with source line; SELECTED_AXIOMS.txt records
34 exact prints; SOURCE_SHA256SUMS inventories the checked Lean sources,
toolchain/dependency files and scripts; EVIDENCE_SHA256SUMS hashes all retained
supporting material; REPORT_SHA256SUMS and RECORD_SHA256SUMS separately hash
final reports and current maps. Key hashes:

- Final strict log: `3766f25ac9689f93b51c3be55a1aaad8b846b184d0cb188996abdcc481c4e5f1`.
- Checked source inventory: `2d3952a7f25f368b43e6dbc071cd9215fffec72627be45b6ff20e1926e67e50e`.
- Evidence inventory: `f4b60d3c4cd086243fe2310d45e5058f45f0d1f5f69743317f920f20f85fe7fd`.

Baseline and checked working sources are distinct records. After committing,
committed source/report/evidence bytes are compared with these inventories.
Commit/ref agreement and Downloads delivery are recorded separately in
`.codex-work/gentzen-w1-thinning/committed-source.json`, delivery.json and
remote-final.json. This avoids circular hashes containing their own commit.
Differing Downloads files are preserved with dated/commit-suffixed names.

Both author-side reviews apply to these actual proofs and correspondence;
they are not independent certification. No independent kernel replay,
Challenge/Solution comparison, Comparator, official preflight/service
verification, manuscript recompilation/layout review, publication or visibility
change ran. Manuscript v4 is byte-preserved. See the retained
[hostile review](reviews/GENTZEN_W1_THINNING_HOSTILE.md) and
[writing review](reviews/GENTZEN_W1_THINNING_WRITING.md).

## Next concrete obligation

The next concrete W1 instance is left contraction commuting with right
exchange (source p.251, γ = cR), together with its left/right dual. For:

```lean
C : NormalForm P
gs : List (List (NormalForm P))
Θ Δ X Y Λ : List (NormalForm P)
hn : 2 ≤ gs.length
f : G P (repeated C gs ++ Θ) (Δ ++ X ++ Y ++ Λ)
```

compare:

```lean
G.contractL C gs Θ (Δ ++ Y ++ X ++ Λ) hn
  (G.exchangeR (repeated C gs ++ Θ) Δ X Y Λ f)
G.exchangeR (gaps gs ++ C :: Θ) Δ X Y Λ
  (G.contractL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f)
```

Both have type `G P (gaps gs ++ C :: Θ) (Δ ++ Y ++ X ++ Λ)`.
Prove reduced denotation equality, exact selected-copy rank equations and
proof-property preservation. The opposite-side exchange predecessor should
be a singleton at the same At position; derive it from Premise.parent and
the fiber API rather than assume rank invariance under denotation.

Other W1 cases, W2–W6, blocked-contraction transformations, proof replacement
at arbitrary ProofAddress, all-site rank decrease, Reducibility, Blocked-w,
the remainder of G2 and cut elimination remain open. The restricted positive
coherence inputs, PositiveCoherence, Reduced.Faithful, Boolean Coherence and
unconditional maximality remain separate/open. Conditional transfers are
reused unchanged. Missing Lean formalizations of cited results do not by
themselves establish manuscript defects.
