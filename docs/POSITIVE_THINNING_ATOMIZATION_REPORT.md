# Positive thinning atomization (Atomic-k)

## Proved endpoint and hypotheses

For every type `P : Type u`, lists `Γ Δ : List (NormalForm P)` and
`g : Reduced.Gentzen.G P Γ Δ`, `G.atomization` proves:

```lean
∃ h : G P Γ Δ,
  h.Atomized ∧ (g.CutFree → h.CutFree) ∧
  ofTerm h.denote = ofTerm g.denote
```

Equality is in the existing syntactic `Reduced.Hom (ante Γ) (succ Δ)`.
Here `ante Γ := Γ.foldr NormalForm.conj .top` and
`succ Δ := Δ.foldr NormalForm.disj .bot`. Composition executes its first
argument first; the notation `f ; g` below denotes `comp f g`.
No inhabitant, decidable equality, enumeration, freshness or coherence premise
is required. Both literal signs, arbitrary binary bracketing, repeated formulas,
constants, empty contexts and empty occurrence types remain permitted.

`G.atomization_cutFree` gives an atomized, cut-free representative whenever
`g.CutFree` holds. `G.atomization_occurrences` adds `h.relation = g.relation`
on the complete, unchanged tagged endpoint types. These theorems compile in
[PositiveThinningAtomization.lean](../DosenPetric/PositiveThinningAtomization.lean).

The witness is the structurally recursive `G.atomize g`. `G.atomize_atomized`,
`G.atomize_cutFree`, `G.atomize_denote` and `G.atomize_relation` are its checked
properties. Atomized constrains only thinning formulas: atomic cut formulas,
atomic contraction formulas and atomic endpoints are not required. This is
Atomic-k, one part of G2; it is not cut elimination or a decreasing-rank theorem.

## Baseline, scope and preserved interfaces

Clean main started at `f5626c562001665829a8b1d6cb11384018eceacb`.
SSH origin was fetched and agreed with main. Actual baseline verification
exited 0 with **70 Lean source files and 3,448 audited project declarations**.
The completed presentation, G0/G1, zero/union algebra, reduction and common
atomic factorization were reused. No unrelated work was present or discarded.

Nineteen modules were added, with root public imports and selected axiom
prints. Every pre-existing `DosenPetric/*.lean` file is byte-identical to the
baseline, including raw/Gentzen syntax, equations, Positive, AtomicFormula,
Atomized and CutFree. The 21 reduced constructors, 61 reduced equation schemas,
19 Positive schemas and 16 Gentzen schemas are unchanged. Lean 4.35.0,
Init-only production closure, Lake configuration/manifest, historical reports
and manuscript v4 are unchanged. `boundaries.json` records the byte comparisons.

## Source correspondence

The source is Došen–Petrić, *Proof-Theoretical Coherence*, September 2007,
[the pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
Its SHA-256 is
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is PDF page n+12 (one-based). Formulas on printed pp.247 and
271 were inspected in rendering; render hashes/locations are recorded in
`source-consultation.json`. The source PDF stays in the ignored reference cache.

| Source location | Source role and exact scope used | Lean construction / replacement for source proof appeals |
| --- | --- | --- |
| §11.1 p.234, mixed structural equations; p.240 mixed-map definitions | The actual e′∧ has type `(X∧Y)∧(A∨B) → (X∧A)∨(Y∧B)`. e′∨ has type `(A∨X)∧(B∨Y) → (A∧B)∨(X∨Y)`. | Existing `Rules.sourceConj X Y A B` and `Term.mixedDisj A X B Y`; `sourceConj_nat`, `mixedDisj_nat` derive naturality of these composites. |
| §11.1 pp.241–243, exchange and separated multiple contraction | Exchange specifies prefix, two blocks, tail; contraction selects copies by the intervening gaps. Empty gaps and repeated equal formulas are legal. | Existing constructors are unchanged. New exchange components, `copies_index` and `Rewire.duplicate` derive block contractions from them. |
| §11.2 pp.246–247, Atomic-k; first compound-k rewrite | Left conjunction thinning becomes two sequential thinnings followed by conjunction-left; the dual handles right disjunction. | `conjLeft_head`, `disjRight_head`, `conj_thin_head`, `disj_thin_head`, `headThinL/R_denote`. Association is a proved arrow comparison. |
| §11.2 p.247, disjunctive compound-k rewrite; use of contraction and (m e∧) | Branch over A and B, then contract both duplicated surrounding contexts. The source invokes earlier coherence in its calculation. | `sourceConj_fst`, `branchL_core`, `branchL_denote`; proved using existing structural equations, constant specializations and union idempotence. |
| §11.2 p.247, dual compound-k case; §11.5 pp.270–271, omitted mixed equations | Right conjunction thinning requires the mixed arrow actually used by `Rules.conjRight`, and contraction on both sides. | `mixedDisj_inr`, `branchR_core`, `branchR_denote`; actual mixedDisj, injection naturality and `diag_mix_codiag`. |
| §11.5 pp.272–273, Atomic-k with constants | Atomic formulas include top/bottom; thinning by bottom on the left and top on the right is retained. The two empty folds have different colours. | `headThinL/R` retain actual primitive thinning at lit/top/bot; no constant-based replacement proof or empty-sequent leaf. |
| §12.5 pp.291–292, zero extension | Atomic zero leaves are among the bases; later zero cut-elimination cases are separate. | `atomize (.zero l) = .zero l`; existing atomic zero bases remain unchanged. Later zero reduction cases remain open. |

Neither omitted `(m e)` schema was added to `Reduced.Equation`. The results
below are sufficient projected/injected consequences, **not a claim to prove
both complete omitted schemas**. No new source discrepancy was confirmed in
this checkpoint; earlier correspondence entries and access records are retained.

## Categorical calculations before proof transformation

`sourceConj_fst X Y A B` proves, for all four normal forms:

```text
sourceConj X Y A B ; (fst X A ∨ fst Y B)
  = fst (X∧Y) (A∨B) ; mix X Y.
```

Both sides have type `(X∧Y)∧(A∨B) → X∨Y`. The left path goes through
`(X∧A)∨(Y∧B)`; the right through `X∧Y`. Its proof expands the actual
source-defined composite only in small structural lemmas, uses the existing
d-k/d-m laws and naturality, proves the top specialization, and maps A/B to
top. The specialization uses the established zero-derived top-domain
uniqueness. It does not use an interpretation to reflect equality.

The required dual calculation is `mixedDisj_inr A B X Y`:

```text
(inr A X ∧ inr B Y) ; mixedDisj A X B Y
  = mix X Y ; inr (A∧B) (X∨Y).
```

Both sides have type `X∧Y → (A∧B)∨(X∨Y)`. The left intermediate object is
`(A∨X)∧(B∨Y)`. The proof establishes the bottom specialization, its typed
unit inverse, and naturality along `fromBot A` and `fromBot B`. Initiality
and existing zero-derived bottom-codomain uniqueness justify the specialization.
There is no cancellation without an inverse and no appeal to full-Presentation
uniqueness. Both calculations are inside Reduced.Hom.

For `f : Hom X Y`, the branching left calculation has the complete path:

```text
(A∨B)∧X → (A∨B)∧(X∧X) → (X∧X)∧(A∨B)
 → (X∧A)∨(X∧B) → X∨X → Y∨Y → Y.
```

The arrows are `id ∧ diag`, swap, sourceConj, the two first projections,
`f∨f`, and codiag. `branchL_core` proves that this equals `snd ; f`.
After `sourceConj_fst`, its remaining duplicated-f expression is `f ∪ f`,
which equals f by the already proved syntactic union idempotence.

The branching right path is:

```text
X → X∧X → (A∨Y)∧(B∨Y) → (A∧B)∨(Y∨Y) → (A∧B)∨Y.
```

Its arrows are diag, `(f;inr A Y) ∧ (f;inr B Y)`, actual mixedDisj, and
`id ∨ codiag`. `branchR_core` proves equality to `f ; inr (A∧B) Y`.
The proof uses `mixedDisj_inr` and the existing diagonal–mix–codiagonal law.
No same-connective medial or older `ReducedWitnesses.mixedConj` is substituted.

## Positional structural operations and formula recursion

`At Γ A` selects a whole-formula position. `At.index_injective`, `splitAppend`,
`swapBlocks`, `copies_index` and `exchangeBack_component` distinguish positions
without comparing formula labels. Literal occurrences inside formulas keep
their existing tags. Repeated equal formulas in fixed blocks remain distinct.

`side P .conj` is the reduced category; `side P .disj` is its opposite.
Products in these two categories give actual projection/injection component
laws and `side_ext`. This is the established finite product/coproduct universal
property, not relational faithfulness or a contravariant arrow-negation functor.

`Rewire P Γ Δ` is an auxiliary script of unary structural rules with only
identity, sequence, exchange, separated contraction and equality reindexing.
There is no raw-term/proof embedding, cut, thinning, logical leaf or arbitrary
arrow constructor. `left/right` expand the script into the unchanged G syntax.
Their denotation, Atomized and cut-count laws are proved by script induction.

`Rewire.duplicate Ξ Γ Θ` contracts the selected two copies of the block Γ,
one formula position at a time. Its empty case is identity with list transport.
For a nonempty block it recurses on the tail, exchanges the intervening block,
then uses a separated two-copy contraction at the selected head position.
`duplicate_index` proves the exact lookup, including fixed prefix and tail.
`dupContext_arrow` and `dupTail_arrow` identify these scripts with the actual
fold diagonal/codiagonal comparisons by component universal properties.
Append, exchange and reindex comparisons have proved laws; binary folds are
never treated as definitionally strict.

| Inserted formula / side | Derived proof over premise f | Denotation dependency |
| --- | --- | --- |
| Left A∧B | Insert B, insert A, then conjL. | conj_thin_head, actual conjLeft_head. |
| Left A∨B | disjL of the two recursively thinned copies of f; contract Γ below the principal formula and the entire Δ. | sourceConj_fst, branchL_core, branchL_denote; dupTail/dupContext comparisons. |
| Right A∨B | Insert B, insert A, then disjR. | disj_thin_head, actual disjRight_head. |
| Right A∧B | conjR of the two recursively thinned copies of f; contract the entire Γ and Δ below the principal formula. | mixedDisj_inr, branchR_core, branchR_denote; dupContext/dupTail comparisons. |
| Either side, lit l/top/bot | Retain the actual thinning constructor at that atomic formula. | thin_head and existing routing. |

`G.headThinL/R` recurse structurally on the inserted formula; their Atomized,
CutFree and denotation theorems cover all five NormalForm constructors.
`Rewire.moveHead` exchanges one selected formula to an arbitrary specified gap.
Its component law proves equality with the original routing. Consequently,
`G.atomThinL Γ Θ Δ A f` has type `G P (Γ ++ A :: Θ) Δ` for
`f : G P (Γ ++ Θ) Δ`, and its denotation equals that of actual `G.thinL`.
`G.atomThinR Γ Δ Λ A f` has the dual arbitrary-gap statement. Both helpers
preserve Atomized premises and any existing CutFree proof.

The replacements introduce no cuts. Branching duplicates premises, so neither
global cut-count equality nor monotonicity, nor a proof-size bound, is claimed.
Only the unary Rewire scripts have the separately proved exact count laws.

## Exhaustive global constructor coverage

`atomize` recurses on the actual original proof, transforming each premise
before the surrounding rule. All sixteen cases occur in the definition and
the Atomized, CutFree and denotation proofs:

| G schema | Transformation / equality proof |
| --- | --- |
| identity | Keep atomic identity; reflexivity. |
| zero | Keep atomic zero; reflexivity. |
| topI | Keep the constant basis term; reflexivity. |
| botE | Keep the other constant basis term; reflexivity. |
| exchangeL | Reconstruct exchange; precomposition congruence. |
| exchangeR | Reconstruct exchange; postcomposition congruence. |
| thinL | Transform premise, then atomThinL; positional denotation law and premise congruence. |
| thinR | Transform premise, then atomThinR; dual law and premise congruence. |
| contractL | Keep every selected gap/copy and contraction formula; precomposition congruence. |
| contractR | Keep every selected gap/copy and contraction formula; postcomposition congruence. |
| conjL | Reconstruct at the original gap; composition congruence. |
| disjR | Reconstruct at the original gap; composition congruence. |
| conjR | Transform both premises; Rules.conjRight_congr. |
| disjL | Transform both premises; Rules.disjLeft_congr. |
| mix | Transform both premises; Rules.mix_congr. |
| cut | Retain the cut over transformed premises; Rules.cut_congr. A CutFree input cannot have this root case. |

`GentzenAnalysisMacros` additionally proves Atomized/CutFree preservation for
reindexing, both exchanges, both separated contractions, contractRFirst and
thinLast. No generic Gentzenization helper is used to implement replacements.

## Occurrences and empty boundaries

`G.atomize_relation g` is obtained by applying the already well-defined
Reduced.occurrenceMap to `atomize_denote g`. It is equality of complete
relations on `(ante Γ).formula.Occ` and `(succ Δ).formula.Occ`, so all fixed
and principal occurrence tags remain. No endpoint coordinate identification is
needed because the contexts are unchanged. Syntactic equality is proved first;
relation equality is only its consequence. Empty branches require no chosen
variable or occurrence. The existing `G.no_empty` boundary remains unchanged:
there is no `G P [] []` and no new top-to-bottom arrow or unwitnessed zero.

## Verification and evidence

All required working-source checks completed at
`2026-10-23T04:06:29.175338+00:00`, one heavy process at a time:

| Actual command | Exit / outcome |
| --- | --- |
| Baseline `bash scripts/verify.sh` | 0; 70 sources / 3,448 declarations. |
| Final `bash scripts/verify.sh` | 0; **89 sources / 3,990 declarations**; strict build and transitive axiom audit. |
| `python3 scripts/check-audit-boundaries.py` | 0; all three expected rejections and public import closure passed. |
| `python3 scripts/check-presentation-boundaries.py` | 0; both expected rejections passed. |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0; unchanged v4 TeX/PDF hashes. |
| `git diff --check` | 0; repeated after documentation/staging. |

All five negative controls have actual Lean exit 1: public direct axiom,
unused private axiom, hidden external axiom dependency, identification of
tagged projections by rfl, and attempted zero without a correctly typed arrow
witness. The last two diagnostics are respectively rfl failure and type mismatch.
Fixture bytes, exact commands, expected diagnostics, statuses and hashes are
retained under `audit-controls/` and `presentation-controls/` in the evidence.
Their JSON records retain the scripts' original runtime fixture paths.

The first staged whitespace check exited 2 for one trailing space in the new
GentzenContextComponents module. The space was removed, all required checks
were rerun successfully, and the staged check then exited 0. The initial
passing build and this diagnostic are preserved under `pre-whitespace/`;
the final source/hash inventory records the corrected sources.

Permitted axioms are exactly `propext`, `Quot.sound`, `Classical.choice`.
The principal atomization/denotation/occurrence theorems use all three.
The two mixed-map consequences and branch core calculations print propext and
Quot.sound; `At.index_injective` and the block comparison denotation chain
also print Classical.choice. No claim of choice-free proofs is made.
No proof hole, custom mathematical axiom, native_decide, new generating
equation or coherence premise was introduced. The transitive audit includes
private project declarations. Selected prints are in `Checks/Axioms.lean`.

Retained evidence: `provenance/wsl-positive-thinning-atomization/` contains
baseline/environment/memory and final logs, command/result JSON, five fixtures,
`DECLARATIONS.txt` (177 explicit source declaration entries in the new modules),
source consultation and interface preservation records, and SHA-256 inventories.
The audit's 3,990 count includes compiler-generated project declarations;
177 source entries are not an alternative audited-declaration count.
Strict log SHA-256:
`b6c42e420e45018e5b245f55f9495ada50e1816eb860eef9c6019187c55b55f1`.
SOURCE_SHA256SUMS SHA-256: `474ca864f6b724750df88c54b8c6a660b9103ed529d7482219d34d69c42c37bc`.
EVIDENCE_SHA256SUMS SHA-256: `0dff38e020bd3cd5acc90f66cfaa4389c62d365634d0c394e000d00870ba22e9`.

The strict log prints baseline HEAD plus hashes of the actual dirty Lean
sources. All 89 current Lean source hashes were compared with that log before
writing the source inventory. Final committed-source checks compare the same
inventory to both Git objects and working files; they are not misreported as
another heavy build. Report/record manifests cover the finalized documents.
Post-commit, live SSH-ref and Downloads byte-comparison receipts are retained
under `.codex-work/positive-thinning-atomization/` and the final response gives
the integration SHA. Reports are retained here and copied to Downloads with
conflict-preserving names.

No independent kernel replay, independent source audit, Challenge/Solution
comparison, Comparator, official preflight/service verification, manuscript
recompilation/layout review, publication, license or visibility change ran.
Both linked reviews are author-side AI-assisted reviews, not independent
certification: [hostile review](reviews/POSITIVE_THINNING_ATOMIZATION_HOSTILE.md)
and [writing review](reviews/POSITIVE_THINNING_ATOMIZATION_WRITING.md).

## Remaining obligations and next concrete theorem

Atomic-k is complete. The rest of G2, G3 cut elimination, restricted
mix-dicartesian coherence, PositiveCoherence, Reduced.Faithful, Boolean Coherence
and unconditional maximality remain open. Object duality does not implement
contravariant arrow negation; inclusion reflection, full reduction quotient
descent and remaining substitution/congruence bridges remain separate.

The next construction is **typed predecessor/ancestor tracing of a selected
whole-formula position through the existing proof tree**. Its entry data are:

```lean
f : G P Γ (C :: Δ)
g : G P (C :: Θ) Λ
ht : G.Topmost f g  -- f.CutFree ∧ g.CutFree
hf : f.Atomized
hg : g.Atomized
-- selected positions: At.here C Δ and At.here C Θ
```

The first target is a recursively defined, typed predecessor family covering
all sixteen rules, carrying proof-node address and source/succedent side.
Contraction must return every selected upper copy at its explicit gaps;
exchange/reindex and logical principal positions must retain positional tags.
`At`, splitAppend/swapBlocks/copies_index and the new block laws are available.
A proposed `SidePos Γ Δ C := At Γ C ⊕ At Δ C` is documentation, not an
implemented production definition. Ancestor closure, finite clusters and rank
are still to be constructed, following §11.2 pp.247–249. Tied/blocked
contractions and Reducibility/Blocked-w then require separate denotation and
rank arguments (pp.249–253), with constant/zero cases from §§11.5 and 12.5.
The existing cutCount is not this rank or a proved decreasing measure.
The previously proved coherence transfers remain conditional on their
explicit unsupplied premises.
