# W1 opposite-side unary logical commutations

## Proved endpoints and hypotheses

For arbitrary `P : Type u`, `A B C : NormalForm P`,
`gs : List (List (NormalForm P))`, `hn : 2 ≤ gs.length` and arbitrary contexts
and premises, two derived commutations compile in
`DosenPetric.Reduced.Gentzen.W1.Logical`. Composition `a ; b := comp a b`
executes a first. Equality is in the existing syntactic Reduced.Hom quotient.
There is no inhabitant, decidable equality, enumeration, freshness, atomicity,
CutFree, Atomized, coherence, equality-reflection or arrow-negation premise.

For `Θ Δ Λ : List (NormalForm P)` and:

```lean
f : G P (repeated C gs ++ Θ) (Δ ++ A :: B :: Λ)
```

define the actual existing-constructor terms:

```lean
oldL := G.contractL C gs Θ (Δ ++ .disj A B :: Λ) hn
  (G.disjR (repeated C gs ++ Θ) Δ Λ A B f)
innerL := G.contractL C gs Θ (Δ ++ A :: B :: Λ) hn f
newL := G.disjR (gaps gs ++ C :: Θ) Δ Λ A B innerL
```

Both outer terms have exactly type
`G P (gaps gs ++ C :: Θ) (Δ ++ .disj A B :: Λ)`.
`denoteL` proves `ofTerm newL.denote = ofTerm oldL.denote`.

For `Γ Θ Λ : List (NormalForm P)` and:

```lean
f : G P (Γ ++ A :: B :: Θ) (repeated C gs ++ Λ)
```

define:

```lean
oldR := G.contractR (Γ ++ .conj A B :: Θ) C gs Λ hn
  (G.conjL Γ Θ (repeated C gs ++ Λ) A B f)
innerR := G.contractR (Γ ++ A :: B :: Θ) C gs Λ hn f
newR := G.conjL Γ Θ (gaps gs ++ C :: Λ) A B innerR
```

Both outer terms have exactly type
`G P (Γ ++ .conj A B :: Θ) (gaps gs ++ C :: Λ)`.
`denoteR` proves `ofTerm newR.denote = ofTerm oldR.denote`.
These constructors are unary disjR/conjL. Binary disjL/conjR are not being
commuted or identified with them. Both signs, constants, empty contexts,
repeated equal formulas and premises containing cuts are allowed.

## Baseline and preserved construction

Clean main at `eb870eeae8a6130d39fe27d235b9316ca95ac563` agreed with fetched
SSH origin. Actual baseline strict verification passed: 117 Lean files /
4,906 audited declarations, exit 0; baseline.json retains measured time.
No intervening commit or unrelated working change was discarded. All earlier
presentation, normalization, reduction, atomic/contextual factorizations,
zero/union, G0/G1, Atomic-k, clusters/rank and opposite-side W1 thinning,
exchange and contraction results are reused unchanged.

Four letters-only modules are added: GentzenOppositeLogicalRank,
GentzenLogicalCommutation, GentzenLogicalCommutationRank and
GentzenLogicalCommutationExamples, with root imports and 45 selected axiom
prints. All older DosenPetric modules are byte-identical, including the
21 reduced constructor/61 equation/19 Positive/16 G schemas, proof predicates,
predecessors and existing ranks. Lean 4.35.0, Init-only dependencies/manifest,
audit scripts, AGENTS, manuscript v4 and historical reports/access records
are unchanged. Boundaries.json inventories these preserved bytes.

## Source correspondence

The consulted source is Došen–Petrić, *Proof-Theoretical Coherence*, September
2007, [pinned PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n is PDF page n+12, one-based. Printed pp.248–253 were consulted,
p.251 also in rendering. Constant/zero extensions on pp.272–273 and 291–292
were checked against the retained syntax. Source-consultation.json records
verified caches and access artifacts; historical access records remain intact.
No new source discrepancy was confirmed.

| Source location | Exact local use / types | Lean correspondence and actual proof input |
| --- | --- | --- |
| §11.2 p.251, (W 1), γ = ∨R | Left contraction commutes with unary right disjunction introduction at the specified gap. Both have source gaps gs ++ C::Θ and target Δ ++ (A∨B)::Λ. | `W1.Logical.oldL/innerL/newL`, `denoteL`; actual G.denote uses copies.product then f then Rules.disjRight.toTerm. Reduced associativity only. |
| §11.2 p.252, right analogue | Right contraction commutes with unary left conjunction introduction. Both have source Γ ++ (A∧B)::Θ and target gaps gs ++ C::Λ. | `oldR/innerR/newR`, `denoteR`; Rules.conjLeft.toTerm precedes f and copies.coproduct follows; reverse associativity. |
| §11.2 p.248, parametric clusters | Every unchanged-side position has one predecessor at the exact same typed At. | `G.predecessors_disjR_left/conjL_right`, `rho_disjR_left/conjL_right` from actual parent/fiber definitions. |
| §11.2 pp.247–249, logical leaf / all-node rank | Introduced whole formula is a leaf; tracing stops, without descending into premise A/B. An outer opposite-side contraction adds one node. | Principal Leaf proofs from sourceArity/index; sourceArity_correct proves empty predecessor lists; rho_leaf proves rank 1; `oldL/oldR_principal_rank` prove 2 and `newL/newR_principal_rank` prove 1. |
| §11.2 pp.249, 251–252, contraction rank and directed requirement | Sum every selected upper copy; each crosses one unary logical proof node. | Existing contractionRankL_eq/R_eq, selectedCopies_length and sum_map_one_add give exact contraction loss n and whole selected-endpoint loss n−1. |
| §11.5 pp.272–273; §12.5 pp.291–292 | Constants remain whole formulas even when literal-occurrence types are empty; atomic zero leaves remain admitted. | Actual G Empty constant examples; arbitrary premises, including cuts/zero, in generic proofs. No new zero or coherence law is needed. |

The source's Semilattice Coherence appeal is not assumed. These are two
opposite-side unary logical instances only. Binary disjL/conjR, same-side
parametric W1 cases and all-site reducibility remain separate. The existing
syntactic quotient and non-strict binary context folds are unchanged.

## Typed categorical calculations

The left denotation follows:

```text
ante (gaps gs ++ C :: Θ)
  -- (copies C gs Θ).product --> ante (repeated C gs ++ Θ)
  -- f.denote --> succ (Δ ++ A :: B :: Λ)
  -- (Rules.disjRight Δ Λ A B).toTerm --> succ (Δ ++ .disj A B :: Λ).
```

NewL is `(a ; f) ; b` and oldL `a ; (f ; b)`. Expand G.denote and
ofTerm_comp and use Reduced.Laws.assoc. The independent right calculation is:

```text
ante (Γ ++ .conj A B :: Θ)
  -- (Rules.conjLeft Γ Θ A B).toTerm --> ante (Γ ++ A :: B :: Θ)
  -- f.denote --> succ (repeated C gs ++ Λ)
  -- (copies C gs Λ).coproduct --> succ (gaps gs ++ C :: Λ).
```

NewR is `a ; (f ; b)` and oldR `(a ; f) ; b`; use reverse associativity.
The source arrow is conjLeft.toTerm, not the inverse exchange arrow from
the preceding checkpoint. No coherence or relation/inclusion reflection is used.

## Opposite-side ranks and complete contraction sums

`G.predecessors_disjR_left` and `G.predecessors_conjL_right` quantify every
unchanged-side position of every formula. Unfolding the actual parent/fiber
definitions gives a complete singleton list at the identical typed At.
Applying rho_eq proves:

```text
rho(disjR f,left,x)  = 1 + rho(f,left,x)
rho(conjL f,right,x) = 1 + rho(f,right,x).
```

Let n = gs.length. For the left case define:

```lean
x := At.shift (gaps gs) (At.here C Θ)
Rnew := G.contractionRankL C gs Θ (Δ ++ A :: B :: Λ) hn f
Rold := G.contractionRankL C gs Θ (Δ ++ .disj A B :: Λ) hn
  (G.disjR (repeated C gs ++ Θ) Δ Λ A B f)
```

The right case uses `x := At.shift (gaps gs) (At.here C Λ)` on the succedent,
with contractionRankR at sources Γ++A::B::Θ and Γ++(A∧B)::Θ. In each case:

```text
contraction_lossL/R:      Rold = Rnew + n
endpoint_rankL/R:         rho(new,x) = Rnew + 1
endpoint_lossL/R:         rho(old,x) + 1 = rho(new,x) + n
contraction_decreasesL/R: Rnew < Rold
endpoint_decreasesL/R:    rho(new,x) < rho(old,x).
```

The old selected endpoint rank is Rold by the existing definition. Every
selectedCopies entry contributes one logical-rule node through the relevant
opposite-side equation. The existing contractionRankL_eq/R_eq sums,
sum_map_one_add and selectedCopies_length give n, without dropping adjacent
equal copies or including fixed equal formulas in gaps. Strictness uses n≥2.
The contraction subterm loses n nodes; the whole selected endpoint loses n−1.
These are local syntactic cluster-rank facts, not quotient invariance, a
cut-count/proof-size inequality, or all-site decrease after proof replacement.

## Introduced whole-formula principal positions

Define the exact positions:

```lean
zL := At.shift Δ (At.here (.disj A B) Λ)
zR := At.shift Γ (At.here (.conj A B) Θ)
```

The generic `disjR_principal_leaf` and `conjL_principal_leaf` prove Leaf
from sourceArity and the selected index equality. sourceArity_correct then
proves the complete principal predecessor list empty; rho_leaf gives rank 1.
These are not assumptions about the desired transformation. The pair-level
newL/newR principal predecessor theorems specialize those results, and:

```text
oldL_principal_rank: rho(oldL,right,zL) = 2
newL_principal_rank: rho(newL,right,zL) = 1
oldR_principal_rank: rho(oldR,left,zR) = 2
newR_principal_rank: rho(newR,left,zR) = 1.
```

The old root is an opposite-side contraction above a logical leaf, adding
one node via the already proved contraction rank helper. The new root is
the logical rule itself. Whole-formula tracing stops at the introduced A∨B
or A∧B; it does not trace that whole formula into premise A/B. Fixed equal
compounds elsewhere are different positions, identified by indices, not labels.
The separate literal-occurrence relation still has all internal Sum tags.
Neither this principal decrease nor the targeted contraction decrease is an
arbitrary-context/all-site reducibility theorem.

## Proof predicates, occurrences and checked boundaries

cutCountL/R, cutFreeL/R, atomizedL/R and relationL/R prove:

```text
new.cutCount = old.cutCount
new.CutFree ↔ old.CutFree
new.Atomized ↔ old.Atomized
new.relation = old.relation.
```

Both unary constructors retain f once. The count/predicate comparisons are
definitional and both atomization predicates equal f.Atomized. Introducing
a compound principal formula needs no AtomicFormula premise: Atomized
restricts thinning formulas only. newL_atomized/newR_atomized reuse hf directly.
Complete tagged-relation equality follows by congrArg occurrenceMap from
Reduced denotation equality, never in reverse. Endpoints are unchanged, so
all internal occurrence coordinates, repeated tags and empty occurrence types
remain in the statement. No arbitrary-endpoint zero is introduced.

| Checked boundary | Actual construction / result |
| --- | --- |
| Three selected copies and fixed equal contraction gap | contextPremiseL/R use gs=[[],[lit l],[]], selecting three of four equal formulas. context_endpoint_lossL/R prove whole targeted loss exactly 2 at the explicit selected position. The established selected/fixed-copy API is reused. |
| Nonempty logical prefix and tail, fixed equal compound | contextPremiseL/R introduce a fixed A∨B/A∧B logically in the prefix, then the outer unary rule introduces an equal compound at the next position. context_checkedL/R check denotation, cutCount 1, Atomized and principal 2→1. fixed_compound_distinct proves those whole-formula positions distinct. |
| Compound principal with Atomized premise | The compound fixed/principal formulas are introduced logically, while all thinnings are literal. The checked contextNew proofs remain Atomized; no compound-thinning leaf or hidden atomicity assumption is used. |
| Empty logical prefixes/tails, two copies and P=Empty | constantPremiseL : G Empty [top,top] [top,top], constantPremiseR : G Empty [bot,bot] [bot,bot] are actual proofs. emptyP_top/bot check denotation and principal ranks 2→1. |
| Both signs, actual cut and internal tags | Context premises retain a G.cut of atomic identities; both_signs_with_cut instantiates positive/negative literals with cutCount 1. internal_literal_tags_distinct proves Sum.inl x ≠ Sum.inr y for actual typed literal-occurrence positions. |

## Verification and evidence

| Command | Exit | Elapsed seconds | Evidence log |
| --- | --- | --- | --- |
| `bash scripts/verify.sh` | 0 | 3.051 | `strict.log` |
| `python3 scripts/check-audit-boundaries.py` | 0 | 6.342 | `audit-boundaries.log` |
| `python3 scripts/check-presentation-boundaries.py` | 0 | 0.945 | `presentation-boundaries.log` |
| `(cd manuscript && sha256sum -c SHA256SUMS)` | 0 | 0.010 | `manuscript.log` |
| `git diff --check` | 0 | 0.008 | `diff-check.log` |

Final verification completed at 2026-10-23T13:20:48.841975+00:00: **121 Lean files /
4,973 audited project declarations**. Four new modules contain
61 explicit source declarations, a different count from generated/environment
declarations. All heavy builds/audits, including exploratory checks, were
sequential; final verification followed the last proof changes.

All five expected controls rejected with Lean exit 1 and expected diagnostics:
public custom axiom, unused private custom axiom, hidden external axiom
dependency, reflexive identification of distinct tagged projections, and
zero construction without a correctly typed existing-arrow witness. Exact
fixtures, source/log hashes, commands and outcomes are retained in the two
control directories. Public import closure passed; audit scripts are unchanged.

Failed attempts are retained with exact logs/exits/times. Principal Leaf
proofs first exposed an At/Place implicit-transparency simplification mismatch;
explicit index equality fixed it. A deprecated conditional lemma then rejected
two attempts and was replaced by ite_eq_left. A later example failed because
arbitrary signed literal occurrence types were specialized to Unit before
reducing the sign. The final tag-disjointness theorem quantifies actual
occurrence positions. These were elaboration/API/example issues; no theorem
was admitted or weakened, and no failed build is reported as passing.

Permitted axioms remain propext, Quot.sound and Classical.choice. All 45
selected dependency prints, including wrapped lines, are retained verbatim.
Denotation/relation equalities use propext and Quot.sound; rank infrastructure
may also use Classical.choice. No choice-free claim is made. Production
contains no proof holes, custom mathematical axioms, native_decide, new
generating equations or coherence assumptions. Intentionally invalid controls
remain outside production imports.

Evidence directory: `provenance/wsl-gentzen-w1-logical/`. summary.json,
baseline.json, verify.json and core/explore records preserve commands, exits,
timings and hashes. DECLARATIONS.txt inventories all new statements;
SELECTED_AXIOMS.txt retains exact dependencies; SOURCE_SHA256SUMS inventories
checked Lean/toolchain/dependency/script bytes; EVIDENCE_SHA256SUMS hashes all
supporting material. Separate report/record manifests hash finalized reports
and current maps/README. Key hashes:

- Strict log: `cf66024ed96773c1120623717a442a224d4d2db5632d16c46878b8ae02645800`.
- Checked source inventory: `9532be3c76703890c213b609507e7d3b61eaaf93c0ebe589667851065e3d986e`.
- Evidence inventory: `b8e23803f8efb95c1a51b996124bd6c4620869e5e6d8bdf97fd0bb3f56c42f31`.

Baseline, checked working source and committed bytes are distinct records.
After committing, source/evidence/reports are compared against the checked
inventories. Runtime committed-source.json, delivery.json and remote-final.json
in .codex-work/gentzen-w1-logical/ record post-commit/ref/Downloads checks,
avoiding circular commit hashes. Differing Downloads files are preserved
with dated/commit suffixes; copies are compared with the committed reports.

Both reviews are author-side and apply to actual code/statements/correspondence,
not independent certification. The verified Knuth–Larrabee–Roberts cache was
consulted directly. Historical reports/access records and manuscript v4 are
preserved; no review/process prose entered its text or LaTeX comments.
Independent kernel replay, exhaustive independent source audit,
Challenge/Solution/Comparator, official preflight/service verification,
manuscript recompilation/layout review, publication, license and visibility
changes have not run. See [hostile review](reviews/GENTZEN_W1_LOGICAL_HOSTILE.md)
and [writing review](reviews/GENTZEN_W1_LOGICAL_WRITING.md).

## Next concrete same-side parametric case

The next task is same-side thinning through contraction at a specified
fixed parametric gap, together with its dual (§11.2 p.251, γ=kL and dual kR).
Use positional list decomposition, not a search for a matching formula.
For arbitrary P : Type u, C,E : NormalForm P, pre,post : List (List (NormalForm P)),
U,V,Θ,Δ : List (NormalForm P), define:

```lean
gs  := pre ++ (U ++ V) :: post
gs' := pre ++ (U ++ E :: V) :: post
upBefore := repeated C pre ++ U
upAfter  := V ++ C :: (repeated C post ++ Θ)
loBefore := gaps pre ++ U
loAfter  := V ++ (gaps post ++ C :: Θ)
```

Require `2 ≤ gs.length` and derive `gs'.length = gs.length`. Prove the exact
list identifications, not definitional strictness:

```text
repeated C gs  ++ Θ = upBefore ++ upAfter
repeated C gs' ++ Θ = upBefore ++ E :: upAfter
gaps gs  ++ C :: Θ = loBefore ++ loAfter
gaps gs' ++ C :: Θ = loBefore ++ E :: loAfter.
```

For `f : G P (upBefore ++ upAfter) Δ`, compare contractL at gs' after
`G.thinL upBefore upAfter Δ E f` with
`G.thinL loBefore loAfter Δ E` after contractL at gs. Use G.reindex with
proved context equalities above; both final proofs must have exactly type
`G P (loBefore ++ E :: loAfter) Δ`.

Every contracted copy must remain parametric through the thinning. In the
thinning conclusion context, its new principal position is precisely
index upBefore.length. Derive from the decomposition:

```text
∀ x ∈ selectedCopies C gs' Θ, x.index ≠ upBefore.length.
```

Also prove the positional embedding of every original selected copy under
Route.thin, with none lost or duplicated. The inserted E belongs to the
fixed gap and is never a selected copy, even when E=C. No freshness or
formula disequality assumption is allowed. Prefixes, suffixes and fixed
gap halves may all be empty; the displayed arity bound is retained.

Include the terminal fixed-tail variant as well: write Θ0=U++V and
Θ1=U++E::V, keep gs unchanged, and use upBefore=repeated C gs++U,
upAfter=V, loBefore=gaps gs++C::U and loAfter=V. Derive the analogous
four context equalities and exclude upBefore.length from every
selectedCopies C gs Θ1 index. All selected copies lie before that new
principal position. This covers the fixed tail after the last selected copy,
including empty halves, without treating any equal fixed formula as selected.

For arbitrary Γ : List (NormalForm P), the dual uses
`f : G P Γ (upBefore ++ upAfter)`, thinR at upBefore/upAfter,
contractR at gs/gs' and final type `G P Γ (loBefore ++ E :: loAfter)`.
Prove the corresponding coproduct routing law and rank equations directly.
Both commutations require actual Reduced equations for the same-side routing
composites, beyond merely reassociating pre/postcomposition. Preserve complete
relations and proof predicates; Atomized equivalence retains AtomicFormula E
on both sides if E is arbitrary. Every selected copy must be parametric.

Same-side W1 exchanges/contractions/logical parametric cases, W2–W6, blocked
transformations, arbitrary proof-context replacement/all-site decrease,
Reducibility, Blocked-w and cut elimination remain open. Positive coherence
inputs, PositiveCoherence, Reduced.Faithful, Boolean Coherence and unconditional
maximality are separate/open. Existing conditional transfers remain unchanged;
a missing formalization of a cited theorem is not itself a manuscript defect.
