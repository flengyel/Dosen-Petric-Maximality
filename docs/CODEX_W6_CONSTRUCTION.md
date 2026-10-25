# Logical W6: concrete construction for local Codex

Latest upstream integration (edb86cb): retain the author's division of work,
correction procedure and tagged-substitution requirements. The new W6 analysis
is an instruction at its historical source anchor. The two-premise terminal-
source left family and all native binary producers compile here; the general
one-premise terminal-source left displayed families/ranks in its §3 remain
open as separately specified source constructions. Native one-premise repairs
and source singleton blockedness exclusions do not discharge those exact
source-rank statements. See the current continuation. No manuscript defect or
completed full-paper proof is inferred.

## Task and evidence

Implement the six W6 families below and connect them to the unchanged
arbitrary-address Reducibility targets. Continue toward general Reducibility;
this document does not replace the full-paper contract or narrow its endpoint.

This construction analysis uses remote main
`a17ec1b0b44c9fe7f5061bb35c2edfd1ded9ef90`. Inspect current main and preserve
newer work before implementation. The rank equations and proposed helper
lemmas below are mathematical derivations and implementation targets, not new
checked Lean declarations. No production Lean source was changed for this
instruction update.

The [hostile audit](reviews/W6_CONSTRUCTION_HOSTILE.md) and
[mathematical-writing review](reviews/W6_CONSTRUCTION_WRITING.md) assess this
construction analysis and preserve its implementation boundary.

The author has assigned implementation and builds to local Codex. ChatGPT's
role is to prepare instructions, examine and referee Codex's work, investigate
mathematical and literature questions, check the manuscript, and assist with
arXiv and Palomar preparation. Leave source builds to local Codex, which retains
the existing verification, main-branch commit/push and delivery requirements.
Publication, visibility, licensing and submission authorization is unchanged.

Read the current `AGENTS.md`, `CODEX_FULL_MANUSCRIPT_FORMALIZATION.md`,
`CODEX_NEXT_SESSION.txt`, both specialized Reducibility instructions, and the
statement, coverage, correction and presentation maps. Preserve all settled
proof, notation and writing decisions in those documents.

The September 2007 book was consulted directly at §11.2, printed pp.248–253;
p.252 was also inspected in rendering. Its SHA-256 is
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed p.n is one-based PDF p.n+12. W6 on p.252 uses the three-copy blocked
pattern on p.250. The present calculations retain the repository's explicit
exchanges instead of importing the source's Semilattice Coherence appeal.

## 1. Existing interfaces and the missing equalities

All namespace names below are relative to `DosenPetric.Reduced.Gentzen`.
The following interfaces were read in the anchored source:

| File | Reuse |
|---|---|
| `GentzenContractionSelection.lean`, `GentzenChainedSelection.lean` | `ContractionSelection`, `keep`, `selected`, `arity`, `lower`, `erased`, `chain`, `chain_count`, `chain_selected` |
| `GentzenContractionAppend.lean`, `GentzenContractionPrepend.lean` | `ContractionBlock.extend`, its selected/retained coordinates, and `ContractionSelection.prependFixed` |
| `GentzenSelectionContraction.lean`, `GentzenSelectionRanks.lean` | Singleton endpoint transport, `performL/R`, their denotation/count/atomization/rank laws, and `overhead_bound` |
| `GentzenBlockedSource.lean`, `GentzenBlockedPatterns.lean` | Actual `disjLLast`, `left2/3`, `right2/3`, and all six selected-principal blocked constructors |
| `GentzenMixedThinning.lean`, `GentzenMixedInjections.lean` | `sourceConj_nat`, `mixedDisj_nat` for the actual mixed composites |
| `GentzenParallelRoutes.lean`, `GentzenMixedSelectionComponents.lean` | Parallel routes, universal component equations and the existing chained-selection factorization |
| `GentzenBinaryFibers.lean`, `GentzenSourceEntryFrames.lean` | Actual binary ancestry and the explicit source-macro exchange paths |
| `GentzenBlockedEntryFrames.lean`, `GentzenReducibilityBoundary.lean` | `ReducibleL/R.entry_unique`, `descendants_left/right` |
| `GentzenReducibilityMixed.lean` | Pattern for assembling arbitrary-address results after proving local equality, blockedness and rank nonincrease |

The two theorems in `GentzenLogicalSelectionComponents.lean` have different
variances from the equalities needed here: `parallel_conjRight` acts on
antecedent routes, while `parallel_disjLeft` acts on succedent routes. W6 needs
antecedent-context naturality for `disjLLast` and residual-succedent naturality
for `conjR`. Prove those equalities from the mixed-map naturality theorems and
structural component equations. Do not apply the existing theorems with
interchanged types.

Fix a universe u, a type P : Type u, a normal form C : NormalForm P,
and contexts F, K and H (lists of normal forms). Use the already constructed
singleton-aware operations. For a selection
`p : ContractionSelection C F K`, a useful additional helper, if not present
in newer source, is

```text
appendFixed p H : ContractionSelection C (F++H) (K++H).
```

Its three defining cases append H to the tail of `last` and recurse through
`fixed` and `more`. Prove that its block equals `p.block.extend H`, its arity
equals p.arity, its keep is `p.keep.before H`, and its selected list is
`p.selected.map (fun a => a.before H)`. Then `performL/R` handles the singleton
case without a new proof node. Alternatively use `p.block.extend H` directly
when p.arity≥2 and `singleton_endpoints` when p.arity=1.

For another selection `q : ContractionSelection C U L`, where U and L are
contexts, prove

```text
(p.chain q).erased = p.erased ++ q.erased.
```

This follows by induction on p, using preservation of `erased` by a fixed
prefix in the `last` case. This equation is a requested result, not a cited
existing declaration. Keep all list transports explicit.

## 2. Left W6 with selected copies in both premises

Let P : Type u be arbitrary, let A and B be normal forms over P, and put
C=disj A B. Let Γ, K, Θ, L, Δ and Λ be contexts. Take

```text
p : ContractionSelection C Γ K
q : ContractionSelection C Θ L
f : G P (Γ++[A]) Δ
g : G P (Θ++[B]) Λ.
```

Write n=p.arity and m=q.arity; both are positive. Define

```text
X = gaps p.gs     Y = p.tail
Z = gaps q.gs     T = q.tail
E = (p.erased ++ q.erased) ++ [C].
```

The existing `lower` and `erased_eq` equations give
`K=X++C::Y`, `L=Z++C::T`, `p.erased=X++Y`, and `q.erased=Z++T`.
These are list equalities with specified positional maps, including when
fixed positions also have formula C.

Set `s := (p.chain q).chain (ContractionSelection.last [])`. It selects all
p copies, all q copies and the fresh terminal C, in that order. Its arity is
n+m+1≥3. Prove that its lower context and `s.erased++[C]` both equal E; in
particular establish the endpoint equality required by the prior handoff.
The old proof, transported to E, is

```text
s.block.applyL (proved arity bound) (Δ++Λ)
  (BlockedSource.disjLLast f g) : G P E (Δ++Λ).
```

Construct `f̂ : G P (K++[A]) Δ` and `ĝ : G P (L++[B]) Λ` by contracting
only the p and q copies in their respective premises. For n≥2 use
`(p.block.extend [A]).applyL`; for n=1 use endpoint transport. Treat q in the
same way. The proposed `appendFixed` helper permits uniform `performL` calls.

Define an outer block d with

```text
d.C    = C
d.gs   = [X, Y++Z, T]
d.tail = []
d.upper : repeated C d.gs ++ [] = (K++L)++[C]
d.lower : gaps d.gs ++ [C] = E.
```

The new proof is

```text
d.applyL (proved three-copy bound) (Δ++Λ)
  (BlockedSource.disjLLast f̂ ĝ) : G P E (Δ++Λ).
```

After the displayed endpoint transports, its blockedness is certified by
`BlockedL.disjunctionBoth A B X Y Z T Δ Λ f̂ ĝ`.
Its selected positions are

1. p.keep inside K, followed by L and the fresh C;
2. q.keep inside L, preceded by K and followed by the fresh C;
3. the final fresh C.

Identify these positions as the entire selected list of d and identify its
keep with s.keep at E. Prove actual blockedness by the constructor and
reindex laws; equality of denotations is insufficient for this step.

### Categorical equality

Let `r_p=p.route : Route K Γ`, `r_q=q.route : Route L Θ`, and

```text
R = (r_p.parallel r_q).parallel (Route.identity [C])
  : Route ((K++L)++[C]) ((Γ++Θ)++[C]).
```

For a route r, write r× for `ofTerm r.product`; for a selection or block t,
write t× for its route's product arrow.
Thus R× has source `ante ((K++L)++[C])` and target
`ante ((Γ++Θ)++[C])`. First prove, with the actual casts,

```text
s× = comp d× R×.
```

Check every component: an original selected p or q copy maps to the final
retained C; the fresh C does too; every unselected position retains its own
tag. Use `Route.ext_get` or `side_ext .conj`, not occurrence faithfulness.

Next prove terminal-disjunction context naturality:

```text
comp R× (ofTerm (disjLLast f g).denote)
  = ofTerm (disjLLast f̂ ĝ).denote.
```

Expand `disjLLast` into its input exchanges, native disjL and output exchange.
Use the actual exchange component equations to transport the context routes,
then `sourceConj_nat r_p× r_q× (id A) (id B)` at the appropriate folded
objects, append comparison equations, and the proved denotations of f̂ and ĝ.
The premise routes are `r_p.parallel (identity [A])` and
`r_q.parallel (identity [B])`; identify them with the extended block routes.
Associativity and `ContractionBlock.denoteL` now give the required equality
of old and new proofs in Reduced.Hom. State each intermediate arrow type.

### Exact rank calculation

For a positive integer k define δ(k)=0 if k=1 and δ(k)=1 if k≥2. Set

```text
Sp = (p.selected.map (fun a => f.rho .left (a.before [A]))).sum
Sq = (q.selected.map (fun a => g.rho .left (a.before [B]))).sum.
```

Prove the following from `Premise.parent`/predecessor laws, before taking sums:

| Position in `disjLLast f g` | Rank |
|---|---|
| A parametric Γ position coming from f | Original rank in f + 3 |
| A parametric Θ position coming from g | Original rank in g + 3 |
| The fresh terminal C | 2 |

Each parametric path crosses its own input exchange, native disjL and the
output exchange. The fresh C has rank 1 at native disjL and crosses only
the output exchange. Count exchange nodes even for empty exchanged blocks.
Reindexing adds no proof node.

The resulting target equations at the common retained position x are

```text
oldL.rho .left x = Sp + Sq + 3*(n+m) + 3
newL.rho .left x = Sp + Sq + δ(n) + δ(m) + 9.
```

The second equation counts the two retained parametric ranks, each increased
by 3, the fresh rank 2, and the outer contraction node. Since
δ(k)≤k−1 for every positive k, newL's rank is at most oldL's rank.
Prove the inequality in Nat without truncating an unjustified subtraction.
For example, use δ(n)+1≤n and δ(m)+1≤m.

## 3. Left W6 with selected copies in only one premise

Keep C=disj A B and the same f/g types, but take a selection in just the
indicated premise. The other premise is entirely fixed; equal C labels there
do not become selected. There is no arity-zero `ContractionSelection`.

| Selected premise | Endpoint | New outer gaps; tail | Blocked constructor |
|---|---|---|---|
| f, with p and K=X++C::Y | `(p.erased++Θ)++[C]` | `[X,Y++Θ]`; `[]` | `disjunctionFirst A B X Y Θ Δ Λ f̂ g` |
| g, with q and L=Z++C::T | `(Γ++q.erased)++[C]` | `[Γ++Z,T]`; `[]` | `disjunctionSecond A B Γ Z T Δ Λ f ĝ` |

For the first old selection, chain p with the singleton terminal C preceded
by the fixed context Θ. For the second, prepend fixed Γ to q chained with
the terminal singleton; transport associativity of concatenation explicitly.
Only the selected premise is contracted. Prove the analogues of the route
factorization, macro naturality, selected-list and retained-position equations.

Let k≥1 be the selected premise's arity and S its full selected-rank sum in
the original premise, embedded before [A] or [B]. The target rank equations are

```text
oldL.rho .left x = S + 3*k + 3
newL.rho .left x = S + δ(k) + 6.
```

Again the new rank is at most the old rank. At k=1 the old proof already has
the corresponding blocked pattern. Likewise the two-premise n=m=1 old proof
is already blocked. Prove these actual shape identifications and exclude them
from reducible-input dispatch using hr's unblocked conjunct. The uniform
construction can still be defined at those arities.

## 4. Separately typed right W6

Here C=conj A B. Take

```text
p : ContractionSelection C Δ K
q : ContractionSelection C Λ L
f : G P Γ (A::Δ)
g : G P Θ (B::Λ).
```

Write X=gaps p.gs, Y=p.tail, Z=gaps q.gs, T=q.tail, n=p.arity, m=q.arity.
The logical proof is the native `G.conjR f g`, with target `C::(Δ++Λ)`.
Set `sR := ContractionSelection.more (p.chain q)`. This selects the fresh
head C and both parametric families, retaining the last q copy. Its lower
context is `E_R=p.erased++L` and its arity is n+m+1.

Contract the premise selections with
`(p.prependFixed [A]).performR Γ f` and
`(q.prependFixed [B]).performR Θ g`, obtaining
`f̂ : G P Γ (A::K)` and `ĝ : G P Θ (B::L)`.
The old proof applies sR.block to `G.conjR f g`. The new proof contracts
`G.conjR f̂ ĝ` with

```text
dR.C = C
dR.gs = [[], X, Y++Z]
dR.tail = T.
```

The new proof has type `G P (Γ++Θ) E_R`; after the explicit list transports,
its blockedness is certified by
`BlockedR.conjunctionBoth A B Γ Θ X Y Z T f̂ ĝ`.
The three selected positions are the fresh head, the
retained p copy and the retained q copy. Identify the last with sR.keep.

For a route r write r+ for `ofTerm r.coproduct`; for a selection or block t,
write t+ for its route's coproduct arrow. Put

```text
R_R = (Route.identity [C]).parallel (p.route.parallel q.route)
    : Route (C::(K++L)) (C::(Δ++Λ)).
```

If dR is the new three-copy block, prove the coproduct equation

```text
sR+ = comp R_R+ dR+.
```

Its source is `succ (C::(Δ++Λ))` and its target is `succ E_R`.
Prove the residual-succedent naturality equation

```text
comp (ofTerm (G.conjR f g).denote) R_R+
  = ofTerm (G.conjR f̂ ĝ).denote
```

using `mixedDisj_nat (id A) p.route+ (id B) q.route+`, the append
comparison laws and the premise contraction denotations. The coproduct
component proof has the reverse composition order from the left product
calculation. Conclude Reduced equality by associativity and `denoteR`.

Define Sp and Sq using `f.rho .right (At.there a)` and
`g.rho .right (At.there a)` on the original selections. At native conjR a
parametric path adds 1 and the fresh head has rank 1. Consequently the target
equations are

```text
oldR.rho .right x = Sp + Sq + n + m + 2
newR.rho .right x = Sp + Sq + δ(n) + δ(m) + 4.
```

They imply newR rank≤oldR rank, including ties when n,m∈{1,2}. The new root
is blocked, so a tie does not defeat the descendant conclusion in §5.

The one-selected-premise right cases are separately typed as follows:

| Selected premise | Old selection | Endpoint | New gaps; tail | Blocked constructor |
|---|---|---|---|---|
| f | `more (appendFixed p Λ)` | `K++Λ` | `[[],X]`; `Y++Λ` | `conjunctionFirst A B Γ Θ X Y Λ f̂ g` |
| g | `more (q.prependFixed Δ)` | `Δ++L` | `[[],Δ++Z]`; `T` | `conjunctionSecond A B Γ Θ Δ Z T f ĝ` |

For the selected arity k and sum S, prove

```text
oldR.rho .right x = S + k + 2
newR.rho .right x = S + δ(k) + 3.
```

These imply nonincrease. The k=1 old proofs and the two-premise n=m=1 old
proof are already blocked. Retain the canonical last-retaining right
constructor here. The separate source-first-retention macro and its exchanges
still require their actual ancestry/rank transport for general dispatch.

## 5. Complete addressed conclusion for each family

For every constructed pair w,h above, prove equality in Reduced.Hom,
equal cut counts, the exact CutFree/Atomized preservation statements, actual
blockedness of h and rank nonincrease at the common retained position x.
Occurrence-relation equality follows from Reduced equality.

For the left theorem take arbitrary contexts Γ₀,Δ₀,Θ₀,Λ₀,U,V and

```text
cutLeft : G P Γ₀ (C::Δ₀)
root    : G P (C::Θ₀) Λ₀
w, h    : G P U V
a       : ProofAddress root w
x       : At U C
hr      : ReducibleL cutLeft root a x,
```

where w and h are the actual old/new constructions and x is their proved
common retained position. Obtain h.CutFree from hr.cutFree and count
preservation. Use the local equality and `a.replace_denote` for rebuilt
denotation equality. Then apply `ReducibilityBoundary.descendants_left` with
the constructed blockedness proof, `(fun z hz => hr.entry_unique z hz)`, and
the proved rank inequality. The conclusion must be

```text
∀ {I J : List (NormalForm P)} {v : G P I J}
  (b : ProofAddress h v) (y : At I C),
  ReducibleL cutLeft (a.replace h) ((a.inserted h).append b) y →
    v.rho .left y < w.rho .left x.
```

For the right theorem take `root : G P Γ₀ (C::Δ₀)`,
`cutRight : G P (C::Θ₀) Λ₀`, `a : ProofAddress root w`, `x : At V C`, and
`hr : ReducibleR root cutRight a x`. Use `descendants_right` to prove

```text
∀ {I J : List (NormalForm P)} {v : G P I J}
  (b : ProofAddress h v) (y : At J C),
  ReducibleR (a.replace h) cutRight ((a.inserted h).append b) y →
    v.rho .right y < w.rho .right x.
```

The existing boundary proof excludes b=root by blockedness. For every proper
b it uses replacement ancestry, entry uniqueness and strict descent along
the actual nonempty path. Thus it covers surviving descendant contractions
as well as newly introduced ones. It does not require nonincrease at every
fixed position. Do not add a caller-supplied entry, rank or reduct hypothesis.

## 6. Integration, checks and continuation

Implement the constructions and their equalities together; do not end the
task after context arithmetic or a classification lemma. Local Codex should
check inhabited singleton/mixed-arity examples, repeated equal fixed C
positions, empty gaps/tails, P=Empty where the data are inhabited, and
cut-containing premises for the local algebra. Apply CutFree only where
required by the addressed Reducibility hypotheses.

The rank equations are targets to derive from the actual constructors.
If a calculation fails, retain the exact counterexample or missing inference
and correct this instruction and its reviews; do not change rho, blockedness,
the source grammar or the full theorem to fit the calculation.

After these families, finish logical W5, native/source-macro ancestry
transport, the remaining W1 exchange regimes, and the actual
profile-to-reducer dispatch. The unchanged general Reducibility theorems still
quantify over arbitrary actual addresses, with no external reduct,
InjectiveAscend, rank bound, coherence or equality-reflection premise.
Then continue the outside-site/blocked-ancestor transport and finite multiset
argument toward Blocked-w and cut elimination, followed by the remaining
full-paper obligations in the governing contract.

Run the required Lean verification locally, one heavy process at a time, and
retain exact source identities, exit codes and failed attempts. Review the
actual resulting declarations and dependency/correspondence evidence before
changing any proof-status map. Commit and push verified implementation to main
without force under the standing authorization. Keep instruction/review
material outside the manuscript and its comments. Preserve v4/v5/v6 and the
existing disclosure, tagged substitution exposition, short q_A/e_A proof and
alternative symmetric-fold route.

This cloud pass read the complete v6 TeX and the governing records; it did
not revise or independently re-review the whole manuscript, compile Lean or
TeX, run kernel/audit/submission checks, or inspect the WSL working tree/stash.
The WSL checkout and Windows Downloads are inaccessible here. Deliver this
instruction and its two reviews from committed bytes to Downloads locally,
preserving differing existing files and comparing bytes. The earlier six
undelivered v6 reports remain listed in `CODEX_NEXT_SESSION.txt`.
