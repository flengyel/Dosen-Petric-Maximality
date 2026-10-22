# Contextual factorization report

The four contextual factorizations (gη), (gε), (gηf) and (gεf) are proved
unconditionally in the equation-generated reduced quotient. Typed one-hole
contexts, their raw and quotient actions, the exact source g recursions, and
tagged occurrence compatibility are implemented. No coherence assumption,
new generating equation or equality reflection is used.

Starting checkpoint: `0f001da5d13a3fd0ccdf33be5e5c5799b9ede101` on clean main. SSH origin was fetched with
Git; local main and origin/main agreed. Completed presentation, normalization,
signed labels and reduction were reused. The restricted 21-constructor grammar
and 61 equation schemas, all earlier reduction sources/reports, pinned Lean
4.35.0, Init-only dependency policy, manifest and manuscript v4 are unchanged.

## Exact endpoints and hypotheses

All statements quantify over arbitrary `P : Type u`. No inhabitant,
decidable equality, finite enumeration or freshness condition is required.
`K : Reduced.Context P` has one hole, with arbitrary signed-literal/constant
normal forms at fixed surrounding positions. Plugging selects that one position,
including when identical formulas occur elsewhere.

`K.mapTerm : Term P A B → Term P (K.plug A) (K.plug B)` preserves
Reduced.Derives, identities and composition. The induced covariant endofunctor
on Reduced.category P has object action plug, arrow action map and proved
map_id/map_comp. Quotient well-definedness is established by map_derives
before map is defined. Raw identity/composition derivations use Quotient.exact
for this same syntactic Derives quotient, not inclusion or a relation kernel.

`K.gConj B : Term P (K[top] ∧ B) K[B]` and
`K.gDisj B : Term P K[B] (K[bot] ∨ B)` use only structural terms of the
unchanged reduced grammar. Each has the hole plus all four recursive cases.

Here are the exact generalized theorems, where semicolon executes left first,
X = K[top], Y = K[bot], r+ = rightIn conj, r− = rightOut disj, and [g]
is the quotient class of a raw term:

```
gEta (h : Hom top B):
  K.map h = r+ X ; (id X ∧ h) ; (id X ∧ zero B) ; [gConj K B]

gEpsilon (h : Hom B bot):
  K.map h = [gDisj K B] ; (id Y ∨ zero B) ; (id Y ∨ h) ; r− Y

gEta_comp (h : Hom top B) (f : Hom A X):
  f ; K.map h = r+ A ; (id A ∧ h) ; (f ∧ zero B) ; [gConj K B]

gEpsilon_comp (h : Hom B bot) (f : Hom Y A):
  K.map h ; f = [gDisj K B] ; (f ∨ zero B) ; (id A ∨ h) ; r− A
```

Each equation is in Reduced.Hom with the displayed endpoints. Taking
h = ofTerm(eta p), B = neg p ∨ pos p, or h = ofTerm(epsilon q),
B = pos q ∧ neg q, gives exactly the source's four atomic equations.
These arrow parameters are existing-arrow witnesses. Zeros remain
endomorphisms; no arrow is installed between arbitrary endpoints.

## Source correspondence and direct proof

The [source correspondence](PRESENTATION_CORRESPONDENCE.md#contextual-factorizations-in-the-reduced-syntactic-category)
records every recursion case and intermediate type, composition convention,
unit/distributor laws, and exact factorization displays. Source: Došen–Petrić,
*Proof-Theoretical Coherence*, September 2007 revision,
[author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
§14.2 printed pp.318–321 / one-based PDF pp.330–333.
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Table 2 p.49, the p.101 unit consequences and §11.5 p.270 were also checked.

The rendered p.319 disjunctive hole display has B → top ∨ B. Its preceding
general type and the named unit map sigma-disj-left-in in Table 2 p.49 require
B → bot ∨ B. This discrepancy is confirmed visually and retained explicitly;
the construction uses the correctly typed named unit map. No ill-typed source
text becomes a Lean equation. Source/cache/render hashes and locations are in
`provenance/wsl-contextual-factorization/source-consultation.json`.

The source invokes Distributive Dicartesian Coherence (§11.5) in the final
sentence of the (gη) contextual induction on p.319; (gε) is dual on p.320.
This development derives only the needed structural instances directly.
Pentagon, triangle, naturality and explicit inverse cancellation give the
right-unit/associator law and its inverse. Hexagon and symmetry give the
right-placement shuffle laws. Product/coproduct unit laws and dist_snd/dist_inl
prove the p.270 unital d identities; the mixed cases expand the actual dR.
No same-connective medial replaces a mixed distributive composite.

The g maps are natural in B and have unit components rightOut/rightIn.
Naturality at h, followed by unit inverses, gives the factorization paths.
Inside Reduced, generic proved DiagonalData provides terminality/initiality;
zero_law then gives zero_top/zero_bot and uniqueness of parallel arrows with
domain top or codomain bot. That uniqueness absorbs the explicit zero factor.
Unit naturality and tensor composition give both composed forms.
The four factorization dependency prints contain only Quot.sound.

## Proved declarations and occurrence endpoints

| Module | Proved/defined declarations |
| --- | --- |
| ReducedLaws | Quotient structural wrappers and Laws for the unchanged 61 inherited schemas; no new Equation constructor. |
| ReducedStructure | conjMonoidal/conjDiagonal and opposite-category disjMonoidal/disjDiagonal; zero_top/zero_bot, fromTop_unique/toBot_unique, rightIn_tensor/rightOut_tensor, shuffle_unit_out/in, dist_top/dist_bot/distRight_top, disj_shuffle_dist_top/conj_shuffle_dist_bot. |
| ReducedContexts | Context, plug, mapTerm, map_derives, map, map_ofTerm/left/right/hole, map_id/map_comp, mapTerm_id/mapTerm_comp. |
| ContextualMaps | gConj/gDisj; gConj_nat/gDisj_nat; gConj_top/gDisj_bot; gEta/gEpsilon; gEta_comp/gEpsilon_comp. |
| ContextOccurrences | Fixed, encode/decode and both inverse laws, fixedEmbedding/holeEmbedding, their injectivity/disjointness, relation_mapTerm, occurrence_map/occurrence_map_decode, top_occ_fixed/bot_occ_fixed, occurrence_comp, eta_prefix_relation/epsilon_suffix_relation, gEta_comp_relation/gEpsilon_comp_relation. |

Fixed K is the type of all surrounding occurrence tags. The inverse
coordinates identify Occ(K[A]) with `Sum K.Fixed A.formula.Occ`.
The action's occurrence relation is the sum of identity on fixed tags and the
supplied arrow relation on hole tags. Both embeddings are injective and their
images disjoint, even for repeated equal signed literals. Constants have Empty
hole occurrences; top_occ_fixed/bot_occ_fixed explicitly show that every tag
then comes from the fixed part.

For E_p = neg p ∨ pos p, the composed η comparison is, for x : Occ(A),
y : Occ(K[E_p]),

```
occurrenceMap (f ; K[eta p]) x y ↔
  occurrenceMap ((f ∧ zero E_p) ; [gConj K E_p]) (Sum.inl x) y.
```

For D_q = pos q ∧ neg q, x : Occ(K[D_q]), y : Occ(A), the ε comparison is

```
occurrenceMap (K[epsilon q] ; f) x y ↔
  occurrenceMap ([gDisj K D_q] ; (f ∨ zero D_q)) x (Sum.inl y).
```

Thus the source's finite-ordinal “same pairs” claim becomes a well-typed
pointwise comparison with endpoint embeddings. The proofs interpret already
proved syntactic equalities and use composition preservation and empty atomic
relations. Relation equality never proves equality in Reduced.

## Verification and retained evidence

Baseline `bash scripts/verify.sh` exited 0: 33 Lean source files and 1950
project declarations. The final sequential run completed at
2026-10-22T22:36:47.745920+00:00:

| Actual command | Exit / outcome |
| --- | --- |
| `bash scripts/verify.sh` | 0; **38 Lean files, 2296 audited project declarations**, Lean 4.35.0 strict build and transitive axiom audit. |
| `python3 scripts/check-audit-boundaries.py` | 0; complete public production import closure; direct-axiom, private-axiom and hidden-dependency fixtures each rejected with Lean exit 1. |
| `python3 scripts/check-presentation-boundaries.py` | 0; identified-projections and zero-without-arrow-witness fixtures each rejected with Lean exit 1. |
| `cd manuscript && sha256sum -c SHA256SUMS` | 0; all retained v4 checksums pass. |
| `git diff --check` | 0. Repeated after documentation and staging. |

Permitted axioms: propext, Quot.sound, Classical.choice. The full audit checks
all 2296 project declarations. New factorization/unit/zero results print
Quot.sound only; raw congruence preservation has no axioms. Coordinate/relation
results use propext, with Quot.sound for quotient arguments. No selected new
endpoint uses Classical.choice. No proof hole, custom mathematical axiom,
native_decide, new dependency, altered faithful-interface definition or
assumed Reduced.Faithful instance was added. One heavy process ran at a time;
old constructions were reused without a clean rebuild. Development elaboration
and rewrite errors were corrected before the recorded final run.

Durable evidence: `provenance/wsl-contextual-factorization/`; runtime evidence:
`.codex-work/contextual-factorization/`. The strict log records baseline HEAD
and exact checked working-source hashes, not a claim that the new files were
already committed. SOURCE_SHA256SUMS covers source, tools and manifest;
boundaries.json confirms the unchanged old sources and 21/61 schema counts.
EVIDENCE_SHA256SUMS covers retained logs, command/exit JSON, control diagnostics,
and source metadata. The five fixtures and both control report JSON files are
retained. Final commit/ref equality and Downloads receipts are separate runtime
records because a report cannot embed its own enclosing commit hash.

Source manifest SHA-256: `f59d275cbdbcbe124f5056b1c2ef0b7c71505cd8f3a07a4147dca38ec8577f7a`.
Evidence manifest SHA-256: `50ee8998b1095f02b01111ab48fa7e99a6a8d6fa47898e4521a5e7b3bc098d04`.
Hostile review SHA-256: `88ad13111b8e7d4b0eb926aa39cd996b3d656fb6da20917c63c230b3aee2e8d5`.
Writing review SHA-256: `13e4d5eafbb5eed69e2c7c18b79ec3b3964b6e60dd5ec2f937c951a0a4883a4e`.

Both reviews are author-side, not independent certification. The writing review
directly consults the verified cached Knuth–Larrabee–Roberts text; historical
access records are preserved. No manuscript revision was needed. No independent
kernel replay, independent complete source audit, Challenge/Solution or
Comparator run, official preflight/service verification, novelty review, new
manuscript compilation/layout review, publication, visibility change or license
change was performed.

## Remaining obligations and next concrete task

The source's common atomic η/ε factorization on pp.320–321 is not implemented.
Its final equality step invokes Zero-Identity Distributive Dicartesian
Coherence (§12.5) on the η/ε-free middle arrows, p.321. That positive-core
coherence theorem and the general §11.5 coherence theorem remain unproved in
Lean. The specific contextual structural identities above do not assume them.
Reduced.Faithful, inclusion equality reflection, Boolean Coherence and a full
faithful OccurrenceInterpretation remain open. The conditional faithfulness
transfer is unchanged and conditional.

Full raw reduction has no proved quotient descent. Derived contravariant arrow
negation and its laws, full congruence/substitution bridges, source equivalence,
remaining Appendix A profiles/ordinals/renaming and actual unconditional
maximality/model corollary remain separate. The three coverage milestones
retain their distinct meanings.

Next: construct the common atomic η/ε factorization of reduced raw terms with
an explicitly η/ε-free positive middle term and typed endpoint embeddings,
following pp.320–321. Prove the required positive-core §12.5 coherence separately
before using that factorization to conclude Reduced.Faithful. Do not replace
the reduced quotient or infer equality from inclusion/occurrence comparisons.
