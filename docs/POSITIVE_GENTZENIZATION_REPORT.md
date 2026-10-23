# Typed positive Gentzenization report

G0 and G1 are completed: a genuine typed Gentzen proof syntax has a positive
raw denotation, and every positive reduced raw term has an existential Gentzen
representative with the requested singleton-unit equation. The equivalent
original-endpoint equation and tagged occurrence correspondence are proved.
The representatives may contain cuts. Cut elimination and coherence are open.

Starting checkpoint: `4db7a0d1045fcb070fcafb423558cb97ecaef153`, clean main.
SSH origin was fetched and local/tracking main agreed. The actual baseline
strict run passed with 49 Lean files and 2875 audited declarations. No reset,
unrelated edit, dependency change or reconstruction of completed reduction,
contextual/common factorization, support or zero/union algebra was needed.
Manuscript v4 and all old Lean modules/reports remain unchanged. The original
21 raw / 61 equation / 19 positive constructor schemas are byte-identical.

## Exact endpoints and hypotheses

All declarations are in DosenPetric.Reduced.Gentzen unless stated otherwise.
P : Type u is arbitrary. No Nonempty P, DecidableEq P, enumeration, fresh
variable, coherence, faithfulness or representation premise is assumed.
“Positive” is the eta/epsilon-free arrow predicate; objects include both
literal signs, both constants and arbitrary nested binary formulas.
Composition comp f g executes f first.

The context objects are

```
ante Γ = Γ.foldr NormalForm.conj .top
succ Δ = Δ.foldr NormalForm.disj .bot.
```

fold is structurally recursive for computational use; fold_as_foldr proves
these equalities. Neither associativity nor unitality of formulas is definitional.
The grammar is an inductive G P Γ Δ with sixteen schemas: atomic identity,
atomic zero, topI, botE, exchange on each side, positional thinning on each
side, full separated multiple contraction on each side, the four logical rule
families, mix and contextual cut. There is no raw-term/positive-term embedding,
general composition or tensor constructor, primitive d/union/compound zero,
or empty-sequent leaf. Atomic leaves range over complete Literal P values.

The two constant leaves and denotations are exactly

```
G.topI : G P [] [.top]      denote = rightIn disj top : top → top∨bot
G.botE : G P [.bot] []      denote = rightOut conj bot : bot∧top → bot.
```

G.denote : G P Γ Δ → Term P (ante Γ) (succ Δ) is defined by the actual
structural composites. G.denote_positive proves positive membership for every
proof tree. G.no_empty proves G P [] [] → False through denotation, reduced
inclusion and the established impossibility of Presentation.Hom top bot.
No faithfulness or identification of the two empty contexts enters that proof.

For t : Term P A B and h : t.Positive, gentzenization proves

```lean
∃ g : G P [A] [B],
  ofTerm g.denote =
    comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B))
```

and gentzenization_decode proves

```lean
∃ g : G P [A] [B],
  comp (rightIn .conj A)
    (comp (ofTerm g.denote) (rightOut .disj B)) = ofTerm t.
```

The singleton endpoints are A∧top and B∨bot. The arrows removing/inserting
those units are part of the statements and proofs. Represented f is only the
existential predicate ∃g, decode g.denote = f, used to organize the induction.
It is not a constructor or an assumed instance. positive_represented covers
all nineteen Positive schemas. No canonical proof, equality preservation for
a chosen translation, or function on quotient arrows is claimed.

## Source rules, order and actual comparisons

Source: Došen–Petrić, Proof-Theoretical Coherence, September 2007 revision,
[author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n is one-based PDF n+12. The full rule-by-rule table in
PRESENTATION_CORRESPONDENCE identifies pp.238–246, 271–273 and 291–292,
all premise/conclusion orders, principal formulas, positional gaps and
compiled denotation declarations. The rendered p.240 was consulted directly.

Iso stores actual positive forward/backward raw arrows and proved inverse
laws. append, under and exchange build context comparisons from associators,
symmetries and units. Equal-list-index transports use termTransport/reindex,
with denote/count compatibility proved by equality elimination. They do not
identify differently bracketed or differently coloured formula objects.

At chooses a whole-formula position by here/there. Route selects each output
position from an input position with exactly the same formula type. Repeated
equal formulas in fixed gaps retain their own positions. Product/coproduct
routing uses pairing/copairing and the actual terminal/initial maps;
product_get/coproduct_get prove its component equations, and
product_positions/coproduct_positions prove equality by the existing reduced
universal properties. These are syntactic equalities, not relation reflection.

Contractions are full separated multiple-copy operations, with n≥2, rather
than adjacent binary contractions whose completeness is assumed. copies keeps
one distinguished C after the fixed gaps and routes each selected copy to it.
The primitive right convention keeps the last copy; contractRFirst constructs
the source's first-copy convention by explicit block exchange and transports.
Its denotation and cut-count equations compile. thinLast supplies the source
rightmost left thinning. Block exchange already has arbitrary fixed prefix,
selected X/Y blocks and fixed suffix. No label comparison or freshness is used.

The head contextual cut has premises f : Γ |- C,Δ and g : C,Θ |- Λ and
conclusion Θ++Γ |- Λ++Δ. Let X=ante Θ, Y=ante Γ, R=succ Δ, S=succ Λ.
Its complete execution-order path is

```
ante(Θ++Γ) --append inverse--> X∧Y --id X ∧ denote f--> X∧(C∨R)
 --d_(X,C,R)--> (X∧C)∨R --((swap_(X,C);denote g) ∨ id R)--> S∨R
 --append--> succ(Λ++Δ).
```

cutAt implements the displayed source cut for f : Γ3 |- Δ2,[C],Δ1 and
g : Γ1,[C],Γ2 |- Δ3, giving (Γ1++Γ2)++Γ3 |- Δ3++(Δ2++Δ1).
It moves only the selected C at each named gap, then uses the head cut.
cutAt_denote and cutAt_count state the composite and its visible cut.
Every empty residual uses top or bot with actual unit arrows. cut_pure and
cut_single prove the empty-residual composition case from dist_top and the
unit laws; no unit-specialized d is simply declared identity.

The conjunction-right mixed arrow is the p.240 e'-disjunction;
sourceDisj_expansion proves the existing mixedDisj expands into exactly those
steps. Disjunction-left uses the separately transcribed Rules.sourceConj,
with the explicit binary path

```
(X∧Y)∧(A∨B) --id∧swap--> (X∧Y)∧(B∨A)
 --assocL--> X∧(Y∧(B∨A)) --id∧d--> X∧((Y∧B)∨A)
 --id∧swap--> X∧(A∨(Y∧B)) --d--> (X∧A)∨(Y∧B).
```

The earlier ReducedWitnesses.mixedConj was a typed witness helper; no general
equality with this source expression was available or inferred. It remains
unchanged, and is not silently substituted for the source composite. The
rendered source is well typed; no new source discrepancy is alleged.
Neither comparison is same-connective medial. Existing historical source
errata and access records remain preserved.

single_split/single_join, append_insert/remove, mixedDisj_bot,
disjInput_out/value and cut_pure supply the precise unital comparisons used
by G1. The empty-source e' case yields actual singleton unit insertions in
our coordinates, not an equality between arrows with different endpoints.
Derived tensorConj/tensorDisj are built from logical rules and have proved
value laws. Generic DiagonalData.assocR_fst/snd/assocR_pair/assocL_pair derive
the needed associator formulas from existing structural/unit laws; the
coproduct cases use the opposite category. These replace the earlier
coherence appeals in the source Gentzenization argument. They do not prove
a general structural or positive coherence theorem.

identityNF and zeroNF recurse on formulas. Their literal cases use the
atomic leaves; the constants use the two basis terms and actual uniqueness
laws. Compound cases use derived Gentzen tensors. zeroNF_value uses both-zero
tensor compatibility and the constant zero/identity results, without a
compound zero leaf. Represented.dist uses genuine contextual cut at B,
conjunction collection, splitDisj and a represented symmetry. Its proof
computes d_(A,B,C) by dist naturality and actual unit cancellations.
No arbitrary-formula arrow is smuggled into the proof grammar.

## Occurrence compatibility and cut interface

G.relation is defined through raw denotation. occurrence_denote proves its
compatibility with the existing well-defined Reduced.occurrenceMap.
singletonOcc and singletonFrom give inverse tagged coordinate maps from
A.formula.Occ to (fold o [A]).formula.Occ, for either connective. Unit positions
are Empty and are eliminated explicitly. The maps are injective without
identifying repeated equal literals or requiring an element of P.

gentzenization_occurrences supplies a g satisfying the first representation
equation and, for all original tagged positions x,y,

```
g.relation (singletonOcc conj A x) (singletonOcc disj B y) ↔ t.relation x y.
```

This follows from the syntactic representation equality in the forward
interpretation direction and the direct encode_relation calculation. It is
not a proof of syntactic equality from relations. Constants and empty
occurrence types are included, and no fullness or general realization claim
for signed-label-respecting relations is assumed.

G.cutCount counts every cut, including subproof cuts, and CutFree means zero
count. cut_not_cutFree, binary cut-free closure, reindex/count and source
cutAt/contractRFirst count laws make this interface usable. Topmost records
two CutFree contextual-cut premises. Atomized checks that every thinning
formula is a literal or constant. None of these definitions supplies a cut
reduction, a well-founded rank, blocked-contraction analysis or cut elimination.

## Positive-constructor coverage

All equalities in this table are in Reduced.Hom. Represented f means existence
of a G proof whose decoded denotation equals f; it is not a constructor of G.

| Positive schema | Checked construction / equality used in positive_represented |
| --- | --- |
| id | G.identityNF / identityNF_value; structural formula recursion, atomic/constant bases. |
| comp | Represented.comp; G.cut with empty residual contexts; cut_pure/cut_single. |
| tensor | Represented.tensor; derived G.tensorConj/tensorDisj and both value laws, built only from logical rules and unit comparisons. |
| assocR | Represented.assocR; proved product/coproduct formulas, not earlier associative coherence. |
| assocL | Represented.assocL; inverse associator product/coproduct formulas. |
| swap | Represented.swap; pair of projections or copair of injections, with proved symmetry component laws. |
| diag | G.diagProof_value; full separated two-copy contraction plus conjunction-right; copies_two_product. |
| codiag | G.codiagProof_value; disjunction-left plus two-copy right contraction; copies_two_coproduct. |
| fst | G.fstProof_value; selected thinning and conjunction-left. |
| snd | G.sndProof_value; selected head thinning and conjunction-left. |
| inl | G.inlProof_value; selected thinning and disjunction-right. |
| inr | G.inrProof_value; head thinning and disjunction-right. |
| rightOut | Represented.rightOut; projection to a unit / copair with a witnessed initial map. |
| rightIn | Represented.rightIn; pairing with a terminal map / unit injection. |
| leftOut | Represented.leftOut; other unit projection / initial copair. |
| leftIn | Represented.leftIn; terminal pairing / other unit injection. |
| mix | G.mixProof_value; source mix rule on identityNF witnesses, then conjunction-left/disjunction-right and explicit unit cancellations. |
| dist | Represented.dist; splitDisj on B∨C, conjunction collection, a represented symmetry and genuine contextual cut at B. dist naturality and the proved singleton laws give exactly d_(A,B,C). No d constructor in G. |
| zero | G.zeroNF / zeroNF_value; atomic zero leaves, both-zero tensor laws and constant zero/identity laws. No compound zero leaf. |

## Declaration inventory and verification

Twenty-one new modules separate contexts/isos, positional routing, rule
composites, the sixteen-schema syntax, source operations/transports, unital
calculations, recursive identities/zeros, structural/distributive
representations, the exhaustive induction, occurrence coordinates and the
analysis interfaces. DECLARATIONS.txt records all explicit declarations with
source line anchors; the strict audit also includes generated declarations.

The actual clean baseline strict run passed: 49 Lean files, 2875 audited
project declarations. Final sequential verification completed at 2026-10-23T02:06:28.122781+00:00.

| Actual command | Exit and outcome |
| --- | --- |
| bash scripts/verify.sh | 0; **70 Lean source files, 3448 audited project declarations**, strict build and transitive axiom audit with Lean 4.35.0. |
| python3 scripts/check-audit-boundaries.py | 0; public import closure passed; direct-axiom, private-axiom and hidden-dependency controls each rejected with Lean exit 1 and expected diagnostics. |
| python3 scripts/check-presentation-boundaries.py | 0; identified-projections and zero-without-arrow-witness controls each rejected with Lean exit 1 and expected diagnostics. |
| (cd manuscript && sha256sum -c SHA256SUMS) | 0; unchanged v4 TeX/PDF checksums passed. |
| git diff --check | 0; repeated after documentation and staging. |

Permitted axioms remain propext, Quot.sound and Classical.choice. The principal
Gentzenization, decoded equation, occurrence theorem and denotation/membership
prints use propext and Quot.sound. G.no_empty additionally uses the permitted
Classical.choice through the existing full-presentation impossibility theorem.
The G grammar, raw sourceConj and generic associator-product lemmas print no
axioms. No custom mathematical axiom, proof hole, native_decide, coherence
assumption or new generating equation was introduced. One heavy verification
process ran at a time with LEAN_NUM_THREADS=1; WSL memory was inspected.
Completed constructions were reused without a clean rebuild. Development
elaboration/typing errors were corrected before the retained final run.

Evidence is retained in provenance/wsl-positive-gentzenization/ and matching
runtime .codex-work/positive-gentzenization/. SOURCE_SHA256SUMS identifies all
checked Lean/audit sources, toolchain, manifest and scripts; SHA-256
`318c5174a6b90afc3d0edf393664d4631edcffe95d0846b4f1ccc9cee28cc07c`. EVIDENCE_SHA256SUMS identifies logs, exact commands and exit
JSON, all five rejected fixtures/diagnostics, declaration inventory, source
consultation and historical preservation; SHA-256 `e730c4290a4b9fc1df91858bb4c09504eb974536cc5ad020c9810e8a62e94743`.
REPORT_SHA256SUMS and RECORD_SHA256SUMS identify the finalized reports and the
updated correspondence/statement/coverage/validation/continuation records.
Manifests exclude themselves. The pinned source and writing-cache hashes,
source page locations and retained p.240 rendering hash are recorded in
source-consultation.json. Rendered PDF evidence remains in the ignored runtime
directory; the book itself is not redistributed as repository source.

The strict log records baseline HEAD plus the actual working-source hashes.
It is not mislabeled as a build of the baseline commit. After committing, the
source inventory is checked against git show HEAD; live SSH ref agreement and
byte-for-byte report delivery receipts are recorded separately at runtime.
The final response supplies the enclosing integration commit, avoiding a
circular self-hash. Historical source/report/manuscript checks are retained
in boundaries.json. The hostile and governing-source writing reviews are
author-side AI-assisted reviews, not independent certification.

Independent kernel replay, independent source-transcription audit,
Challenge/Solution or Comparator comparison, official preflight/service
verification, manuscript recompilation/layout review, publication and
visibility/license changes were not performed. Historical access records
and reports are unchanged.

## Next concrete cut-elimination prerequisite

Implement thinning atomization (Atomic-k Lemma), source §11.2 printed
pp.246–247, extended to constants in §11.5 p.272 and atomic zero leaves in
§12.5 p.291. The actual implemented types give this next target:

```lean
∀ {Γ Δ : List (NormalForm P)} (g : G P Γ Δ),
  ∃ h : G P Γ Δ,
    h.Atomized ∧
    (g.CutFree → h.CutFree) ∧
    ofTerm h.denote = ofTerm g.denote
```

AtomicFormula permits lit l (both signs), top and bot. G.Atomized recursively
requires every inserted thinning formula to be atomic, while preserving the
full proof tree. The first nontrivial task is the source compound-thinning
rewrite, especially left thinning by a disjunction and its dual. Its source
proof invokes semilattice/lattice coherence and a derived (m e) law on p.247.
Those appeals must be replaced with proved reduced structural identities;
the two omitted (m e) schemas cannot simply be added to Reduced.Equation.
G0/G1, typed block operations, routing component laws, logical comparisons,
constant cases and zero/union algebra are available predecessors.

| Obligation | Current status / exact next dependency |
| --- | --- |
| G0 typed syntax/positive denotation | **Proved** by G, denote_positive, the sixteen denotation equations, actual comparisons and source-order macros. |
| G1 existential representation | **Proved** by positive_represented, gentzenization, gentzenization_decode, with gentzenization_occurrences. |
| G2 Atomic-k / clean topmost cuts | **Open**. The displayed atomization target comes first. G.Topmost f g means the two contextual-cut premises are CutFree. Clusters, rank, blocked contractions and the multiset/lexicographic induction remain to be constructed; cutCount is not a claimed decreasing elimination measure. |
| G3 cut elimination | **Open**: for every g : G P Γ Δ, construct h of the same type with h.CutFree and ofTerm h.denote = ofTerm g.denote. Source §§11.2,11.5,12.5 supply a mathematical argument to formalize, not a Lean proof. |
| M0–M3 restricted mix-dicartesian coherence | **Open**: define the smaller mix syntax and settled atomic/path normal forms, prove its composition elimination, zero/constant handling and restricted faithfulness for DNF-to-CNF endpoints (§§10.2–10.3, §12.5 pp.289–290). No such syntax or coherence theorem is supplied here. |
| R0/R1 and PositiveCoherence | **Open**: typed DNF/CNF retractions, cut-free passage to the restricted mix fragment and its normal-form argument (§11.3 pp.264–266, §11.5 pp.270–274, §12.5 p.292). |
| Reduced.Faithful / Boolean Coherence | **Open**. Existing faithful_of_positive_coherence and subsequent transfers remain conditional and unchanged. |

This checkpoint is representation with cuts. It does not prove uniqueness,
cut elimination, restricted coherence, fullness, equality reflection, a quotient
translation, contravariant arrow negation, or unconditional maximality.

## Other remaining obligations

There is no blocker to the requested G0/G1 endpoint. Reduced.Faithful,
Boolean Coherence, faithful OccurrenceInterpretation, inclusion equality
reflection, full raw reduction's equation preservation and quotient descent,
source equivalence, contravariant arrow negation and its laws, congruence
restriction, remaining substitution-schema/Appendix A bridges, actual
maximality and the every-interpretation corollary remain separate open work.
No milestone is promoted by representation with cuts. The completed common
factorization and conditional transfers remain available unchanged.
