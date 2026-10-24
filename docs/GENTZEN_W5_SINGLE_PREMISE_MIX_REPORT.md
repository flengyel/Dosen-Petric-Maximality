# W5 single-premise mix

## Exact proved endpoint and hypotheses

Contracting only g's selected copies after G.mix f g equals mixing f with
the direct contraction of g. The separately typed right dual is also proved.
G.mix f g puts the second argument's contexts first.

For arbitrary P,C,gs,Θ let n=gs.length, F=repeated C gs++Θ and
K=gaps gs++C::Θ. Assume n≥2 and existing premises. On the left they are
f:G P Φ Ψ and g:G P F Δ. Old mixes f,g and contracts with gaps gs,
tail Θ++Φ, using actual casts. New is G.mix f (contractL gs/Θ g).
Both outputs have exact G P (K++Φ) (Δ++Ψ).

On the right f:G P Φ Ψ and g:G P Δ F. Old contractsR gs with tail
Θ++Ψ after mix; new is G.mix f (contractR gs/Θ g).
Both outputs have exact G P (Δ++Φ) (K++Ψ).
W5.SinglePremiseMix.single_premise_left/right quantify over original inputs,
and prove ofTerm new.denote=ofTerm old.denote. No atomicity, CutFree,
Atomized, freshness, DecidableEq, variable inhabitant, coherence or
equality-reflection hypothesis is required. Premises may contain cuts.
Composition a;b applies a first.

The reusable implementation takes an existing ContractionBlock d:F/K whose
fields are raw contraction data and typed endpoint identifications. Its
canonical block C gs Θ has reflexive endpoint identifications. No desired
square, denotation equation or rank law is stored as an input.

## Correction to the continuation's rank target

The historical CODEX_W5_SINGLE_PREMISE_MIX.txt predicted opposite-side g
ranks old=1+rho and new=2+rho, with f unchanged at 1+rho. That prediction
omitted the old outer contraction's opposite-side node. The unchanged
G.rho_contractL_right/rho_contractR_left definitions give a node at every
opposite-side position. Thus old is 1+(1+rho), and the proved table below
has g unchanged at 2+rho and f decreasing from 2+rho to 1+rho, on either
sequent side. Actual signed cut examples and old_opposite_not_one refute
the historical old=1+rho target.

This corrects a planning prediction, not the source equation or manuscript.
The historical prompt is preserved; current maps and the next prompt use
the proved formulas. No rank definition or transformation was weakened.

## Baseline, implementation and preservation

Clean main 230152d412044a4948d639ed43e7812a739a9df5 matched fetched SSH
origin. Fresh strict baseline: 192 files / 7,543 declarations, exit 0,
4.033s. The integration stash and other checkouts are preserved.

| New module | Function |
| --- | --- |
| GentzenContractionMixComponents | Actual extension naturality from universal components, product/coproduct split equations, and both mix denotation calculations. |
| GentzenMixRanks | Exact branch-tagged predecessors and singleton rank laws for both mix premises and both sides; casted opposite contraction laws. |
| GentzenSingleMixFibers | Both concrete branch squares, complete retained/fixed fibers, ordered selected transport and same-label exclusion of f. |
| GentzenSingleMixRules | Actual old/new constructors, original-data public endpoints and preservation. |
| GentzenSingleMixRanks | Complete selected sums, exact rank balances and every fixed/opposite branch table entry. |
| GentzenSingleMixExamples | Actual constants, compounds, equal labels, two/three copies, cuts in either/both premises and corrected opposite ranks. |

Every older DosenPetric module and grammar/equation/denotation/tag/predecessor/
rank/predicate interface remains byte-preserved. Existing Lean edits only add
root imports and 118 selected axiom prints. Lean 4.35.0 and Init-only dependency
closure/manifest are unchanged. Manuscript v4/v5, diagrams, references/checksums,
AGENTS and historical reports/access records are preserved. No new G primitive,
generating equation, mathematical axiom or empty-hom-set zero is supplied.

## Source correspondence

The directly consulted source is Došen–Petrić, Proof-Theoretical Coherence,
September 2007, cached from
[the full PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Printed pp.248–253 are PDF pp.260–265, one-based. Rendered p.251 and the
continuation/right analogue on p.252 were consulted. No new source discrepancy.

| Source location | Exact correspondence | Actual Lean proof |
| --- | --- | --- |
| p.251 W5 first equation | Only the selected copies in g are contracted after mix(f,g). | Original-data single_premise_left and actual oldL/newL. |
| p.252 (m nat) | Naturality of the reduced mix arrow, with actual append comparisons. | extend_join/split, extend_product/coproduct, mixL/R and Laws.mix_nat. |
| pp.248–249 clusters | Every selected path comes from g; each mix adds a node, and opposite contraction adds a node too. | Complete branch predecessors/fibers, selected_sumL/R and opposite_g/f_old/newL/R. |
| p.252 right analogue | Actual contractR and correctly variant coproduct comparison, without arrow negation. | single_premise_right and separately typed right laws. |
| p.252 further W5 cases | mix(g,f), both-premise selection and binary logical cases. | Separate/open; the other single-premise placement is the next task. |

The Semilattice Coherence appeal is replaced by component calculations in the
original Reduced category. Mix naturality is an already inherited equation,
not an added axiom or a reflection of occurrence equality.

## Complete positional and categorical calculation

Write e=d.extend Ξ, with Ξ=Φ on the left or Ψ on the right.
It is an actual contraction with the same gs and tail extended by Ξ.
For every original g position a and f position b,

```text
e.route.get (a.before Ξ) = (d.route.get a).before Ξ
e.route.get (At.shift F b) = At.shift K b.
```

These are concrete positional squares, with original tags and domains.
The complete ordered selection is d.selected.map (before Ξ), of length n.
Every selected entry comes from g; an f occurrence is excluded even if its
formula label is C. The final retained index is (gaps gs).length, in g's prefix.

The old and new complete g branch traces are equal, as are the f traces.
At a final g-prefix z.before Ξ, the g fiber is the entire d.route fiber of z
and the f fiber is empty. At a final f-suffix At.shift K b, the g fiber is
empty and the f fiber is exactly [b]. Thus at the retained position the
original g fiber is all n selected positions. At any other g-prefix z it is
the singleton [d.fixed z hz]. These exhaust all final positions and prove
unique common originals with premise tags retained.

The full old outer retained fiber is the embedded selected list; its fixed
prefix fiber is [(d.fixed z hz).before Ξ] and suffix fiber [At.shift F b].
These are complete fiber equations, not membership-only comparisons.

Universal components give extend_join/split. The conjunction equation has
type ante(K++Ξ)→conj(ante F)(ante Ξ): extension product followed by the
actual append inverse equals append inverse at K followed by tensor of
d.route.product and identity. The disjunction equation has type
disj(succ F)(succ Ξ)→succ(K++Ξ), with tensor of d.route.coproduct and
identity before the append map at K.

The left mix calculation follows by tensor composition. The right calculation
also uses Laws.mix_nat to pass the coproduct comparison through mix. Actual
G denotations and Rules.mix_congr then give both principal Reduced equalities.
No coherence, occurrence reflection, inclusion reflection or inverse for
either input proof is assumed.

## Exact ranks and preservation

Separately for each side let LC be the direct contraction rank on g, one
plus the complete original selected sum. All n selected paths gain one mix
node in old; thus old outer rank=LC+n. New retained rank=LC+1.

| Position / rank | Old | New |
| --- | --- | --- |
| Compared contraction subterm | LC+n | LC |
| Final retained position | LC+n | LC+1 |
| Other same-side g position | 2+rho(g,a) | 2+rho(g,a) |
| Same-side f position | 2+rho(f,b) | 1+rho(f,b) |
| Opposite-side g position | 2+rho(g,a) | 2+rho(g,a) |
| Opposite-side f position | 2+rho(f,b) | 1+rho(f,b) |

The fixed same-side a is the computed d.fixed original; opposite-side a and
f's b are the exact original positions. Endpoint balance old+1=new+n gives
loss n−1 and strict decrease for n≥2; contraction loss n is strict too.
Even an empty f-side block leaves the actual mix node in rank calculations.
These are local syntax equations, with no global termination, quotient-rank,
arbitrary-context replacement, Reducibility or Blocked-w conclusion.

Both cut counts equal f.cutCount+g.cutCount. Both CutFree predicates are
equivalent to f.CutFree and g.CutFree; both Atomized predicates are equivalent
to f.Atomized and g.Atomized. Compound C needs no atomicity restriction.
Full tagged relation equality follows from Reduced equality. Existing-arrow
premises and empty hom-sets remain intact.

## Inhabited examples

For gs=[[C],[C]], Θ=[C], Ξ=[C], every source label is C. Both selected
lists have indices [1,3]. The full old six-C map is [0,2,1,2,3,4].
Both original g maps are [some 0,some 2,some 1,some 2,some 3]; the
single f position maps to final index 4 and is unselected. Retained g fiber
has indices [1,3] and f fiber is empty.

Actual signed cut identities and prefix thinning give inhabited left/right
premises with cuts in either premise or both, and total cut counts one or
two. Both literal signs occur. Fixed g ranks agree; f ranks drop one on
both sides; opposite g ranks agree. old_opposite_not_one is a regression
against the historical planning error.

Actual Empty P constant/atomized premises cover empty f source or target,
two and three copies, empty/nonempty fixed gaps/tails, compound formulas and
empty literal-occurrence sets. The three-copy endpoint loss is exactly two
on both sides. Both compound Atomized/equality instances compile. No example
uses an impossible G [] [] or an uninhabited hypothetical premise.

## Verification, reviews and evidence

Final strict verification: 198 files / 7,702 audited declarations, an increase
of 159. All 118 new theorems have selected axiom prints and exact public-type
queries, supplementing complete transitive audit and public import closure.
Only propext, Quot.sound and Classical.choice are permitted; no choice-free claim.

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 3.961 |
| python3 scripts/check-audit-boundaries.py | 0 | 7.974 |
| python3 scripts/check-presentation-boundaries.py | 0 | 1.163 |
| manuscript SHA256SUMS | 0 | 0.012 |
| git diff --check | 0 | 0.008 |
| git diff --cached --check | 0 | 0.008 |

All five controls reject with expected diagnostics and Lean exit 1: direct,
private and hidden external axioms, identification of distinct tagged
projections by rfl, and zero without a correctly typed existing-arrow witness.
Heavy checks were sequential after the last proof edit.

Failed elaborations remain retained: composition direction/normalization,
an omitted automatically dropped parameter, explicit argument typing and
semireducible Place/field aliases in selected sums. Typed equality composition
resolves the scalar sums. No target, source equation, old interface or heartbeat
limit was weakened. Final example build command passes in 5.284s.

Evidence is retained under provenance/wsl-gentzen-w5-single-premise-mix/ and
.codex-work/gentzen-w5-single-premise-mix/: baseline/final commands, versions,
exits/timings, exact types/axioms, declarations/source inventories, source
access, controls and failed attempts. The
[hostile review](reviews/GENTZEN_W5_SINGLE_PREMISE_MIX_HOSTILE.md) and
[writing review](reviews/GENTZEN_W5_SINGLE_PREMISE_MIX_WRITING.md) inspect actual
proofs/maps and the corrected rank table. These are author-side AI-assisted
reviews, not independent certification. Separate receipts compare checked and
committed bytes, SSH refs and Downloads copies; no self-referential commit hash.

Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service, fresh manuscript layout/compilation, publication, licensing
and visibility changes did not run.

## Next concrete proof obligation

Prove the other single-premise W5 placement, with selected g in G.mix g f,
and its right dual; see [the continuation](CODEX_W5_OTHER_PREMISE_MIX.txt).
Mixed-premise/binary logical W5/W6, remaining W1/W2, all-site replacement,
Reducibility, Blocked-w, cut elimination, restricted coherence, PositiveCoherence,
Reduced.Faithful, Boolean Coherence and unconditional maximality remain open.
Three milestones and conditional transfers are unchanged. Unfinished
reconstruction of published work does not establish a manuscript defect.
