# W5 other single-premise mix placement

## Exact proved endpoint and hypotheses

Contracting only g's selected copies after G.mix g f equals mixing the
direct contraction of g with f. The separately typed right dual is proved.
The actual constructor puts its second argument's contexts first.

For arbitrary P,C,gs,Θ set n=gs.length, F=repeated C gs++Θ and
K=gaps gs++C::Θ. Assume n≥2 and existing premises f:G P Φ Ψ.
On the left g:G P F Δ; both old and new have G P (Φ++K) (Ψ++Δ).
Old contracts the g suffix after G.mix g f; new is G.mix (contractL g) f.
For gs=H::hs, old's actual gaps are (Φ++H)::hs and its tail is Θ.
On the right g:G P Δ F; outputs have G P (Φ++Δ) (Ψ++K), and old
uses gaps (Ψ++H)::hs and tail Θ. New is G.mix (contractR g) f.
Nonemptiness of gs follows from n≥2. Public other_premise_left/right keep
original C,gs,Θ and context inputs, without a decomposition hypothesis.

Both prove ofTerm new.denote=ofTerm old.denote. They allow compound C,
cuts, Empty P and empty literal-occurrence sets. No atomicity, CutFree,
Atomized, freshness, DecidableEq, inhabitant, coherence or reflection premise
is required. Generic ContractionBlock stores raw data and typed endpoint
identifications, never the desired equation or rank law. Composition a;b
applies a first.

## Track/drift audit and integration checkpoint

Progress remains on the positive-coherence dependency path: these are actual
source W5 equations and necessary local infrastructure. The completed local
families do not close G2 or establish a global decreasing measure. Repeatedly
choosing another local subcase without testing how the lemmas combine would
risk drifting into an expanding library with no checked reduction procedure.

The audited production tree has Premise and ProofAddress, plus cluster
address validity and CutFree/Atomized descent. It has no proof-occurrence
replacement operation and no implemented Blocked/Reducible/clean-cut layer.
The latter names in the dependency table describe proposed targets. The
recorded scoped search and inspected address definitions are retained as
INTEGRATION_AUDIT.json. This is a construction gap, not evidence against the
published mathematical result. File/declaration counts do not measure the
fraction of the global theorem completed; no completion percentage is claimed.

| Gate | Current evidence | Next required construction |
| --- | --- | --- |
| Local transformations | Both single-premise W5 placements and their duals now compile; preceding W1–W4 scopes remain preserved. | Mixed-premise/binary W5–W6, crossing/absorption and other W1/W2 cases still require classification/proofs. |
| Integration into a larger proof | Typed addresses distinguish identical subproof occurrences. | Typed reconstruction replacing exactly one occurrence, denotation congruence and predicate/count laws; exercise an existing local rewrite beneath a context. |
| Source G2 | Atomic-k, clusters/rank and local rules are proved. | Blocked/Reducible definitions, complete case dispatch, tied-site control and a justified rank/multiset argument, then Reducibility/Blocked-w/clean cuts. |
| G3 | Cut syntax, predicates and representation with cuts exist. | Cut elimination including source constants/zeros and its well-founded measure. |
| M0–M3, R0–R1, C | Structural/zero/union ingredients and conditional faithfulness transfer exist. | Restricted coherence, retractions, positive normal forms and PositiveCoherence. F's premise remains unsupplied. |
| Actual maximality | Conditional transfer theorems are proved. | Faithfulness/Boolean Coherence and remaining presentation/congruence/substitution bridges. Three milestones stay separate. |

The next task is proof-tree replacement, with a concrete local-to-context
example as its integration test. It is a prerequisite for the p.250
Reducibility Lemma's subterm replacement; it does not prove that lemma.
Remaining local case families stay visible instead of being declared complete.

## Baseline, implementation and preservation

Clean main c319ceec00f1a3304648c2044dd0453af78adb9c matched fetched SSH origin.
Fresh strict baseline: 198 files / 7,702 declarations, exit 0, 7.782s.
The integration stash and other checkouts are preserved.

| New module | Function |
| --- | --- |
| GentzenContractionPrepend | Reuse ContractionSelection.prependFixed; derive prefixed raw gaps, arity/unchanged tail, route, retained and complete selected positions. |
| GentzenPrependMixComponents | Concrete product/coproduct prefix component equations and both mix denotation calculations. |
| GentzenOtherMixFibers | Both branch squares and complete retained/fixed/prefix fibers, ordered selection and equal-label exclusion. |
| GentzenOtherMixRules | Actual old/new proofs, original-data public theorems, counts, predicates and tagged relations. |
| GentzenOtherMixRanks | Complete selected sums, n/n−1 losses and every same/opposite branch rank. |
| GentzenOtherMixExamples | Actual repeated tags, n=2/3, Empty constants/compounds, empty prefixes and signed cuts in either/both premises. |

Every older DosenPetric module and its grammar/equation/denotation/tag/
predecessor/rank/predicate interface is byte-preserved. Existing Lean edits
only add six root imports and 126 selected axiom prints. Lean 4.35.0,
Init-only manifest/dependency closure, AGENTS, manuscript v4/v5, diagrams,
references/checksums, historical prompts/reports and the stash are preserved.
No new G primitive, generating equation, mathematical axiom or hom-set zero
is introduced. The prefix operation reuses existing selection infrastructure.

## Source correspondence

Directly consulted: Došen–Petrić, Proof-Theoretical Coherence, September 2007,
[full PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA-256
e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Printed pp.248–253 correspond to PDF pp.260–265, one-based. Rendered p.252
(PDF p.264), the six-page text and prior p.251 render were consulted.
No new source discrepancy was identified.

| Source location | Exact correspondence | Actual implementation |
| --- | --- | --- |
| p.252 following first W5 equation | The analogous equation has mix(g,f), with all selected copies in g. | other_premise_left, prefix gaps and actual oldL/newL. |
| p.252 mix naturality | Move a concrete product/coproduct comparison across mix. | prepend_join/split, prepend_product/coproduct, otherMixL/R and inherited Laws.mix_nat. |
| pp.248–249 clusters | All selected ancestry is in g; each mix and opposite contraction adds a node. | Complete branch fibers and selected_sum/fixed/opposite rank laws. |
| p.252 right analogue | Actual right contraction with coproduct variance. | other_premise_right and separately typed right proof/rank laws, without arrow negation. |
| p.250 Reducibility replacement | Replace one specific reducible subterm in a larger proof. | Not implemented here; the next integration task constructs the replacement prerequisite. |
| pp.252–253 further transformations | Both-premise selection, binary logical cases and Blocked-w. | Separate/open. |

Semilattice Coherence is replaced here by component calculations in the
original Reduced category. Mix naturality is inherited, not added as an axiom.
No occurrence/inclusion equality reflection is used.

## Complete positional and categorical calculation

Let Ξ=Φ on the left and Ξ=Ψ on the right, and e=d.prepend hn Ξ.
Derived gs≠[] allows reuse of the existing selection; e has n selected copies
and, when d.gs=H::hs, gaps (Ξ++H)::hs. The actual endpoint identifications
come from the selection's block. For every g position a and f position b,

```text
e.route.get (At.shift Ξ a) = At.shift Ξ (d.route.get a)
e.route.get (b.before F) = b.before K.
```

The complete ordered selection is d.selected.map (At.shift Ξ), of length n.
Every selected position comes from g. Even when an f position has formula C,
it is excluded by the disjoint prefix/suffix positions. The retained output
has index Ξ.length+(gaps gs).length.

Both old/new g branch traces agree, as do both f traces. At an output
At.shift Ξ z in g's suffix, the g fiber is the full original d.route fiber
at z and f's fiber is empty. At an output b.before K in f's prefix,
g's fiber is empty and f's fiber is [b]. These exhaust all output positions.
At the retained output, the g fiber is the entire selected list; at any other
g output it is the singleton [d.fixed z hz], with unique common original.

The full old outer retained fiber is the shifted selected list. Its fixed
g-suffix fiber is [At.shift Ξ (d.fixed z hz)]; its fixed f-prefix fiber is
[b.before F]. Original branch fibers and full outer fibers remain distinct.

Universal components prove prepend_join/split. The product equation has
type ante(Ξ++K)→conj(ante Ξ)(ante F): e.product followed by the append
inverse at Ξ,F equals append inverse at Ξ,K followed by tensor(id,d.product).
The coproduct equation has type disj(succ Ξ)(succ F)→succ(Ξ++K):
append at Ξ,F followed by e.coproduct equals tensor(id,d.coproduct) followed
by append at Ξ,K. Product/coproduct variance and empty folds are explicit.
Tensor composition gives otherMixL; the right calculation also uses
Laws.mix_nat. Actual G denotations and Rules.mix_congr then prove both
Reduced equalities. Relations follow afterward.

## Exact ranks and preservation

For either side, LC is the direct contraction rank on g: one plus its complete
selected rank sum. All n selected paths gain one mix node in old. Thus old
outer rank=LC+n, while new retained rank=LC+1.

| Position / rank | Old | New |
| --- | --- | --- |
| Compared contraction subterm | LC+n | LC |
| Final retained position | LC+n | LC+1 |
| Other same-side g position | 2+rho(g,a) | 2+rho(g,a) |
| Same-side f position | 2+rho(f,b) | 1+rho(f,b) |
| Opposite-side g position | 2+rho(g,a) | 2+rho(g,a) |
| Opposite-side f position | 2+rho(f,b) | 1+rho(f,b) |

The same-side fixed g position uses its computed d.fixed original; the other
rows use the exact original branch positions. Balance old+1=new+n gives
endpoint loss n−1, strictly positive for n≥2. Contraction loss is n.
Empty prefix blocks do not remove the actual mix node. The earlier placement's
correction is independently confirmed here: the old opposite contraction
contributes a node as well as mix. No rank definition was changed.
These are local syntax balances, not quotient-rank or global termination laws.

Both cut counts equal f.cutCount+g.cutCount, with actual g+f order commuted
explicitly. Both CutFree/Atomized predicates are equivalent to the corresponding
conjunction on f and g. Tagged relation equality follows from Reduced equality.
Premises may contain cuts; compound C is permitted; empty hom-sets are preserved.

## Inhabited examples

With gs=[[C],[C]], Θ=[C] and Ξ=[C], all six source positions have label C.
Original g selection has indices [1,3]; actual outer selection [2,4].
The retained output index is 3. The full old outer map is [0,1,3,2,3,4].
Both original g maps are [some 1,some 3,some 2,some 3,some 4]; f's single
position maps to 0 and is unselected. Original retained g fiber has indices
[1,3], f's is empty; the full outer retained fiber has indices [2,4].
The actual prefixed gap list is [[C,C],[C]].

Actual signed cut identities and prefix thinnings supply both signs and cuts
in either premise or both, with total counts one or two. Fixed g ranks agree
on both sides; f ranks drop one; opposite g ranks agree. old_opposite_not_one
rules out the previously incorrect omitted-node formula on an actual premise.
Empty P constant and atomized compound proofs supply two/three copies,
empty/nonempty fixed blocks and empty literal-occurrence sets. Both compound
equalities/Atomized examples compile. Three-copy endpoint loss is two on
both sides; empty-prefix mix adds a node on both. No G [] [] premise is used.

## Verification, reviews and evidence

Final strict verification: 204 source files / 7,859 audited declarations,
an increase of 157. All 126 new theorems have selected axiom prints; exact
public types cover all 142 explicit new declarations. The complete transitive
audit and public import closure pass. Only propext, Quot.sound and
Classical.choice are permitted; no choice-free claim.

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 19.163 |
| python3 scripts/check-audit-boundaries.py | 0 | 8.25 |
| python3 scripts/check-presentation-boundaries.py | 0 | 1.198 |
| manuscript SHA256SUMS | 0 | 0.011 |
| git diff --check | 0 | 0.023 |
| git diff --cached --check | 0 | 0.011 |

Exact public-type queries pass in 4.376s; standalone example build passed in 5.252s.
All five controls reject with expected diagnostics and Lean exit 1: direct,
private and hidden external axioms, distinct tagged projections identified
by rfl, and a zero lacking a correctly typed existing-arrow witness.
Heavy checks were sequential after the last proof edit.

Failed attempts are retained: prefix route recursion, automatically dropped
parameters, dependent record-field transport, selected-sum parameter order and
an unused simplification argument. Repairs expose the needed typed equalities;
no theorem target, rank, source equation, old interface or heartbeat changed.

Evidence: provenance/wsl-gentzen-w5-other-premise-mix/ and matching
.codex-work/ contain commands/exits/timings, versions, source/declaration and
import closure, exact types/axioms, controls, failed attempts, source access
and the integration audit. The [hostile review](reviews/GENTZEN_W5_OTHER_PREMISE_MIX_HOSTILE.md)
and [writing review](reviews/GENTZEN_W5_OTHER_PREMISE_MIX_WRITING.md) inspect
actual arguments and current maps; these are AI-assisted author-side reviews,
not independent certification. Separate receipts compare checked source with
committed bytes and main/origin/main/live SSH refs and verify conflict-preserving
Downloads copies. No self-referential commit hash is embedded in this report.

Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service, fresh manuscript layout/compilation, publication, licensing
and visibility changes did not run. All-site replacement, source classification,
Reducibility, Blocked-w, elimination/coherence and unconditional maximality
are open. The [next task](CODEX_GENTZEN_PROOF_REPLACEMENT.txt) addresses the
replacement integration gate explicitly.
