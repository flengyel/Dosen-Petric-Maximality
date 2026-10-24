# Blocked contractions, reducible occurrences and selection classification

## Exact checkpoint and scope

The development now has explicit encodings of the seven source blocked left
patterns and separately typed right analogues, reducibility at actual tied
proof occurrences, and an exhaustive finite classification of a contraction's
ordered selected positions. The classification records actual predecessors
and premise tags. It does not construct a reduct or prove a rank decrease.

For arbitrary P, d:ContractionBlock P U K, hn:2≤d.gs.length, and an
existing cut-free premise g:G P U Δ (or g:G P Γ U), classificationL/R
excludes a basis/cut head and supplies a SelectionRegime satisfying its typed
Holds condition on every selected position. No atomicity, freshness,
DecidableEq or inhabitant of P is required. Empty literal-occurrence sets and
compound formulas are allowed. Existing G syntax/equations/ranks are unchanged.

## Source encoding and positions

Directly consulted: Došen–Petrić, Proof-Theoretical Coherence, September 2007,
[full PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA256
e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Printed pp.248–253 are PDF pp.260–265 one-based. The p.250 render, six-page
text, W1–W6 and right-analogue discussion were consulted. No new discrepancy.

BlockedL/R are inductive predicates on actual contracted G proofs. Their
constructors supply original premises, context lists and actual selected gaps;
there is no reduct, desired denotation equation or rank law in their inputs.
The left correspondence is:

| p.250 pattern | BlockedL constructor | Actual gs / tail |
| --- | --- | --- |
| w gamma 1, mix(f,g) | gammaMix | [Z,T++X] / Y, for f:X,C,Y and g:Z,C,T. |
| w gamma 2, conjunction-right | gammaConj | [X,Y++Z] / T. |
| w gamma 3, disjunction-left | gammaDisj | [X,Y++Z] / T++[A∨B]. |
| w conjunction 1 | conjunction | [X,Y] / [], with C=A∧B and the terminal logical principal selected. |
| w disjunction 1 | disjunctionFirst | [X,Y++Z] / [], selecting a first-premise C and the new principal. |
| w disjunction 2 | disjunctionSecond | [X++Z,T] / [], selecting a second-premise C and the new principal. |
| w disjunction 3 | disjunctionBoth | [X,Y++Z,T] / [], selecting both parametric copies and the new principal. |

Here C and every displayed occurrence are typed. The last case has three
selected copies; the other six have two. left2/left3 and right2/right3 use
actual primitive bounds 2≤2 / 2≤3. selected2_indices/selected3_indices give
all ordered offsets, including fixed empty/nonempty gaps. BlockedL.lower and
BlockedR.lower exhibit the actual retained lower-contraction position.

The primitive G.disjL has a head principal, while the source left-disjunction
rule uses terminal inputs/principal. disjLLast constructs the two input
exchanges and one output exchange explicitly; conjLLast uses the actual
terminal unary rule. Endpoint changes use only proved list equalities and
G.reindex. Both operators are actual proofs, not new primitive rule schemas.

The primitive right contraction retains last. BlockedR describes its canonical
inner contraction; sourceRight2/sourceRight3 realize the source's first-retained
order through the existing contractRFirst exchange macro. For example the
nonempty right context [top,top,bot,top] contracts to [top,top,bot] in source
order. The primitive's canonical target orders its fixed gaps before the
retained copy. These are explicit different orderings, not an implicit
strictification or rank-invariance assertion. Right patterns are independently
typed, using conjunction-right/disjunction-right and correct side positions;
no arrow-negation functor is assumed. Administrative exchanges remain visible
syntax nodes and are not erased from rank calculations.

The immediate classifier sees these explicit exchange nodes as exchanges.
No theorem here equates a macro's immediate head profile with its underlying
logical head, or transports all tied-site ranks across the macro. The encoded
blocked patterns and the raw-rule classifier have distinct roles.

## Occurrences and source reducibility

ProofAddress.ProperContains a b requires a nonempty typed suffix address c
with a.append c=b. Its strict path-length inequality, irreflexivity,
transitivity and immediate-descent law compile. The empty suffix cannot make
an occurrence its own proper ancestor. Two identical sibling proof values
retain distinct paths; neither properly contains the other.

traceAt retains an actual proof/address and a selected whole-formula position.
ReducibleL f g a x requires an existing topmost cut, the chosen left
contraction tied in g's right cut-premise, that contraction unblocked, and
every proper containing tied left contraction blocked. ReducibleR is separately
typed for right contractions in the left cut-premise f. TiedRight/TiedLeft
supply both cluster membership and the exact lower-contraction formula.
The ancestor condition concerns the chosen occurrence inside a containing
contraction's premise; it does not require the chosen contraction itself
both blocked and unblocked. No desired reduct or rank conclusion is a field.

Reducible occurrences are cut-free by address descent from the topmost cut.
Two reducible occurrences for the same cut cannot properly contain one
another. Actual signed examples show reducible root contractions on both
sides. A nested contraction is genuinely tied but not reducible when an
unblocked tied contraction properly contains it. These tests rule out vacuous
self-blocking and proof-value-only ancestry.

## Exhaustive selection classification

PortOrigin classifies each actual selected position as fresh (empty
predecessors), first/second (a complete singleton predecessor with premise
branch 0/1), or shared (the selected retained formula of an inner contraction).
The class exists and is unique. G.selectionPort uses permitted Classical.choice;
this is a logical classification, not an executable normalization algorithm.
No decidable equality on P is requested.

The ordered profile is d.selected.map (g.selectionPort side), with a typed
origin proof for every original position. port_member links profile membership
to a selected position and its actual predecessor evidence. Branch labels
refer to actual constructor arguments, independently of mix's context order.
A selected shared port forces contractL/contractR on the selected side.
A second-premise port forces a binary rule. Outside a basis, a fresh position
forces the corresponding thinL/conjL/disjL or thinR/disjR/conjR head.

The seven selection regimes are shared; selectedFirst/selectedSecond/
selectedBoth; and parametricFirst/parametricSecond/parametricBoth. Shared has
explicit priority; otherwise fresh membership separates selected from parametric,
and both branch-membership flags are recorded. Holds conditions are mutually
exclusive and their uniqueness is proved. This does not assert exclusivity
of the seven source blocked descriptions.

The outer bound gives two selected positions with increasing indices.
Every head has at most one fresh position of the same formula, as proved
by leaf_indices; hence, without a shared port, some parametric premise branch
is present. This proves exhaustive regime existence without caller-supplied
coverage. Basis heads cannot supply the two distinct positions. Cut is
excluded using the existing cut_not_cutFree theorem and the actual CutFree
hypothesis. The classifier applies to the original complete selection, not
a deduplicated set of formula labels.

## Finite case ledger and remaining reduction obligations

For left input d,hn,g above, a required new proof has G P K Δ and the same
Reduced denotation as d.applyL hn Δ g; on the right its type is G P Γ K.
Every missing row must construct the new contexts/routes and prove the required
selected/rank conclusions, not simply return the old proof. The following
ledger separates available local theorems from certified global dispatch:

| Actual head / selected regime | Existing typed local result | Exact remaining obligation |
| --- | --- | --- |
| Basis or cut | not_basisL/R and cutFree_not_cut | Excluded by proof at the stated bound/hypothesis. |
| exchangeL/R, parametric | W1.Exchange.denoteL/R; W1.SameSideExchange.interior/terminal_left/right | Opposite-side and fixed-gap/tail local scopes exist. Compute crossing-selected, multi-gap or absorption data when those hypotheses fail, retaining exact K and complete tags. |
| thinL/R, parametric | W1.denoteL/R; W1.SameSideThinning.interior/terminal_left/right | Opposite/fixed scopes exist; derive instance data from the profile. |
| Same-side thinning, selectedFirst | W2.SelectedThinning.terminal_left/right | Other principal placements need explicit exchange/selection transport; derive the same K, predicates and n+1/n progress. |
| Same-side contraction, shared | W3.SharedContraction.fusion_left/right | Extract the shared selected membership/context data to instantiate fusion; transport all tied sites remains unproved. |
| Same-side contraction, parametric | W1.DisjointContraction.fixedGap/terminalTail_left/right | These scopes do not cover arbitrary disjoint interleaving. Construct the missing route/selection square and directed ranks at exact K. |
| Opposite contraction, parametric | W1.Contraction.denote/reverse | Available directed local equations; no globally decreasing two-rank sum. |
| Unary logical, parametric | W1.Logical and W1.SameSideLogical interior/terminal laws | Opposite/fixed local scopes exist; other placements need derived routing. |
| Unary logical, selectedFirst | W4.SelectedLogical.terminal_left/right | Extend beyond terminal scope without ignoring the n=2 endpoint tie or other fixed-rank increases. |
| mix, parametricFirst/Second | W5.SinglePremiseMix.single_premise_left/right; OtherPremiseMix.other_premise_left/right | Local equalities exist. Derive branch-block data and casts from the profile to instantiate them uniformly. |
| mix, parametricBoth | BlockedL/R gammaMix encodes the one-copy-per-premise base pattern | General mixed-premise W5 is unproved. Construct separate inner blocks, treating singleton branches without a contraction node, then a blocked outer two-copy contraction at the exact original K. Prove component equality, all branch fibers and strict ranks for new inner contractions. This is the next checkpoint. |
| conjR/disjL, parametric branches | Source p.252 W5 analogues; blocked gamma patterns encoded | General single/mixed-premise binary logical equations are still unproved; construct exact indexed rules, selections and component squares. |
| conjR/disjL, selected branches | Source W6; two/three-copy blocked principal patterns encoded | General principal-plus-one/both-premise W6 transformations and their rank/control laws remain unproved. |
| Explicit source-order exchanges | disjLLast and contractRFirst/sourceRight2/3 | Raw profiles classify the actual exchange heads. Derive any required macro-level dispatch and rank transport; do not erase these nodes. |

Head restrictions and the seven profile regimes cover every allowed input;
this table is not a theorem that every row already has a reducer. It identifies
missing cases instead of automatically scheduling unrelated local lemmas.
The proved ProofAddress.replace layer can lift an obtained local equality,
but selection of a reduct and control of all affected tied contractions remain
separate. No Reducibility Lemma, Blocked-w, clean-cut normalization, cut
elimination, restricted coherence, PositiveCoherence, faithfulness/Boolean
Coherence or unconditional maximality is supplied. Milestones stay separate.

## Inhabited tests and verification boundary

All fourteen blocked constructors have actual Empty-variable constant examples,
including compound principal formulas and the three-copy pattern. All seven
profile regimes have inhabited examples. The binary mix profile is [second,first],
confirming constructor branch order despite reversed context order. A head
logical profile is [fresh,first,second]. Equal-label fixed/principal tags stay
distinct; signed shared-contraction tests and nested reducible/tied examples
compile. The source right-retention test uses nonempty unequal fixed contexts.
No impossible G [] [] or unwitnessed zero is used.

Baseline main: 6b860df5fdb6e4c1c50dc583e0de0d04c102eb25, matching fetched SSH
origin. Fresh baseline: 208 files / 7,972 declarations, exit 0, 7.612s.
Eight new modules total 924 physical source lines. Old DosenPetric modules
and interfaces are byte-preserved; existing Lean changes only add root imports
and 83 selected theorem axiom prints. Exact public queries cover 123 explicit
declarations and the fourteen blocked constructor types. Lean 4.35.0,
Init-only manifest, manuscript v4/v5/diagrams/references/checksums, AGENTS,
historical reports/prompts and the integration stash remain preserved.

Completed final sequential checks at 2026-10-24T22:45:22.905851+00:00: **216 source files /
8,406 audited project declarations**, an increase of 434 from the baseline.

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 122.936 |
| python3 scripts/check-audit-boundaries.py | 0 | 44.598 |
| python3 scripts/check-presentation-boundaries.py | 0 | 4.891 |
| manuscript SHA256SUMS | 0 | 0.065 |
| git diff --check | 0 | 0.059 |
| git diff --cached --check | 0 | 0.055 |

All five negative controls reject with the expected diagnostics and Lean exit 1;
public import closure passes. All 137 exact public type queries (123 explicit
declarations plus fourteen blocked constructors) pass in 8.203s.
The 83 selected theorem axiom prints supplement the complete transitive audit.
Only propext, Quot.sound and Classical.choice are permitted. Selected outputs,
source/record hashes, all command exits/timings and versions are retained.

An early working-tree import-closure check failed when untracked modules with
overlapping APIs appeared. They were left untouched and excluded from the
frozen staged candidate. An optional fresh isolated rebuild at
/tmp/dp-blocked-candidate-20261024T2228 was interrupted with exit 130 while
compiling unchanged dependencies; it is not counted as a successful check.
Later, no extra Lean files remained and all staged/working proof bytes matched
the frozen candidate. The completed final checks use the original
checkout's existing artifacts from this same project and pinned toolchain.
No validation of the transient separate modules is claimed. Source inventories
and committed-byte comparisons identify the exact checked proof source.

Failed elaborations are retained, including dependent index normalization,
source-order casts, omitted explicit arguments and unavailable non-Init tactics/
helpers replaced with core proofs. No target, source equation, old rank or
heartbeat was weakened. Two failed exploratory builds briefly overlapped;
subsequent builds and the required final candidate checks were sequential.

Reports and evidence are retained under docs/, docs/reviews/ and
provenance/wsl-gentzen-blocked-classification/. The
[hostile review](reviews/GENTZEN_BLOCKED_CLASSIFICATION_HOSTILE.md) and
[writing review](reviews/GENTZEN_BLOCKED_CLASSIFICATION_WRITING.md) are
AI-assisted author-side reviews, not independent certification. Separate receipts
compare checked/committed bytes, SSH refs and conflict-preserving Downloads
copies. Independent source/kernel replay, Challenge/Solution/Comparator,
official preflight/service, fresh manuscript layout/compilation, publication,
licensing and visibility changes did not run.
