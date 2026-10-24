# Gentzen proof-occurrence replacement and W5 integration

## Exact endpoint and hypotheses

A chosen occurrence of a Gentzen proof can be replaced while retaining the
outer sequent and every surrounding constructor and sibling. For arbitrary P,
existing root:G P Γ Δ, g:G P Θ Λ, address a:ProofAddress root g and
h:G P Θ Λ, ProofAddress.replace a h has type G P Γ Δ.
No equality test on proof values, freshness, atomicity, DecidableEq, nonempty-P,
CutFree or Atomized hypothesis is needed to construct it.

If ofTerm h.denote=ofTerm g.denote in the original Reduced category, then
the rebuilt root has the same Reduced denotation as root. The local equality
is a legitimate congruence hypothesis, not a coherence or normalization input.
The W5 applications discharge it with an existing proved transformation.
Complete tagged relation equality follows afterward. Composition is left-first.

## Construction and proof

Premise.rebuild replaces the selected immediate premise of one actual rule.
Its eight unary branches retain all contexts/formulas/contraction bounds;
its eight binary branches retain the other proof exactly. These are the two
branches of each of conjR, disjL, mix and cut. Cut formula parameters are
explicit. The four leaves permit replacement at the root; they have no premise
addresses. No new proof-context grammar or semantic-law record is introduced.

ProofAddress.replace recurses on the existing address. At root it returns h;
at a.down p it replaces the parent's occurrence by p.rebuild h. Dependent
indices give the exact sequent at every step. rebuild_original and
replace_original recover the original parent/root. The inserted proof has a
constructed address in the rebuilt root, with exactly the old branch path.
Replacing that inserted occurrence again equals replacing the original
occurrence directly. Equal proof values in different branches remain distinct.

Address append composes actual occurrences. Both unit laws, associativity,
path concatenation and replace_append are proved. The latter says replacing
at a composed address equals rebuilding the inner replacement and then the
outer one. replace_congr permits comparing any two equal-denotation proofs
plugged at the same address, without requiring either to equal g's denotation.

Single-rule denotation congruence unfolds actual G.denote: unary composition
uses inherited congruence, and binary rules use Rules.conjRight/disjLeft/mix/
cut_congr. Address induction then proves replace_denote. No coherence,
occurrence/inclusion reflection, inverse of a premise or arrow negation is used.

For every replacement, exact additive balances hold in Nat:

```text
(replace a h).cutCount + g.cutCount = root.cutCount + h.cutCount
(replace a h).proofSize + g.proofSize = root.proofSize + h.proofSize.
```

Each surrounding rule contributes its unchanged node and siblings exactly
once. These equalities avoid truncated subtraction and impose no monotonicity
on h. Equal local cut counts imply equal total counts. If both root and h
are CutFree, the rebuilt root is CutFree. If both are Atomized, so is the
rebuilt root; the proof retains thinning's AtomicFormula condition and the
unchanged sibling's predicate. Neither preservation theorem assumes its
conclusion as data. No rank or cluster-transport theorem follows here.

## Existing local rewrites integrated into larger proofs

For both OtherPremiseMix.oldL/newL and oldR/newR, public replacement theorems
now accept any address of old in any existing root. They preserve Reduced
denotation, complete tagged relation and total cutCount. CutFree and Atomized
are preserved whenever the original root has the respective predicate:
descent to old and the existing old/new equivalences supply the new predicate.
These are genuine arbitrary-address applications of the replacement API.

The concrete surrounding proof is

```text
surround A s q = G.mix (G.thinL [] Γ Δ A q) s
    : G P (Θ++A::Γ) (Λ++Δ),  s:G P Θ Λ, q:G P Γ Δ.
```

Its address of q is [0,0]. Replacing q by h gives exactly surround A s h,
so s, A and all endpoints remain unchanged. actual_w5 instantiates q with
the completed other-placement W5 old proof and h with new, using the public
replace_denote theorem. Signed cut premises and an unchanged cut-containing
sibling give an inhabited example with exactly three cuts; actual_w5_count
uses the public integrated count theorem. Separate inhabited examples use
the integrated Atomized and CutFree theorems. empty_w5_right lifts the actual
right dual with Empty variables and constant premises at the same depth.

The eight generic binary reconstruction examples prove both branches of all
four binary rules. identical_siblings replaces either identity in mix(id,id)
by zero and proves the resulting syntactic proofs differ. This tests selection
by occurrence, without asserting identity and zero are categorically equal.
Nested cuts use address [1,0]; insertion of a one-cut proof gives three total
cuts and seven proof nodes. Both literal signs preserve the inserted path.
Empty constants provide an actual cut-free atomized conjR(topI,topI) example,
with empty literal-occurrence sets. No impossible G [] [] is used.

## Source correspondence and gate status

Directly consulted: Došen–Petrić, Proof-Theoretical Coherence, September 2007,
[full PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf), SHA256
e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Printed pp.248–253 are PDF pp.260–265 one-based; rendered p.250/PDF p.262
and the cached six-page text were consulted. No new source discrepancy.

| Source anchor | Typed correspondence | Status |
| --- | --- | --- |
| p.250 Reducibility Lemma's replacement of one subterm | ProofAddress.replace reconstructs the actual surrounding proof at unchanged endpoints. | Replacement prerequisite proved; the lemma's existence/rank conclusion remains open. |
| pp.248–249 proof occurrences and clusters | Existing premise/address branches distinguish repeated equal values and positions. | Original address interfaces preserved; inserted address/path and address composition proved. |
| pp.251–252 W5 single-premise transformations/right analogue | Existing local Reduced equalities now hold when applied at an address inside a larger proof. | Both other-placement duals integrated; concrete nested signed-cut/Empty examples compile. |
| p.250 blocked/reducible definitions; pp.251–253 W1–W6 | Classification must select the appropriate local transformation and control newly reducible tied contractions. | Still open; the next checkpoint targets definitions and exhaustive case dispatch. |

The missing reconstruction layer identified in the preceding audit is now
closed. This is an integration result rather than another isolated rewrite.
It does not close G2: Blocked/Reducible definitions, complete case dispatch,
remaining local transformations and the source tied-site rank argument remain
open. proofSize is a proof-node count, not a claimed elimination measure.
G3 cut elimination, restricted coherence M0–M3, retractions/normal forms R0–R1,
PositiveCoherence, faithfulness/Boolean Coherence and actual maximality remain
open. The positive-coherence-to-faithfulness transfer stays conditional.
The three milestone boundaries are unchanged; counts are not a completion
percentage and no manuscript defect is inferred from unfinished reconstruction.

## Implementation, preservation and verification

Clean main 6bbf0a4143d395fc339972f86f25d3b74203a9b0 matched fetched SSH origin.
Fresh strict baseline: 204 files / 7,859 declarations, exit 0, 5.659s.
Four new modules total 447 source lines: GentzenPremiseReplacement,
GentzenProofReplacement, GentzenReplacementExamples and GentzenRewriteIntegration.
All older DosenPetric modules/interfaces are byte-preserved; existing Lean
changes add only four root imports and 56 selected theorem axiom prints.
Lean 4.35.0, Init-only closure/manifest, AGENTS, manuscript v4/v5, diagrams,
references/checksums, historical reports/prompts, other checkouts and the
integration stash are preserved. No mathematical axiom or equation is added.

Final strict verification: 208 source files / 7,972 audited declarations,
an increase of 113. All 56 new theorems have selected axiom prints, and exact
public types cover all 67 explicit declarations. Complete transitive audit
and public import closure pass. Only propext, Quot.sound and Classical.choice
are permitted; no choice-free claim.

| Command | Exit | Seconds |
| --- | --- | --- |
| bash scripts/verify.sh | 0 | 6.076 |
| python3 scripts/check-audit-boundaries.py | 0 | 9.536 |
| python3 scripts/check-presentation-boundaries.py | 0 | 1.198 |
| manuscript SHA256SUMS | 0 | 0.011 |
| git diff --check | 0 | 0.01 |
| git diff --cached --check | 0 | 0.009 |

Exact types pass in 2.835s; final integration module build passes in 14.500s.
All five negative controls reject with expected diagnostics and Lean exit 1:
direct/private/hidden external axioms, distinct tagged projections identified
by rfl, and a zero without a correctly typed existing-arrow witness. Heavy
checks were sequential after the last proof edit.

Failed elaborations are retained. Dependent reconstruction required curried
replacement arguments, explicit changing sequent indices, explicit cut-formula
parameters and qualified root constructors. Some inferred example arguments
and unfolding steps also needed explicit types. Compiler diagnostics include
placeholders from failed definitions; no source hole was inserted or remains.
No target, source equation, old interface, rank or heartbeat limit was changed.

Evidence is retained under provenance/wsl-gentzen-proof-replacement/ and
matching .codex-work/: baseline/final commands, versions/exits/timings, exact
types/axioms, source/declaration/import closure, controls, failed attempts and
source access. The [hostile review](reviews/GENTZEN_PROOF_REPLACEMENT_HOSTILE.md)
and [writing review](reviews/GENTZEN_PROOF_REPLACEMENT_WRITING.md) inspect the
actual proofs/examples and maps; they are AI-assisted author-side reviews,
not independent certification. Separate receipts verify checked versus committed
bytes, main/origin/main/live SSH refs and conflict-preserving Downloads copies.

Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service, fresh manuscript layout/compilation, publication, licensing
and visibility changes did not run. The [next checkpoint](CODEX_GENTZEN_BLOCKED_CLASSIFICATION.txt)
is source-faithful Blocked/Reducible definitions and a finite classification
linking every allowed case to a proved rewrite or a precise remaining obligation.
