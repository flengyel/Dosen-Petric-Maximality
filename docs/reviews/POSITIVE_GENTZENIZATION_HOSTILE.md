# Positive Gentzenization: hostile-referee review

## (A) Kill-shots / hard blockers

This is an author-side, AI-assisted audit of the actual twenty-one new modules,
their source correspondence, report and scope maps. It is not independent peer
review. No confirmed blocker remains for the exact G0/G1 endpoints.

Anchor: GentzenProofInterfaces.lean, Atomized/Topmost; report “Next concrete
cut-elimination prerequisite”; PositiveFragment.lean, PositiveCoherence.
Claim: representation with cuts is completed, while atomization, cut elimination
and coherence remain open. Failure mode: **unproved** if any of the latter were
promoted. Evidence: **absence_in_text** and **derivation**—cutCount/CutFree are
analysis definitions, the new theorem supplies no CutFree field, and the earlier
faithfulness transfer still requires an explicit coherence premise. Severity:
fatal for a promoted coherence/elimination/maximality claim, not for the scoped
checkpoint. Repair: prove the displayed Atomic-k target and subsequent inputs.

## (B) Major weaknesses

A source-correspondence risk was found and corrected before the final strict
run. Anchor: rendered source §11.1 p.240 e'-conjunction; ReducedWitnesses.lean
mixedConj; GentzenRules.lean sourceConj; GentzenDisjunction.lean disjInput_out.
The old witness helper had the right mixed type, but no theorem identified
it with the displayed source arrow. Failure mode if silently identified:
**unproved** / **misuse_of_prior_work**. Evidence: **absence_in_text** in the
old witness correspondence and **citation** to the rendered source. Severity:
major, repairable. Applied repair: use the actual p.240 composite as the
separate sourceConj definition and prove its needed unit calculation. The old
helper remains unchanged; no equality with it or source erratum is claimed.
The disjunctive source expansion is separately proved by category/tensor laws.

| Anchor / claim | Typed proof or boundary check | Evidence / result |
| --- | --- | --- |
| PositiveGentzenSyntax, all 16 schemas | Constructor arguments are normal forms, contexts, subproofs and contraction length proofs; none embeds Term or Positive. Atomic id/zero and two constants are the only leaves. | structural_argument; no disguised raw grammar. |
| GentzenContexts, Iso/append/exchange | Actual raw arrows, positive membership and both inverse laws; fold_as_foldr and explicit list-index transports. | derivation; no assumed strictification or formula unital equality. |
| GentzenRouting, copies and full contractions | here/there positions distinguish selected copies from equal formulas in fixed gaps. n≥2; source first-right-copy and rightmost thinning are explicit derived operations. | derivation; full source operations are present, not an unproved adjacent-rule completeness claim. |
| GentzenRules cut; Derived cutAt | Head positions are distinguished; full source gaps are moved by explicit block exchange. comp executes its first argument first. Every intermediate mixed d endpoint is typed. | derivation, citation p.241; no same-connective medial substitution. |
| GentzenUnitLaws and Disjunction | Empty residual composition uses actual dist_top and units. Empty mixed cases have proved singleton-coordinate formulas. | derivation; no declaration of a unit-specialized composite as identity. |
| DiagonalData associator formulas; StructuralRepresentation | Specific component formulas and actual unit laws replace earlier associative/symmetric coherence appeals. | derivation; no positive/Boolean faithfulness premise. |
| positive_represented | Exhaustive induction has exactly the 19 Positive cases; mix/dist/zero have independent constructive witness proofs. | derivation and retained coverage inventory; no omitted primitive. |
| Gentzenization and occurrences | Both unit equations compile; tagged inverse coordinates plus the direct encode relation give exact correspondence. | derivation; equality is interpreted forward, never reflected from relations. |

## (C) Minor issues

The report defines decoded representation before its constructor-closure
argument and states both singleton unit maps in the endpoint. It distinguishes
raw denotation, its Reduced.Hom class and an existential proof witness.
The type G is not called a quotient category or a faithful interpretation.

The two empty contexts are written as top and bot folds, not as one common ∅.
The source's differently ordered ∨L premises and right contraction are matched
by explicit comparison formulas. Source block names label positions rather
than a search for every formula with the same printed name.

## (D) Cross-section consistency failures

No remaining mismatch was found between the exact endpoint, coverage table,
source map and compiled construction. G.identityNF/zeroNF recurse from atomic
signed leaves and constant bases. Compound zero witnesses use the proved
two-zero tensor law; no arbitrary endpoint zero or compound G zero leaf occurs.

G.no_empty gives an actual contradiction from G P [] [] via the established
full-presentation Hom(top,bot) impossibility, without faithfulness. That
selected boundary proof uses permitted Classical.choice inherited from the
existing consistency argument. The principal representation and occurrence
results print only propext/Quot.sound. Both facts are reported accurately.

Repeated equal literals in a context have different here/there paths and
internal Sum tags. Empty unit occurrence branches are eliminated, not populated
with a dummy value. No Nonempty/DecidableEq/finiteness/freshness premise enters.
Object duality and categorical opposite are not used as a contravariant arrow
negation operation. No claim realizes all signed-label-respecting relations.

The existing 21 raw, 61 equation and 19 positive schemas, old Lean modules,
reports and manuscript v4 are unchanged. PositiveCoherence and the existing
faithfulness transfers retain their prior scope. Representation witnesses may
contain cuts even for structural arrows; no unsupported cut-free claim is made.

## (E) Acceptance conditions, non-negotiable

1. Genuine positional syntax with all four logical families and no raw embedding:
   met by G's sixteen schemas and constructor inventory.
2. Correct constant bases and no empty-sequent leaf: met by topI/botE and no_empty.
3. Positive typed denotation with actual structural comparisons/inverses:
   met by denote_positive, Iso and the explicit unital calculations.
4. Source mixed composites and contextual cut order: met by sourceConj,
   sourceDisj_expansion, cutAt_denote and all rule denotation equations.
5. Full source contraction/exchange operations with denotation laws:
   met by positional copies/routing and contractRFirst/thinLast/cutAt formulas.
6. Exact G1 equation and decoded counterpart covering every Positive constructor:
   met by the compiled induction and both Gentzenization theorems.
7. Nontrivial tagged occurrence compatibility without faithfulness:
   met by gentzenization_occurrences and inverse singleton coordinates.
8. Cut visibility and honest open proof boundaries:
   met by cutCount/CutFree/Atomized/Topmost and the open Atomic-k target.
9. Actual verification/source closure and historical preservation evidence:
   met by 70 files, 3448 audited declarations, five rejected controls and hashes.

Failure of 1–7 or 9 would require withdrawing the corresponding G0/G1 claim.
Failure of 8 would withdraw a promoted elimination/coherence claim.

## (F) Not checked / uncertainty log

No independent kernel replay, independent full source-transcription review,
Challenge/Solution comparison, Comparator, official preflight/service check,
novelty survey, manuscript recompilation or whole-paper layout review ran.
The future Atomic-k, blocked-contraction and cut-elimination cases were not
proved here. The author-side source audit does not certify the entire book.

Strongest confirmed remaining blocker: the displayed Atomic-k theorem and
later elimination/restricted-coherence inputs for faithfulness. Strongest
suspected unconfirmed blocker for this checkpoint: none identified. Most
important unchecked item: independent source/kernel audit. Recommendation
does not depend on unavailable review material. Final recommendation:
**unknown** as independent certification; the scoped G0/G1 endpoint passes
this author-side audit, with cut elimination and coherence open.
