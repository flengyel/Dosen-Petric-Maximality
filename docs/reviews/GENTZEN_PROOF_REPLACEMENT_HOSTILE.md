# Author-side hostile review: Gentzen proof replacement

## (A) Kill-shots / hard blockers

This AI-assisted author-side audit examines all four new modules, exact public
types/proofs/examples, report and current correspondence/coverage. It is not
independent peer review or certification. No fatal blocker was established
for the typed reconstruction and W5 integration claims.

| Anchor / claim | Failure mode / evidence | Finding |
| --- | --- | --- |
| Premise.rebuild and ProofAddress.replace; report “Exact endpoint” | ill_typed, unproved / derivation | Existing root:G P Γ Δ, g:G P Θ Λ, a:ProofAddress root g and h:G P Θ Λ produce G P Γ Δ. Actual rule parameters, contraction bounds and siblings are reconstructed. No conclusion-equivalent field or new semantic context type. |
| Premise.rebuild branches; report “Construction and proof” | inconsistent_use, false / derivation | Eight unary cases and both branches of four binary rules cover every premise constructor; four leaves have no premise addresses. Actual mix order and cut formulas are retained. |
| rebuild_original, replace_original, inserted_path, replace_inserted | false, ambiguous / derivation and toy_test | Original input recovers root; inserted occurrence has the same path; second replacement changes only the same occurrence. Identical siblings are independently replaceable, with syntactically distinct resulting proofs. |
| append units/assoc/path; replace_append | ill_typed, inconsistent_use / derivation | Address composition has exact indexed endpoints; path order is outer then inner; nested reconstruction equals replacement at the composed address. |
| rebuild_denote, replace_denote/congr/relation | misuse_of_prior_work, unproved / derivation | Actual unary composition and all four binary congruences prove Reduced equality. Local equality is an explicit congruence hypothesis, discharged by W5's proved equation in applications. No coherence, relation/inclusion reflection or inverse arrow. |

No counterexample to the final scoped endpoint or reconstruction laws was found.

## (B) Major weaknesses

1. Anchor: report “Source correspondence and gate status”, “does not close
   G2”; p.250 Reducibility Lemma versus replace_denote. Failure modes
   unsupported_generalization and missing_definition; evidence citation and
   structural_argument. This operation reconstructs a given local replacement.
   It does not select a reduct, prove Blocked/Reducible classification or
   control the ranks of all affected tied contractions. Those remain confirmed
   blockers to global Reducibility/cut elimination. Current maps and next
   prompt preserve that boundary; no local-scope defect was established.
2. Anchor: replace_denote's hypothesis “ofTerm h.denote=ofTerm g.denote”
   and OtherPremiseMix.replace_denoteL/R. Failure mode unproved; evidence
   derivation. Congruence needs this local equality. It is not a restatement
   of the outer conclusion, and the W5 instances supply it from prior
   denoteL/R proofs. actual_w5 and empty_w5_right instantiate the public
   replacement theorem beneath a two-level proof with an unchanged sibling.
   No circular coherence or normal-form assumption was found.
3. Anchor: replace_cutCount/proofSize and report additive balances.
   Failure mode false; evidence derivation and toy_test. Exactly one hole is
   replaced; every unchanged sibling contributes once. Nat addition balances
   avoid subtraction. Equal local cut counts imply equal total counts, but
   arbitrary insertion can increase counts/size: the nested-cut example has
   three cuts/seven nodes. Neither balance is a global termination claim.
4. Anchor: replace_atomized, rebuild_atomized, integrated W5 predicate laws.
   Failure modes unused_hypothesis and unproved; evidence derivation.
   Original-root Atomized supplies unchanged siblings and thinning atomicity;
   replacement Atomized supplies the hole. CutFree follows from the count
   balance and both predicate hypotheses. W5 old/new equivalences supply
   its replacement predicates. No missing freshness/atomicity/nonempty-P
   premise was found; arbitrary compound formulas and cuts remain permitted.

No unresolved major defect was established in the stated checkpoint.

## (C) Minor issues

Anchor: retained failed elaborations. Failure mode ill_typed; evidence
compiler diagnostics and final builds. Dependent matches required curried
replacement arguments, explicit changing endpoint indices and cut formulas;
a variable shadowed the root constructor, and some example inference/unfolding
steps needed explicit arguments. These repairs preserve all target statements.
Compiler placeholders occur in failed diagnostics, not as source proof holes.
No heartbeat, old equation, rank or predicate was changed.

Anchor: current records' older “all-site replacement” wording. Failure mode
ambiguous; evidence absence_in_text and structural_argument. Mechanical
reconstruction is now proved; global all-site rank control is not. Current
maps distinguish those claims and mark the preceding audit as historical.
The actual earlier report/prompt files remain byte-preserved.

## (D) Cross-section consistency failures

No remaining inconsistency was established between actual proof types,
report, current maps and next continuation. The endpoint is reconstruction
plus W5 integration, not a new W5 family or a global reduction procedure.
The seven blocked source patterns and right analogues remain next; the
future ancestor condition must distinguish the chosen occurrence from proper
containing contractions. That is a next-task condition, not a proved result.

The eight generic binary examples cover both branches of mix/cut/conjR/disjL.
Actual repeated equal proofs, both signed literals, Empty constants and
cut-containing W5/sibling examples compile. Full relation equality is a
consequence of original Reduced equality. Empty hom-sets and witnessed zeros
remain intact. The two-object one-arrow check supplies no reverse arrow:
replacement stays within one existing hom-set and uses only inherited rule
congruence, without a category equivalence or new coherence assertion.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding scoped completion claim:

1. Typed exact-sequent replacement at one selected address, covering all
   genuine rule/premise cases and preserving siblings/parameters: met.
2. Original-hole recovery, inserted address/path and repeated replacement: met.
3. Address units/associativity/path law and composed replacement law: met.
4. Derived Reduced congruence and full tagged-relation consequence: met.
5. Exact additive cutCount/proofSize balances and predicate preservation: met.
6. Existing W5 duals lifted at arbitrary addresses, with actual nontrivial
   nested signed-cut/Empty tests and unchanged siblings: met.
7. Frozen old interfaces, 208 sources / 7,972 audited declarations, 56 selected
   theorem axiom prints, 67 exact public types and five control rejections: met.
8. Scoped reports/evidence and next classification checkpoint: prepared;
   committed-source/ref and Downloads receipts record final procedural completion.

## (F) Not checked / uncertainty log

Pinned source pp.248–253 and rendered p.250/PDF p.262 were consulted. Full
local audit/import closure, exact types/axioms, all checks and failed attempts
are retained under provenance/wsl-gentzen-proof-replacement/. Only propext,
Quot.sound and Classical.choice are permitted; no choice-free claim.
Independent source/kernel replay, Challenge/Solution/Comparator, official
preflight/service, fresh manuscript compilation, independent peer review and
novelty assessment did not run. No unavailable review is reported done.

Strongest confirmed blocker: source classification and the global tied-site
rank argument remain absent; they block G2, not reconstruction/W5 integration.
Strongest suspected unconfirmed blocker: none established within local scope.
Most important unchecked item: source-faithful global reduction/termination,
plus independent source/kernel validation.
Dependence on unavailable material: none for this author-side audit.
Final recommendation: unknown for independent certification; the scoped
construction and local verification conditions above are met.
