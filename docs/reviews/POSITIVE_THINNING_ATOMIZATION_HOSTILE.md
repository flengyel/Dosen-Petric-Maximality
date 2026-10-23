# Author-side hostile review: positive thinning atomization

## (A) Kill-shots / hard blockers

Scope: the actual Atomic-k construction, nineteen new Lean modules, the
report and updated source correspondence. This is an AI-assisted author-side
audit of the author's work, not independent peer review or certification.
Equality is the existing reduced generated-equation quotient; composition is
execution order. No fatal blocker was confirmed for the stated Atomic-k endpoint.

The following potentially fatal inferences were checked against actual code,
rather than accepted from prose:

| Anchor / claim | Failure mode tested / evidence | Finding and downstream scope |
| --- | --- | --- |
| PositiveThinningAtomization: atomization, atomize_denote | unproved; derivation by all sixteen G cases and strict compilation | The exact existential, unchanged endpoints and quotient denotation equality compile without a representation premise. No blocker confirmed. |
| GentzenMixedThinning: sourceConj_fst; GentzenMixedInjections: mixedDisj_inr | misuse_of_prior_work / unproved; structural_argument | Actual sourceConj and actual mixedDisj are used. Their sufficient projection/injection equations are derived from existing laws and constant specializations; no coherence input or new equation. |
| GentzenBlockContraction: duplicate; GentzenBlockComparisons: dupContext_arrow/dupTail_arrow | false / ambiguous; derivation | The block recursion contracts every selected position. Exact index lookup and component universal properties prove the complete fold comparison, including empty blocks and fixed tail. Equal labels are not deduplicated. |
| GentzenHeadAtomization: headThinL/R_cutFree | unproved; structural_argument and checked recursion | Helpers contain no cuts and preserve CutFree. The two branching cases combine cut-free premises and unary rewiring only. No generic Gentzenization witness is substituted. |
| PositiveThinningAtomization: atomize_relation | inconsistent_use; derivation | Relation equality follows from proved syntactic equality by occurrenceMap congruence. It is never used backwards to establish arrow equality. |

No new counterexample is claimed. The evidence is the typed derivations and
actual build, not a relational toy test. Atomic-k does not close the still-open
central coherence or cut-elimination claims; treating it as such would be a
fatal unsupported_generalization, and the current records explicitly avoid it.

## (B) Major weaknesses

No unresolved major defect was found in the scoped theorem. Three boundaries
need to remain visible in all uses:

1. **Projected laws versus full mixed schemas.** Anchor: report, “Categorical
   calculations before proof transformation”; correspondence, Atomic-k table.
   Failure mode tested: unsupported_generalization. Evidence: structural_argument,
   exact theorem types. sourceConj_fst discards principal outputs, while the
   full source (m e∧) retains more information; the dual is likewise an injected
   consequence. Reporting the full schemas as proved would overstate the result.
   Status: narrowed wording applied in both records; no new equation. Repairable
   documentation risk, not a remaining theorem hypothesis.
2. **Use of zero-derived uniqueness.** Anchor: top_inr_codiag and
   fromBotPair_unique, followed by the mixed-law proofs. Failure mode tested:
   misuse_of_prior_work. Evidence: derivation through existing fromTop_unique,
   toBot_unique and coproduct/product laws. These are reduced theorems, not
   full-Presentation reflection. The report states the dependency on zero laws;
   it does not assert a proof for a zero-free category. No unresolved gap.
3. **Duplication and measures.** Anchor: headThinL disj / headThinR conj;
   report, formula recursion and remaining obligations. Failure mode tested:
   false. Evidence: structural_argument: each branch contains a copy of f.
   Rewire count preservation concerns only its unary scripts. No theorem bounds
   atomization's global cut count or size. Cut-freeness, which is the requested
   invariant, is proved directly. A future decreasing-rank argument is open.

## (C) Minor issues

Anchor: correspondence entry for mixedDisj and report's dual calculation.
Failure mode tested: ambiguous. Evidence: exact type. The helper arguments
interleave A,X,B,Y whereas the source display groups principal/residual
variables differently. Applied repair: both the argument order and the
intermediate object `(A∨X)∧(B∨Y)` are displayed. No mathematical change.

Anchor: report's verification section. Failure mode tested: irreproducible.
Evidence: actual logs/manifests. Source-level declaration entries (177) and
audited environment declarations (3,990) have different meanings. Applied
repair: explicitly distinguish them and retain both inventories.

## (D) Cross-section consistency failures

The continuation and coverage records previously named Atomic-k as the next
open task. They now identify it as proved and retain the rest of G2 as open.
The statement map names the exact theorem and its CutFree/occurrence variants.
The source map distinguishes the full omitted equations from the sufficient
consequences actually proved. Historical reports/access records are unchanged.
No remaining status conflict was identified in the updated current sections.

The raw grammar, 61 reduced equation schemas, Positive and sixteen G schemas,
AtomicFormula, Atomized and CutFree are byte-identical to baseline. Rewire is a
derived unary script, not an added G constructor or a disguised raw-term leaf.
Its categorical opposite calculation supplies no arrow-negation operation.
The constant basis terms stay differently coloured. Atomic thinnings by bot
on the left/top on the right remain actual thinning operations. The empty
sequent boundary and witnessed-zero policy remain intact.

## (E) Acceptance conditions, non-negotiable

For this scoped checkpoint, failure of any condition rejects its completion claim:

1. Exact atomization and cut-free existential endpoints compile: **met**.
2. Both positional helpers preserve Atomized/CutFree and actual thinning
   denotation at arbitrary gaps: **met**.
3. All four compound cases, both constant cases and sixteen proof schemas
   are covered: **met**, explicit tables and exhaustive Lean definitions.
4. Actual source-defined mixed arrows have sufficient proved laws inside
   Reduced.Hom: **met**; complete omitted schemas are not claimed.
5. Both duplicated context blocks are contracted with positional proofs:
   **met**, duplicate_index and dupContext/dupTail comparisons.
6. Complete relation equality follows from denotation equality with unchanged
   endpoints, including empty cases: **met**.
7. Strict build and transitive audit accept only permitted axioms, and all
   five negative controls reject: **met**, 89 sources / 3,990 declarations.
8. No manuscript, grammar, equation or analysis-interface weakening; no
   unsupported coherence/cut-elimination promotion: **met**.

Commit, live remote agreement and delivery are checked separately after the
reports are finalized; their receipts are runtime records, not proof hypotheses.

## (F) Not checked / uncertainty log

Strict verification, both boundary scripts, manuscript hashes and whitespace
all exited 0. The principal results print propext, Quot.sound and
Classical.choice; choice is permitted and no choice-free assertion is made.
Evidence is in `provenance/wsl-positive-thinning-atomization/`, with complete
commands, fixture/source hashes and declared-source anchors. The author-side
review inspected the actual new argument and source correspondence, including
rendered printed pp.247 and 271 of the verified September 2007 PDF.

No independent kernel replay, exhaustive independent source-to-Lean audit,
Challenge/Solution comparison, Comparator, official preflight/service review,
manuscript recompilation/layout review or novelty certification ran. The
reviews make no acceptance claim for PositiveCoherence or Boolean Coherence.
The governing writing source is available; its distinct review is linked from
the main report. Nothing here depends on an inaccessible mathematical premise.

Strongest confirmed blocker: none for Atomic-k; the next larger G2 claim lacks
typed ancestor clusters/rank and the blocked-contraction reduction arguments.
Strongest suspected unconfirmed blocker: none established in the scoped proof.
Most important unchecked item: independent kernel/source validation of the
full formalization. Dependence on unavailable material: none for the scoped
author-side conclusion. Final recommendation: **unknown** for independent
certification; the verified author-side Atomic-k checkpoint meets the stated
conditions, without establishing cut elimination or coherence.
