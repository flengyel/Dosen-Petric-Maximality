# Author-side hostile review — binary-input Reducibility integration

This is an author-side simulation of a hostile referee, not independent peer
review or external certification. Scope: the new production proofs, exported
signatures, integration report and current correspondence/coverage records.
Genre: formalization checkpoint. Axes: correctness, exact scope and
reproducibility. The manuscript is unchanged and is not being refereed here.

## (A) Kill-shots / hard blockers

**The requested complete Reducibility result is still unproved.** Anchor:
`docs/GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md:223` and `DosenPetric/GentzenReductionStatements.lean:13`. The first states that both full targets remain open;
the latter defines the target quantifier but supplies no witness. The actual
assembled producer at `DosenPetric/GentzenBinaryInputReducers.lean:54` (and `DosenPetric/GentzenBinaryInputReducers.lean:72`) retains `t.ruleKind.Binary`.
Failure mode: **unproved** for completion of the governing task; severity:
central task-acceptance blocker, repairable by the missing constructions.
Evidence: **absence_in_text + structural_argument**. Case analysis in the
binary producer explicitly covers conjR/disjL/mix/cut and excludes cut through
cutCount. It has no branch supplying a reduct for arbitrary unary input.
The report correctly declines to claim a full producer; this is not a false
mathematical theorem or a counterexample to the published Reducibility Lemma.

Downstream impact: outside-site transport, multiset descent and Blocked-w
cannot be represented as completed corollaries. No compiled binary-only result
repairs that gap by changing its name or dropping the Binary hypothesis.

## (B) Major weaknesses

1. **Arbitrary unary selection transport is missing.** Anchors: report §7,
   `DosenPetric/GentzenSelectionSplit.lean:26` and the existing GapExchange.Data hypotheses. Failure mode:
   **unproved / unsupported_generalization** if fixed-gap statements are
   promoted to arbitrary exchange. Evidence: **structural_argument**.
   A swap can interchange selected sublists; selected indices are not globally
   monotone under it. Internal Split identifies actual lower contexts for an
   append, but it does not prove the required lower-context permutation for a
   swap crossing selected positions. A product/coproduct component square and
   complete descendant bound must be constructed. Severity: major; repairable.
   The report states the exact unrestricted left/right types and does not
   install them as axioms or conditional substitutes.

2. **Further full-dispatch and outside-site obligations remain.** Anchor:
   report §7 dependency table. Failure mode: **unproved**. Evidence:
   **absence_in_text**, corroborated by the limited theorem types. Existing
   local W1, W2 and W3 results do not alone supply a dispatcher for every
   unary input/selection placement. Nor does a bound on descendants inside
   a replacement prove transport of all containing/outside reducible sites.
   Severity: major for the full task; repairable. No global multiset-decrease
   or cut-elimination conclusion is accepted.

3. **Verification is local, not independent certification.** Anchor: report
   §5 and the retained receipts. Failure mode: **unknown** for an independent
   clean build, external kernel replay or Palomar service acceptance.
   Evidence: **absence_in_text** and explicit unperformed-check log.
   The actual successful strict build and dependency audit support the checked
   local statements. They do not support unperformed external statuses.
   Severity: a scope limitation; not a mathematical refutation.

## (C) Minor issues

- The old phrase about a two-copy right-W4 case could obscure the smallest
  missing case. The production comment and current records now say two
  parametric copies **plus** the fresh compound. The new singleton case is
  separate and its exact formula is anchored at `DosenPetric/GentzenNonemptyRightRanks.lean:36`. This is a resolved
  exposition issue, not evidence against the earlier correctly typed theorem.
- The implementation adds 81 modules. The module and named-declaration
  inventories are needed to make the proof dependencies navigable. Declaration
  counts include generated helpers and are not treated as a theorem count.
- An interrupted exploratory run has no saved elapsed-time receipt. The
  dedicated interruption note retains its log and exit 130 and labels the
  elapsed time as uncaptured; no timing has been fabricated.

## (D) Cross-section consistency failures and checks

The obsolete current continuation pointed to the 05c6bc8 prompt. It is now
archived; current records name the exact supplied 1e967bc instruction. Older
reports and source-access history remain. The following claim-bearing checks
were applied to the actual code:

| Question | Evidence and outcome |
| --- | --- |
| Actual inputs or caller-chosen selection? | `MixReducer`, `ConjunctionReducer`, `DisjunctionReducer` construct selection/block/arity/retained-position/old-proof comparisons internally; `DosenPetric/GentzenSelectionSplit.lean:26` and `DosenPetric/GentzenHeadSelectionSplit.lean:27` jointly track indexed endpoints. No caller decomposition premise. |
| Empty branch or discarded copy? | Split has one-branch and both-branch cases; HeadSplit has unselected/selected head regimes. OnlyFresh is arity one and contradicts outer arity two. Ordered selections retain all multiplicities. |
| Independent arities? | Source/native rank bounds use p.arity and q.arity independently, each positive; no equality of counts. Singleton operations are node-free. |
| Native versus source blockedness? | `DosenPetric/GentzenSourceOneSingletons.lean:43` and its second-premise analogue identify actual terminal-source patterns. Native disjL repairs build blocked source bodies and explicit exits; `DosenPetric/GentzenNativeLogicalBounds.lean:69` proves their bounds. No blockedness is transported along mere Reduced equality. |
| Right W4 smallest case? | `SingletonRightRegression.old_reducible` is an inhabited Empty-variable example with some 1 prefix. `NonemptyRight.old_rank` is S+n+2; at n=1 the old rank is S+3 and the inner rank S. |
| Every eligible descendant? | ReducesL/R retain the full address/position/post-replacement quantifier. ContractionBound skips actual blocked nodes and bounds surviving parametric frontiers. Entry uniqueness is proved, not assumed globally injective. |
| Categorical variance? | Product arrows precompose; coproduct arrows postcompose. Component calculations and actual sourceConj/mixedDisj naturality supply the logical squares. No contravariant arrow-negation operation is used. |
| Circular coherence? | No coherence premise, occurrence-equality reflection or full-inclusion reflection occurs in the new producers. Interpretation equality is downstream of Reduced denotation equality. |
| Public/private dependency boundary? | The separate public importer succeeded. The complete audit passed 9,737 declarations with only propext/Quot.sound/Classical.choice; all five negative controls rejected. |
| Rank descent or quotient invariance overstated? | The records distinguish syntactic cluster rank from cutCount/proof size and describe only proved descendant bounds. No global rank sum or quotient invariance is claimed. |

No source or writing review is evidence of faithfulness. Empty hom-sets and
witnessed zeros are preserved by the unchanged presentations. Whole-formula
positions, including constants, are not confused with empty literal-occurrence
types.

## (E) Acceptance conditions, non-negotiable

For accepting the **original full task**, not merely these checked partial results:

1. Compile both full Reduces producers without the Binary restriction or any
   substitute caller-supplied rank, reduct, selection or coherence hypothesis.
2. Construct the unrestricted unary exchange factorization in report §7 and
   its separately typed dual, with repeated-label positional tests and complete
   descendant bounds. Failure leaves the full task rejected.
3. Close every remaining unary placement/selection branch or exhibit a checked
   blockedness contradiction. A classifier alone is insufficient.
4. Prove outside-occurrence and containing-blocked-contraction transport before
   applying finite multiset descent to conclude Blocked-w.
5. Retain the exact permitted-axiom/dependency boundaries, five negative
   controls, checked-versus-committed inventory and non-force ref agreement.
6. Keep coherence, unconditional maximality and external service/publication
   statuses separate until their actual constructions or actions are complete.

The compiled binary producers and scoped W4/source exclusions can be retained
as proved without claiming acceptance of these unmet full-task conditions.

## (F) Not checked / uncertainty log

This is not a full manuscript review. No novelty claim, independent clean
kernel build, official comparator/preflight/service status, global unary
algorithm, Blocked-w proof or coherence proof is certified. Manuscript bytes
are preserved and checksum-checked; their full mathematical correctness is not
inferred from this Lean integration. Historical inaccessible-source records
were not rewritten. Current pinned PDF and writing-cache access succeeded.

Strongest confirmed blocker: the missing unrestricted unary producer and hence
both full Reducibility Lemmata. Strongest suspected unconfirmed blocker:
additional administrative exchanges may invalidate a proposed root-rank bound
in a future unary repair; no such unproved bound is accepted here. Most
important unchecked endpoint: outside-site reducibility transport and the
multiset induction. The rejection of full completion does not depend on
unavailable material. **Final recommendation: reject the claim that the full
governing task is complete; retain only the compiled scoped results.**
