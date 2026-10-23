# Author-side hostile review: W1 opposite-side exchange

## (A) Kill-shots / hard blockers

Scope: four new Lean modules, their exact public statements, the full exchange
report, source correspondence and current status/README changes. This is an
AI-assisted author-side audit, not independent peer review or certification.
No fatal blocker was confirmed for the two stated local exchange instances.

| Anchor / claim | Failure mode tested; evidence | Finding / downstream scope |
| --- | --- | --- |
| GentzenExchangeCommutation denoteL/R | ill_typed, unproved; derivation | Actual G.exchangeR denotes postcomposition with .disj toTerm; actual G.exchangeL precomposes .conj invTerm. The four endpoints in each report path match. Existing Laws.assoc proves equality in opposite directions. No coherence input. |
| GentzenOppositeExchangeRank predecessors_exchangeR_left/exchangeL_right | false, ambiguous; derivation | Unchanged-side parent is identity on the exact typed position, so inverse fiber is precisely a singleton. Every position, not every matching label, is preserved. |
| Same module rho_exchangeR_left/exchangeL_right; Examples empty_exchange* | inconsistent_use, unsupported_generalization; structural_argument | An explicit exchange contributes one proof node even for two empty blocks. Rank is computed from predecessors, never simplified using identity denotation. |
| GentzenExchangeCommutationRank contraction_lossL/R and endpoint_lossL/R | false, unproved; derivation | Complete selectedCopies maps and their length give loss n at the contraction; a new exchange root leaves loss n−1 at the whole endpoint. Both strict inequalities use hn ≥ 2. Fixed equal formulas in gaps remain distinct. |
| Commutation atomizedL/R, cutFreeL/R, cutCountL/R | unused_hypothesis, unproved; exact definitions | Both atomization predicates reduce to f.Atomized with no atomicity condition; counts reduce to f.cutCount. No cut-freeness premise enters denotation/rank results. |
| Commutation relationL/R | misuse_of_prior_work; derivation | congrArg occurrenceMap applies only after the Reduced equality is proved. No interpretation/inclusion reflection or conditional faithfulness theorem is used. |

No counterexample is asserted. W1's source appeal to Semilattice Coherence
is replaced only for these two instances by actual associativity proofs.

## (B) Major weaknesses

No unresolved major defect was found within scope. Two broader claims were
tested and explicitly excluded:

1. Anchor: report “Exact predecessors and ranks”. Failure mode
   unsupported_generalization; evidence structural_argument. Local loss at
   the displayed contraction/endpoint says nothing yet about all tied sites
   under replacement at an arbitrary proof address. The report keeps typed
   proof replacement and all-site decrease open. No hypothesis restates these
   desired later results.
2. Anchor: report preservation and Examples repeated_with_cutL/R. Failure mode
   inconsistent_use; evidence derivation. The premise actually has cutCount 1;
   it is not a cut-free toy proof or an uninhabited assumption. Exact unary
   count preservation is not generalized to Atomic-k or branching rules.

These are preserved scope boundaries rather than defects of the local result.
No result is reported as the full W1 family or Reducibility Lemma.

## (C) Minor issues

Anchor: first exploratory log, one_empty_blockR. Failure mode ill_typed;
evidence compiler diagnostic. The originally shortened context X++Θ was not
definitionally X++[]++Θ. Applied repair: retain the constructor's actual list
expression; no strictification equation added. Both attempts and their exact
exit codes/timings are retained. The repaired example and required checks pass.

Anchor: README opening/current-review links. Failure mode inconsistent_use;
evidence prior README at baseline. The count 645 and “presentation bridge
remains open” description were obsolete. Applied repair: describe constructed
presentation/reduction bridges, link maintained validation for counts, identify
current author-side exchange reviews, preserve historical links. Setup now
uses Git over SSH in README and WSL2_SETUP. No history was rewritten.

## (D) Cross-section consistency failures

All current maps identify thinning and exchange instances as completed, with
general W1, W2–W6, blocked transformations, Reducibility, cut elimination and
coherence open. The typed next task concerns opposite-side contractions.
README distinguishes the generated structural model from the actual source
presentation and distinguishes constructed bridges from unproved faithfulness.
The three milestone gates remain separate.

All pre-existing DosenPetric modules, syntax/equations/Positive, G constructors,
proof predicates, predecessor and rank definitions are byte-identical. No
arbitrary zero, new equation, new Gentzen constructor, coherence assumption,
arrow negation or equality reflection enters production proofs. The premise
and all context blocks are arbitrary; no variable inhabitant or DecidableEq
is required. Equal literals keep different tags; constants with Empty P use
actual inhabited G types. Manuscript and historical access/review records are
unchanged. No unresolved status conflict was found in current records.

## (E) Acceptance conditions, non-negotiable

Failure rejects the corresponding scoped completion claim:

1. Both exact old/inner/new endpoint types and unconditional Reduced denotation
   equalities compile: **met**, W1.Exchange namespace preserves thinning API.
2. Computed predecessor lists are exact singletons at the same At, and rank
   adds one including empty blocks: **met**.
3. Every selected copy contributes, with contraction loss n and whole endpoint
   loss n−1; both strict inequalities compile: **met**.
4. Exact cutCount, CutFree/Atomized equivalences without new atomicity, and
   complete tagged relation equality follow in the correct direction: **met**.
5. Two/three copies, fixed equal gap, repeated nonempty blocks, one/both empty
   blocks, Empty P constants and both signs with actual cuts are checked: **met**.
6. Frozen interfaces, manuscript, pinned toolchain and dependency policy are
   preserved; no general W1/coherence promotion: **met**.
7. Required sequential checks pass with five expected negative rejections and
   retained failed attempt: **met**, 113 sources / 4,850 audited declarations.
8. Current README/maps, three reports and exact inventories are retained:
   **met**. Commit/ref and Downloads checks have separate runtime receipts.

## (F) Not checked / uncertainty log

Baseline, exploratory and final required commands have retained logs, exit
codes, elapsed times and hashes in provenance/wsl-gentzen-w1-exchange/.
Only propext, Quot.sound and Classical.choice are permitted; 35 selected
prints are retained verbatim. No choice-free claim is made. The pinned source
and rendered p.251 were directly consulted; the writing source is available.

No independent kernel replay, exhaustive independent source-to-Lean audit,
Challenge/Solution or Comparator, official preflight/service acceptance,
new manuscript compilation/layout review, independent peer review or novelty
assessment ran. These omissions are validation limits, not evidence that
an unformalized published theorem is defective.

Strongest confirmed blocker: none for the two local exchange instances;
full Reducibility still needs other rewrites and all-site replacement control.
Strongest suspected unconfirmed blocker: none established within scope.
Most important unchecked item: independent full source/kernel validation.
Dependence on unavailable material: none for this author-side conclusion.
Final recommendation: **unknown** for independent certification; the scoped
author-side conditions above are met.
