# Mathematical-writing review of simultaneous clean cuts

The report now states the simultaneous existence theorem first and explains
why its particular witnesses preserve atomization during blocked reduction.
It distinguishes the initial elimination equations from the global theorem
still to be proved. No manuscript revision is justified by this proof checkpoint.

This is an author-side review using
[mathematical-writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59).
Its scope is the new mathematical source comments/statements, implementation
report, current claim maps, correction record and continuation. It does not
constitute a fresh review of the entire manuscript or mathematical certification.

## Governing source and outline

Consulted Knuth, Larrabee and Roberts, Mathematical Writing, §1 points 5,
10–15, printed pp.2–3, in the retained
[MIT-hosted text](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf).
The local PDF has SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
The retained §4 excerpt, printed p.9, was also read. These passages support
self-contained theorem statements, connected explanation, definitions at use
and consistent notation. Definition placement remains sensitive to context;
the project's stricter definition-order requirement is not attributed to an
absolute rule in that excerpt. No long verbatim source passage is reproduced.

The chosen report outline follows the proof dependency:

1. Baseline and original-sequent simultaneous theorem.
2. Atomic structural realization and positional residual support.
3. One witness through every local repair and finite descent.
4. Initial cut-elimination equations proved after clean cuts.
5. Boundary examples, exact checks and the limits of verification.
6. Remaining full-paper obligations and delivery records.

The main result is clean_cut_premises, followed by its cut-equality corollary.
Route realization and strengthened Reducibility are prerequisites, rather than
alternative endpoints. The final global statement is written explicitly in
the remaining-obligation paragraph. This organization separates the theorem's
mathematical content from the external implementation and delivery records.

## Findings, revisions and connected read-through

| Anchor | Finding or risk | Revision or verification |
| --- | --- | --- |
| Report opening and exact endpoint | Separate blocked/atomized existence could obscure a common witness | State all properties for the same f',g' and give the full original types. |
| Route support section | Direction of get and coproduct variance can be misread | Define At F A → At K A and both arrow types before explaining recursion. |
| AtomicOmissions / fixedAt comments | Equal formula labels can obscure occurrence tags | Describe unused positions and exact preimages, and retain the equal-compound negative example. |
| Parameterized repair and rank sections | Existential witness switching would hide a proof gap | Name the chosen h and explain that its equality, Atomized proof and full descendant bound enter the same decomposition. |
| CutBase / constant discussion | Base equations could be mistaken for exhaustive elimination | List the proved equations and separately state missing rank classification and global induction. |
| GentzenFiniteOccurrences.lean:100 | Stray plus joined two sentences | Remove it; no definition or theorem change. |
| AtomizedReducesL comment | A sentence described API history rather than its mathematical hypothesis | State that the bound is on atomized inputs; verify the resulting source. |
| Active maps, README and continuation | Previous immediate target is now proved | Reconcile the current checkpoint in one pass and preserve earlier snapshots as historical. |
| Manuscript v6 | Formalization progress alone is not a manuscript defect | Preserve the manuscript, diagrams, references and accepted correction record. |

The complete new report and reviews were read as connected prose, together
with the current status passages and continuation. The explanation flows from
the exact theorem to its prerequisites, then to its scope. Definitions of
AtomicFormula, AtomicOmissions, StructuralProgram.Atomic and the two strengthened
reduction predicates precede use. Both constants remain atomic by the existing
definition. The product/coproduct convention, whole-formula ancestry and distinct
occurrence tags are consistent across source, report and maps.

The normalizers' Atomized hypothesis concerns the proof being normalized;
initial atomization supplies it. The report explains why there is no comparison
with pre-atomization ranks. It does not suggest that generic post-atomization
preserves blockedness. The retained negative example and its new positive
existence instance are compatible and remain visible.

The added comments state mathematical properties or explain a construction;
model-facing instructions, verification counts and delivery workflow remain
outside publication prose. No diagram was changed, so no new diagram rendering
or TeX build is claimed. The tagged-block and ordinal-coordinate requirements,
full-paper scope, symmetric-fold alternative and settled source/native rank
terminology remain in the active records.

## Validation and review limits

The local strict audit covers 442 Lean files and 11,105 project declarations;
three exact-signature files, the five negative controls and manuscript hashes
pass. Those checks substantiate the typed statements and source consistency,
not the literary quality of an unreviewed manuscript or an independent kernel
status. The companion hostile review records mathematical scope and remaining
uncertainty. No confirmed manuscript defect was found in this review scope.

Retain this review under docs/reviews and deliver its committed bytes to
Downloads alongside the mathematical review, implementation report and the
three successor artifacts. Actual conflict-preserving paths and byte comparisons
belong to the post-commit receipt and final response.
