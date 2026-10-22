# Contextual collapse checkpoint report

The WSL2 checkpoint proves contextual collapse, signed-literal isolation,
substitution transport, and relative maximality under explicit typed inputs.
It instantiates every field of the §5 interface in a generated nonthin
structural-fragment model, including an empty hom-set. It does not establish
maximality for the actual Došen–Petrić presentation.

## Source and task scope

The initial source was `37e1ee3792d04e3634ff6737a3da436e7c1ef476`, clean on
`main`, tracking `origin/main`. Development used `codex/contextual-collapse`.
The user authorized committing these scoped changes, integrating them into
`main`, and pushing `origin/main` over SSH without force. The remote is
`git@github.com:flengyel/Dosen-Petric-Maximality.git`; repository metadata
confirmed private visibility. The final commit and post-push identity check
are recorded in the completion response and `.codex-work/contextual-collapse/`.
Other projects and checkouts are outside this task. Manuscript v4 is unchanged.

The checkpoint's exact Lean source contents are identified by
[`source-hashes.json`](../provenance/wsl-contextual-collapse/source-hashes.json)
and [`source-SHA256SUMS`](../provenance/wsl-contextual-collapse/source-SHA256SUMS).
The clean build below was performed before the task commit; its printed HEAD
is the baseline, and its per-file hashes identify the actual working source.
It is not misrepresented as a clean test of the baseline commit.

## Proved declarations and exact hypotheses

All declarations are under `DosenPetric`. Objects are `Formula P`, for an
arbitrary type P; these conditional results do not require P to be nonempty.
The model corollary's nonempty-variable assumption remains a separate issue.

| Declarations | Exact data / hypotheses and conclusion |
| --- | --- |
| `Structure.pair_ext`, `copair_ext`, `comp_pair`, `copair_comp`, `prodMap_comp` | A category C and the typed product/coproduct beta and eta laws in `Structure`; derive universal extensionality, composition, and product-map equations. |
| `OccurrenceInterpretation.fold_independent`, `fold_swap`, `first_injection`, `second_block`, `through_top` | C, its `Structure` S, `ZeroIdentity` Z, and `OccurrenceInterpretation S Z` I. I preserves identity/composition, projections, injections, pairing/copairing, zeros, and distributor, and is faithful on original arrows. Conclusions are original-category equations obtained from the existing relation lemmas. No fold or collapse conclusion is an interface field. |
| `ContextualCollapse.second_block`, `injected_projections`, `terminal_injection`, `terminal_retraction`, `terminal_hom`, `other_injection`, `fold_top`, `equal_projections`, `total` | The preceding data plus Q, an equivalence on each existing Hom compatible with composition, pairing, and copairing; and every K_A. Here K_A means Q relates `comp (fst A bot) (j A)` to `zeroOf` of that existing arrow. The final conclusion is `∀ {X Y} (f g : Hom X Y), Q.Rel f g`. |
| `GeneratedModel.category`, `operations`, `zero`, `interpretation`, `nonthin`, `empty_hom` | Constructed for every P, with no assumed structural/model laws. Nonthinness requires p : P and distinguishes projections on var p. Empty hom proves `¬ Nonempty (Hom top bot)` for every P. |
| `Normalization.recover`, `transport_injective` | Actual normalization arrows A → normal(A) and back with inverse equations; transport to signed normal forms is injective on original arrows. |
| `Isolation.selector_edge`, `coselector_edge`, `isolate_edge` | S and I; a chosen occurrence in a signed normal form; for isolation, a relation edge of f missing from g and equality of the two signed literals. Constructs the typed selector/coselector and proves exact edge equations. Empty occurrence sets have no selectable positions. |
| `Isolation.literal_context`, `normalized_literal_context` | In addition: signed-label preservation of all interpreted edges between normal forms, normalization data N for the latter theorem, and an identified distinct parallel pair f,g under Q. Concludes existence of a positive or negative literal l satisfying K_l. |
| `Substitution.context_subst`, `ContextualCollapse.context_retract`, `all_contexts` | U maps every arrow f : A → B to an arrow A[σ] → B[σ] for each uniform σ and preserves the fragment operations, zeros, and identity/composition. Q is separately closed under U. Retract transport uses m : A → B, n : B → A with comp m n = id A. Negative literals use the specified `DoubleNegation` inverse arrows and p ↦ neg A. Concludes every K_A. |
| `relative_maximality` | C,S,Z,I,N,signed-label preservation,U,`DoubleNegation`, Q and its substitution closure, and f ≠ g with Q.Rel f g. Concludes Q.Total. These are explicit structural and published-input hypotheses, not a proved instance for B(P). |

`Structure` includes terminal and initial maps with uniqueness and the
manuscript distributor endpoints. `ZeroIdentity` retains the parallel-arrow
zero law. Congruence compatibility here is the restriction needed by the
argument; it does not specify every full Boolean proof operation.
`Substitution` gives a family of structure-preserving endofunctors with the
specified formula maps; laws for composition/identity of substitution schemas
themselves remain open. No substitution stability is deduced from a kernel
of one interpretation. The only existing-source transparency change makes
`Formula.Occ` an abbreviation, retaining its definition and tagged positions.

## What the generated model establishes

An arrow is a binary relation on occurrence sets together with propositional
evidence that a typed `GeneratedModel.Term` denotes it. All category,
product/coproduct, truth-constant, zero-identity, distributor, and faithful
occurrence-interpretation fields of the §5 interface are constructed and
checked. This is a complete model of that structural interface, rather than
just a pair of unequal relations. It proves both nonthinness (when P has a
variable) and a genuinely empty `Hom(top,bot)`. Zero arrows are always formed
from an existing-arrow witness.

The typed term grammar is the structural fragment. It contains no negation
functor, De Morgan isomorphisms, eta, or epsilon operations. Its auxiliary
`Term.Truth` treats negated formulas as atomic only for the empty-hom proof.
The model has not been identified with the full intended category, and no
joint instance of the whole relative-maximality interface is claimed. In
particular its normalization and arrow-substitution instances are outstanding.
The intended-model/presentation gate for milestone I remains open despite the
completed conditional collapse proof.

## Verification and controls

Observed host: Linux M2MA3HI, `6.6.87.2-microsoft-standard-WSL2`, x86_64;
15 GiB total memory, about 11 GiB initially available, no swap. The installed
pinned compiler was Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with Lake
`5.0.0-src+eb6cafb`. No setup/install or Mathlib/Foundation dependency was needed.
One build or audit was run at a time.

| Command / check | Actual result |
| --- | --- |
| `bash scripts/verify.sh` at baseline | Exit 0; five source files; 176 project declarations. |
| `lake clean`, then `bash scripts/verify.sh` for integrated source | Both exit 0; all 12 Lean sources pass screening; 13 Lake jobs complete; 645 visible project declarations pass transitive axiom audit, including private names. |
| `python3 /tmp/dp-contextual-collapse/check-boundaries.py` | Exit 0; public axiom, private axiom, and hidden external-axiom dependency controls each exit 1 with the required rejection; all production modules are in the public import closure. The committed replay command is `python3 scripts/check-audit-boundaries.py`. |
| `sha256sum -c SHA256SUMS`, from `manuscript/` | Exit 0 for the original TeX and PDF. |
| `git diff --check` | Exit 0. |
| Hostile-referee / mathematical-writing reviews | Applied to the actual conditional argument and correspondence map; reports under `docs/reviews/`. Author-side automated reviews, not independent peer review. |

The permitted axioms are exactly `propext`, `Quot.sound`, and
`Classical.choice`. Collapse and the generated model use the first two;
normalized isolation and relative maximality also use `Classical.choice`.
`context_retract` and `all_contexts` print no axioms. No custom mathematical
axiom, production proof hole, or `native_decide` is used.

A first control exposed that encoded private names escaped the old namespace
filter. `Checks/Axioms.lean` now applies Lean's `privateToUserName` before
filtering project declarations. This raises coverage from 619 to 645 for the
integrated library, and all three final controls reject. The negative-control
sources are stored as `.lean.txt` evidence and are never production imports.

No independent Challenge/Solution compilation or shared-definition comparison,
Comparator run, independent kernel replay, official Palomar preflight, service
verification, or publication was performed. The local import check and
compiler-environment axiom collection are not substitutes for those checks.
No comprehensive new literature or priority review was performed.

## Evidence locations and hashes

Durable records are in `provenance/wsl-contextual-collapse/`; local working
logs are in `.codex-work/contextual-collapse/` and `.codex-work/verification/`.
The directory's `SHA256SUMS` authenticates every evidence file, including the
source inventory, baseline environment, control sources, and raw rejection
logs. Main evidence SHA-256 values are:

- `baseline-verify.log.txt`: `815066ebb09e69f2b2e112cdf7f129615e965270ae7cd58cfbc57aee4eb26a5a`.
- `baseline-environment.json`: `d1f125e9fc5494c04dc5518ba9fb8dc84f6bc6330918197d88b60a5ae654d0ac`.
- `verify.log.txt`: `49a2e4e2a69ec4f4e92c667c9b12b2022773390df554fbb97eca7b0e440f3dc8`.
- `audit-controls.json`: `e5635ec304909ab2bc88c49ba09a9736f32d07f66d6a14c63ef27b86af929c97`.
- `source-hashes.json`: `556d492bcee9cb53021d2512f8b5661f6a1c9a8ecc254db74a505c928c516b84`.
- `source-SHA256SUMS`: `14e9a88b52cd1358da7829721c73e90af411d1441f53b6f75135c5b87501b280`.
- `record.json`: `ee87fc9445d70e6ed294865330c0d74484cc390c28e2b34f712bd601208bc7ef`.

To check the durable bundle, run `sha256sum -c SHA256SUMS` in its directory;
run `sha256sum -c provenance/wsl-contextual-collapse/source-SHA256SUMS` from the
repository root to compare the production source. The selected theorem
`#print axioms` outputs are in `verify.log.txt`. Exact control commands, exit
statuses, source/log digests, and import inventory are in `audit-controls.json`.

## Remaining obligations and next concrete task

1. Define/import the actual Došen–Petrić arrow presentation from the exact
   September 2007 revision, including negation/De Morgan/eta/epsilon operations
   and equations. Prove the structural and zero-identity-formula bridge.
2. Establish the intended faithful occurrence interpretation and its operation
   laws. The generated fragment's faithful relation semantics do not establish
   the published coherence theorem for the actual category.
3. Construct the intended normalization, signed-label preservation,
   double-negation, arrow-substitution, and congruence-restriction instances.
   Prove their occurrence/substitution correspondence and schema action laws.
4. Instantiate relative maximality through that bridge; then prove the semantic
   corollary with every interpretation and nonempty P. Complete Appendix A's
   profile, finite-ordinal, and renaming bridges separately.
5. Before any Palomar package, recheck official policy and implement independent
   statement/definition/dependency/source-closure checks, focused Comparator
   controls, independent kernels, and immutable-source evidence. Publication,
   visibility changes, and license selection require separate authorization.

The next proof task is the typed intended-presentation bridge, beginning with
its arrow grammar, equations, and the §5 structural/zero interface. Do not
re-prove the completed conditional collapse or treat fragment-model consistency
as the intended-category instance. The updated statement and coverage maps
retain all these boundaries.
