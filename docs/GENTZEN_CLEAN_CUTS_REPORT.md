# Simultaneous clean-cut normalization and initial elimination equations

Simultaneous atomization and blockedness are proved in the existing Reduced
presentation. The same representatives have the original sequents, cut-free
proofs, atomic thinnings, individual denotation equalities and every tied
contraction blocked. The formalization also continues with the identity,
atomic-zero, thinning and constant equations used at the base of cut elimination.
Global cut elimination and the full-paper endpoint remain open.

## Baseline and exact endpoint

The checkout fast-forwarded from ba5af8b to successor documentation
`a006ecdf7ca961f5355a44ed97629f960d5605d2`. No reset or stash operation was used.
The stash anchor is `dedfd8fc8cd49930e9a162d5be585215b062a43c`.
The preceding Reducibility, containing preservation, complete site correspondence,
finite descent and Blocked-w results are retained. Original production proofs
are unchanged except for the requested typographic repair in the comment at
GentzenFiniteOccurrences.lean:100. The public import and audit/check files grow.
The manuscripts are unchanged.

`DosenPetric.Reduced.Gentzen.clean_cut_premises`, in
GentzenCleanCuts.lean:14, quantifies over arbitrary P : Type u, C : NormalForm P
and all four contexts. Given f : G P Γ (C::Δ), g : G P (C::Θ) Λ and
G.Topmost f g, it constructs f' and g' at those same sequents, satisfying

    G.Topmost f' g' ∧ f'.Atomized ∧ g'.Atomized ∧
    ofTerm f'.denote = ofTerm f.denote ∧
    ofTerm g'.denote = ofTerm g.denote ∧
    AllBlockedR f' ∧ AllBlockedL g'.

`clean_cut_normalization`, at line 31, derives cut equality with
Rules.cut_congr and exports both universal addressed tied-contraction clauses.
Checks/CleanCuts.lean checks both complete types, including the per-premise
version with AllBlocked expanded. There is no coherence, Nonempty P,
DecidableEq P, supplied reduct or compatibility premise.

The source correspondence is the paragraph defining clean cuts immediately
after Blocked-w in Došen–Petrić, September 2007, §11.2, printed p.253. The
retained source PDF has SHA-256
e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
The proof supplies the simultaneous witnesses that were previously missing.

## Atomic structural realization and positional support

A Route K F sends At F A to At K A. Its product arrow goes from ante K to
ante F; its coproduct arrow goes from succ F to succ K. A StructuralProgram
P K F acts on a premise at F to produce a proof at K. The opposite-category
notation used for the coproduct calculations retains that variance.

`Route.AtomicOmissions` requires an atomic label at every individual lower
position with no preimage. `StructuralProgram.Atomic` requires every thin
instruction to insert an AtomicFormula. Both constants and both literal signs
are atomic under the existing predicate. Equal labels never merge tags.

`Route.atomic_program`, GentzenEconomicalRoutes.lean:13, recurses on K.
An empty lower context forces the upper context to be empty. For an unused
head, support supplies its atomicity; dropHead removes it for the recursive
call and a single thinning restores it. For a used head, anchored_factor selects
its complete fiber, with a node-free singleton or actual contraction, normalizes
its retained position, and recurses on the remaining lower context. The final
program composes that selection, normalization and the recursive tail under
consFixed. All requested get values are proved, and atomic_program_arrow
identifies both categorical arrows by their components. Program cut-count laws,
atomic composition/reindex/consFixed laws and left/right Atomized preservation
are available without a new G constructor.

SelectionMask.fixedAt embeds exactly the unselected positions into the original
context. fill_fixedAt and canonical_fixedAt prove its positional action.
factor_preimage proves that a residual tail position has a preimage precisely
when the original normalized route hits that same tail tag. The public
ContractionSelection.factor_route_preimage specializes this to the existing
unary factorization, including all casts. This equivalence transfers support to
the residual route; equality of categorical components alone is not used to
infer atomicity.

Exchange and contraction routes are surjective on lower positions. The actual
thinning route omits only its inserted position, whose formula is atomic when
the old input is Atomized. These facts are proved in GentzenInputRouteSupport.
The final same-side structural producers obtain support internally.

## One witness throughout local reduction and descent

Parameterized unary repairs accept the chosen tail program. Their count,
Atomized, equality and ContractionBound laws concern that same repair. The
existing consFixed_boundL/R laws keep every tail contraction outside the
selected head ancestry. The proof does not assert a strict drop in the repaired
root rank when that is unnecessary.

AtomizedReducesL/R describe a joint conclusion on atomized inputs. Both
`reducibility_left_atomized` and `reducibility_right_atomized` prove that
conclusion for every actual input constructor, every containing address and
every rebuilt eligible descendant. The unrestricted ReducesL/R definitions
and reducibility_left/right statements and proofs are unchanged.

| Actual input family | Atomization of the concrete repair |
| --- | --- |
| Same-side exchange, thinning, contraction | Economical tail program with internally proved support; the same program is used in equality and the full bound. |
| Opposite-side unary rules | Existing atomization equivalences retain each original atomic thinning; strict-rank repairs use the same witnesses. |
| Fixed/selected logical rules | Explicit exchange, logical and singleton-aware selection operations; the right HEAD-disjunction repair uses NonemptyRight.atomized. |
| Mix, native conjunction/disjunction and their one/two-premise regimes | GentzenAtomizedBinaryLeaves and GentzenAtomizedMix prove Atomized for each named existing repair, retaining their strict or blocked-middle bounds. |
| Terminal-source W6 | SourceLeft.reduces_atomized and TerminalOne.reducesFirst_atomized/reducesSecond_atomized package the actual source witnesses. |
| Basis and cut input | Existing basis impossibility and input CutFree exclude these cases internally. |

ReducibleL/R.rank_replacement_for takes the chosen h, its CutFree proof and
its complete bound. It gives the old/new rank-list permutations for that h.
Outside keys, inserted-root coverage, containing exclusion and multiplicity are
reused. The two atomized blocked normalizers call the strengthened producer,
obtain atomization of the addressed subproof from its root, and use
replace_atomized to retain the invariant through the existing well-founded
rank descent. No comparison is needed between ranks before and after the
initial atomization. The two premises are normalized successively; each
AllBlocked condition concerns only its own premise.

## Cut-elimination equations proved after clean cuts

The following equations are in Reduced, with actual Gentzen proof terms.
They are not an elimination interface supplied as a hypothesis.

| Source pattern | Declaration in namespace CutBase |
| --- | --- |
| Identity cut against identity | identity_identity |
| Zero/identity, identity/zero, zero/zero | zero_identity, identity_zero, zero_zero |
| Both cut occurrences freshly thinned | thinned_thinned, for arbitrary formula and contexts |
| Singleton endomorphism cut against a fresh left thinning | endomorphism_thinning; instantiate with either identity or zero |
| Fresh right thinning cut against a singleton endomorphism | thinning_endomorphism; instantiate with either identity or zero |
| topI against top thinning | top_thinning, with topRepair at the exact Θ++[], Λ++[] sequent |
| bot thinning against botE | thinning_bot |

These cover the displayed atomic/zero/thinning base equations in §11.2
pp.253–254 and §12.5 p.291, and the extra constant base patterns in §11.5
p.273. The generic thinned_thinned equation also specializes to top and bot.
The empty residual context is preserved explicitly by nilProgram and its
proved categorical arrow. topRepair_count and leftThinningRepair_count retain
cut count, and their atomization laws hold with the indicated atomicity input.
The singleton equations use decode_injective and the proved zero idempotence,
without interpreting relations or assuming faithfulness.

An exhaustive theorem classifying every minimal-rank clean cut has not yet been
proved. Nor have all principal, parametric and blocked-contraction cut reductions
and their rank bounds been assembled into global elimination.

## Regression checks and verification

GentzenCleanCutChecks checks a compound identity route, a singleton fiber,
a doubled fiber, atomic omissions including top/bot and signed literals, an
empty context, and the swap of two equal-labelled compound positions with
indices 1 and 0. equal_compound_unused proves failure of support when the
second of two equal compound tags is unused. These statements are generic in
P where appropriate; Empty supplies the constant-only examples.

The original GentzenAtomizationBlockedBoundary file is preserved byte for byte.
Its negative post-atomization preservation result remains true. boundary_clean
now instantiates the full positive simultaneous theorem at topI and before.
Checks/CleanCuts also instantiates both constant equations with Empty.

Final local evidence covers **442 Lean files / 11,105 audited project
declarations**, including generated helpers, with **29 new production modules**
and **458 hashed source/configuration/manuscript files**. The following
checks all exit zero:

- bash scripts/verify.sh: pinned Lean 4.35.0, source screening, complete public
  build and transitive axiom audit; only propext, Quot.sound and Classical.choice.
- Checks/CleanCuts.lean, Checks/BlockedW.lean and Checks/Reducibility.lean with
  warningAsError: expanded new and unchanged old public types.
- Both established boundary scripts: all five deliberate controls rejected,
  including illicit dependencies and removing the existing-arrow zero witness.
- Public import closure, manuscript SHA256SUMS and git diff --check.

The command receipts, all **25 nonzero attempts**, **62 compressed logs**,
control sources/results, module/declaration inventory and checked hashes are
retained in provenance/wsl-gentzen-clean-cuts. .codex-work/gentzen-clean-cuts
retains the original logs. A single heavy build or audit ran at a time under
the repository lock. The final checked bytes are compared with staged and then
committed bytes. Local build is distinct from independent kernel replay,
Comparator, official preflight/service verification, automated review or publication;
none of those additional statuses is asserted.

## Remaining contract and delivery

The next global statement is, for every t : G P Γ Δ, existence of t' at the same
sequent with t'.CutFree and ofTerm t'.denote = ofTerm t.denote. It is unproved.
First complete minimal-rank classification and the principal/commuting/blocked
reductions from §11.2 pp.254–262 with constants and atomic zeros retained.
Then assemble lexicographic clean-cut elimination and replacement of arbitrary
cut subproofs. There is no confirmed mathematical obstruction; these are
remaining implementation obligations.

Restricted mix/positive/reduced/Boolean coherence, actual source instances,
congruence/substitution bridges, the short q_A/e_A proof, actual maximality,
model corollary and the remaining appendix ledger retain their open scope.
The three milestones and full-paper endpoint stay distinct. All tagged-block,
ordinal-correspondence, source/native rank, singleton, empty-exchange, writing
and witnessed-zero requirements remain in force. No manuscript defect was
established or inferred from those obligations.

Retain this report and the two reviews under docs/ and docs/reviews/. Deliver
these committed copies, together with CODEX_AFTER_BA5AF8B_CLEAN_CUTS.txt and
the two GENTZEN_BA5AF8B reviews, to /mnt/c/Users/fleng/Downloads. Preserve any
differing destination and use the commit suffix. Actual delivered paths,
byte/SHA-256 comparisons, checked/committed source identity, preserved stash,
clean status and local/origin/live SSH refs are recorded after the commit in
.codex-work/gentzen-clean-cuts/POST_COMMIT_DELIVERY.json and the final response.
The preceding six ba5af8b deliveries remain complete and are not reopened.
