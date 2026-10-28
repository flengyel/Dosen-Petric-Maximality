# Completed-run mathematical and evidence review: 77199ac

## (A) Kill-shots / hard blockers

**Whole-paper and global cut-elimination completion remain unproved.**
Anchor: `GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md`, seven pending logical binary
rows, fourteen blocked families and its final induction paragraph;
`GentzenCutEliminationSpec.lean`, the two endpoint definitions. Claim assessed:
whether every actual G proof now has the required unconditional cut-free
atomized representative. Failure mode: **unproved**. Evidence:
**absence_in_text / structural_argument**: five binary rank steps are supplied,
while the remaining constructor cases and the rank/degree/structural induction
assembly are absent. This is a hard blocker to a broader completion claim,
not a counterexample to the completed five branches. Repair: the concrete
remaining reductions and discharged inductions, followed by later paper obligations.

No confirmed defect was found in the bounded additions after reading all twenty
new production modules and both new public check files. This is an author-side
source audit applying [HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe),
not external peer review or an independent kernel replay. The formal target is
manuscript v7 with all three appendices; this review covers the completed code
delta and its correspondence records, not a new whole-paper referee judgment.

## (B) Major weaknesses

1. **The exact first-child native equation is still unproved.**
   Anchor: `provenance/wsl-gentzen-logical-binary-cuts/open/next-native-first.lean`,
   lines 8–21, and `OPEN_OBLIGATIONS.json`. Claim as written: the denotation of
   `G.cut h (G.conjR f g)` equals the denotation of the typed `firstNative`
   reconstruction of `G.cut h f`. Failure mode: **unproved**; severity: major
   remaining construction. Evidence: **derivation / absence_in_text** and the
   retained exit-1 log, whose only final error is the unsolved arrow equality.
   The input I/Theta and output D/Lambda exchanges elaborate. The attempted
   rewrite does not establish a false equation. Repair: prove the distribution,
   symmetry and fold comparisons, then the original-tag reconstruction and rank
   step. The successor supplies two typed comparison targets; they remain uncompiled.

2. **Completed mix equations use their actual builders.**
   Anchors: `GentzenBinaryMixLeftStep.lean:15–50,64–112` and
   `GentzenBinaryMixRightStep.lean:24–60,65–113`. Claim: exact positional-cut
   replacement and smaller-original-rank recursion. Evidence: **derivation**.
   `firstRaw`/`secondRaw` apply concrete residual structural programs to the
   proved leading/right-first construction. Their equations use `native_swap`
   and proved unique fibers. Each rank step calls `ih` on the original child
   given by its existing descent. No conclusion-shaped diagram assumption is
   present. The direct `leftFirst` macro has typing/count/Atomized/congruence
   laws but is not the builder in `first_equation`. Failure mode if conflated:
   **unproved**; no such conflation was found in the final public results.
   Downstream requirement: preserve these exact builders and their proved scope.

3. **Atomization is used after cut elimination in the swapped mix cases.**
   Anchors: `GentzenBinaryMixLeftStep.lean:52–75` and
   `GentzenBinaryMixRightStep.lean:90–101`. Claim: the same output witness is
   cut-free, atomized and equal in Reduced to the original cut. Evidence:
   **derivation**: the raw cut count is the eliminated child's count plus the
   unchanged child's count; both are zero before `G.atomize` is applied.
   `G.atomize_cutFree`, `G.atomize_atomized` and `G.atomize_denote` then supply
   the three conclusions. Neither output blockedness nor a returned-rank bound
   is claimed. The earlier atomizer counterexample therefore gives no new defect
   here. Potential failure mode: **unsupported_generalization** if such stronger
   properties are inferred. Preserve the accepted limited use; no repair needed.

4. **The reflected mix comparison is an instantiated interpretation.**
   Anchors: `GentzenBinaryMixMirror.lean:12–23,82–119` and
   `GentzenBinaryMixRightDiagram.lean:18–46`. Claim: the right-premise splice/mix
   equation holds in Reduced. Evidence: **derivation**. The added interpreted
   mix/injection arrows and laws are explicitly defined; `splice_native`
   identifies the interpreted splice, object involutions are normalized and
   the product cross is identified by the actual coordinate law. A general
   duality on G proofs or quotient arrows is not assumed. Potential failure mode:
   **unsupported_generalization** in extending this argument without new
   interpretation laws. Later disjL diagrams must supply those laws or a direct proof.

5. **The right-second conjunction branch is complete at its stated scope.**
   Anchors: `GentzenBinaryLogicalDiagram.lean:14–77`,
   `GentzenConjRightSecondDiagram.lean:13–32`,
   `GentzenConjRightSecondParent.lean:79–83` and
   `GentzenConjRightSecondSelected.lean:45–114`. Claim: exact original-tag
   equation, generic reconstruction, count/Atomized/congruence and instantiated
   rank step. Evidence: **derivation**. The product splice and residual
   association are proved from actual laws; every native fold/unit and selected
   routing comparison is instantiated. The retained B occurrence remains a
   separate typed component. The rank call is exactly `ih h z g a hd.2 hd.1`,
   with original-child full Clean and strict rank supplied before reconstruction.
   No defect or additional premise was found. Generalizing from this branch to
   the other seven without their equations would be **unsupported_generalization**.

6. **Mixed-rule symmetry resolves one failed attempt, not the native cut equation.**
   Anchor: `GentzenMixedDisjSymmetry.lean:13–95`, especially
   `mixedDisj_swap:44–48`. Claim: the displayed interchange of the two mixed-rule
   factors holds in Reduced. Evidence: **derivation** from the defined
   `distRight`, `dist_b_disj`, naturality, symmetry cancellation and hexagon.
   The retained old distributor failure is superseded by this proof. The
   separate first-child equation remains open. Potential failure mode:
   **inconsistent_use** if these two statuses are merged. Repair in the handoff:
   name both equations and their different statuses explicitly. The principal
   swap inside B∧A must remain an actual arrow; a context permutation alone
   cannot change B∧A into A∧B.

## (C) Minor issues

The active instructions still identify b8fcd28 as the reviewed head:
`AGENTS.md:47–50`, `CODEX_NEXT_SESSION.txt:11–13` and the full contract's
“Immediate continuation” opening. The live constructor table also places the
new mix-reconstruction status beside the older mix-algebra evidence pointer.
These are confirmed instruction/provenance ambiguities, **inconsistent_use**,
supported by **absence_in_text / derivation** from the current records.
They do not invalidate a proof. The successor reconciles all active pointers,
separates the evidence phases and archives the previous continuation verbatim.
Historical reports retain their checkpoint-specific scope.

The rejected focused controls test concrete type or definitional boundaries.
A failed `rfl` attempt is not by itself a general semantic counterexample.
The audit treats these controls as expected rejections, exactly as recorded,
and keeps the unsolved next-native attempt separate from the nine controls.

## (D) Cross-section consistency failures

No new mathematical inconsistency was confirmed in the reviewed additions.
Equality means equality of `ofTerm p.denote` in Reduced; it is not identity of
G derivations. `G P Gamma Delta` denotes a proof with the displayed input/output
contexts; `At` and `erase` track selected occurrences, not just labels.
The original selected rank and the rank after native head routing remain distinct.
Generic statements retain arbitrary P without new Nonempty or DecidableEq premises.
Empty contexts, signed literals and empty hom-sets remain allowed; no unwitnessed
zero or occurrence-graph equality-reflection principle was introduced.
Composition applies its left argument first; native mix still has reversed child
blocks. Existing opposite/structural and unary results keep their original scope.

The complete Git delta after b767c19 has 195 added/changed blobs and no deletions.
Twenty production modules and two Checks are new. The only modified existing
Lean files are the public import root and `Checks/Axioms.lean`, adding imports
and audit requests. Toolchain, manifest and verifier scripts are unchanged.
All nine manuscript blobs match the preceding checked state. No TeX edit or
new manuscript erratum is indicated. Appendix C's two actual blocked-rank
correspondences remain open, as do all later paper obligations.

The handoff's first-factor splice and residual-output equations were checked
for source/target compatibility against `splice`, `innerDisj`, `mixedDisj` and
the side associators. Their proposed derivation uses completed second-factor
equations and symmetry. They are marked implementation targets throughout;
this review does not count them as Lean results or assume them in an endpoint.

## (E) Acceptance conditions, non-negotiable

1. Preserve all five completed binary branches, their exact hypotheses/builders
   and full original-child rank calls. Failure rejects the affected bounded claim.
2. Complete the retained conjR_right_first equation through the selected-tag
   eliminated wrapper and instantiated rank step. Auxiliary equations alone
   do not meet this endpoint; omit a completed-row claim if it remains open.
3. Complete the remaining six logical branches with actual typed equations and
   witnesses, preserving retained principal occurrences. Otherwise a complete
   binary dispatcher remains unproved.
4. Prove all fourteen blocked reductions, source/native comparisons and the
   discharged rank/degree/structural inductions before claiming either unrestricted
   elimination inhabitant. Failure excludes global elimination completion.
5. Complete later coherence, intended-presentation/substitution/congruence,
   maximality, model and all-three-appendix claims before full-paper completion.
6. Retain the local strict/transitive checks, public signatures and actual
   reconstruction witnesses, source closure and nine existing controls; add
   focused new checks when they test the new construction. Validation claims
   require the corresponding successful recorded commands.
7. Preserve v7, earlier versions and accepted corrections. Change manuscript
   mathematics only for an established correction within the author’s scope.
8. Commit scoped work without force and deliver the three new successor files
   plus new reports/reviews from committed bytes. Missing copies remain a
   delivery obligation, not a mathematical defect.

## (F) Not checked / uncertainty log

| Item | Work performed and limit |
| --- | --- |
| New source | Read all twenty production additions and both new public Checks, with relevant unchanged splice, rule, descent and structural definitions. No complete handwritten reproof of every old dependency. |
| Source identity | All 554 attached archive files match both their SHA-256 list and Git blob identities at 77199ac. Archive SHA-256: 9bfc0d3a383a6bb233a9ea27e0fd6e6c902ce6a81c06c261e34addc7d0eb8cba. Manifest SHA-256: e81bc78e841df35ecc3f4cb549cc00d118a67d78bc9f9a180648779523bb113c. |
| Final evidence | Checked compressed/raw hashes of 21 logs: strict verification, twelve public checks, two boundary checks, whitespace, four focused controls and the final open-equation failure. All sixteen final verification commands have exit zero; the four focused controls and open attempt have their expected/distinguished exit-one statuses. |
| Audit scope | Strict log records 546 screened files and 11,911 transitively audited declarations. New result dependencies print only permitted propext, Classical.choice and Quot.sound. Nine control sources were fetched and their intended mutations/type failures inspected. |
| Development logs | Earlier failed attempts remain archived. The other 33 logical-phase log archives and earlier mix-phase logs were not independently rehashed or replayed here. Final checks include the retained mix construction. |
| Current deliveries | All seven newly attached files were checked. All sixteen logical-register artifacts match their recorded lengths/SHA-256 values and current Git bytes. The uploaded register and verification JSON equal the repository copies. |
| Earlier deliveries | Read the 19-entry mix register and successor receipt; checked its three mix reports/reviews and three b767c19 successor files. The other thirteen mix-register entries were not individually revalidated in this review. All 35 retain their recorded local delivery status. |
| Manuscript | Nine unchanged blobs; no fresh TeX build, layout inspection, whole-paper mathematical audit or novelty review. Earlier manuscript reviews retain their stated scope. |

The actual WSL checkout, stash, live SSH refs and Downloads storage are not
accessible here. Their reported state is supported by the author/local receipts,
not independently inspected filesystem state. No Lean or TeX build, independent
kernel replay, Comparator, official/service verification or publication ran.

Strongest confirmed blocker: seven logical branches, fourteen blocked reductions
and the global induction remain unproved. Strongest suspected unconfirmed blocker:
none established in the completed additions. Most important unchecked result:
the remaining native equations and complete induction. The bounded source verdict
does not require unavailable material; direct WSL-state validation and whole-paper
completion require work outside this review. Final recommendation: **unknown**
for whole-paper formalization; retain the five completed branches at their scope.
