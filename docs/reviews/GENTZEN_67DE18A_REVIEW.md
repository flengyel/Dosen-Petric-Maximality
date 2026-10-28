# Completed-run review: 67de18a

The completed run supports the reported principal, structural and opposite
logical results. No confirmed defect was found in those new proofs or in v7's
bounded errata addition. Global cut elimination and the full-paper formalization
remain open. The next work is concrete same-side logical/binary commutation,
fourteen blocked families and the induction assembly.

This author-side review applies
[HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe).
It is a source/evidence review, not an independent kernel replay or a new
whole-paper correctness certificate. Local Codex's completed run preceded this
handoff, as the author required.

Reviewed head: 67de18a77f1c3901c68b82f5e0533d873ce6e80d.
Checked proof parent: 59e2c12528ecb6e48df436136265afb81edc20de.
The final commit changes delivery/continuation evidence only. Git history
contains 1376bcb and the intervening v7, positional, principal conjunction,
principal disjunction, structural and opposite logical checkpoints.

## (A) Kill-shots / hard blockers

**A1. The unrestricted elimination endpoint remains unproved.**
Anchors: GentzenCutEliminationSpec.lean (CutElimination and AtomizedCutElimination),
GentzenPrincipalDegreeSteps.lean (DegreeBelow) and
PositionalCut.rank_two_degree_step. Claim tested: whether the current results
supply an unconditional representative for every G proof. Failure mode:
unproved, not false. Evidence: absence_in_text of an endpoint inhabitant and
explicit source signatures retaining DegreeBelow/strict-rank hypotheses.
Severity: hard blocker to claiming global or full-paper formalization.
Repairability: requires the missing concrete cases and discharged inductions;
a status edit or additional interface cannot repair it.

**A2. No new hard blocker was confirmed in the bounded results.**
Evidence: derivation by reading all 63 added production modules and five added
public check files, against the current definitions and retained verification.
Both principal equations are actual equalities in Reduced; the recursive
degree branches produce actual witnesses. Structural/logical commutations
have typed reconstructions and actual predecessor descent. This conclusion
does not independently reprove every unchanged dependency.

## (B) Major weaknesses

The following are the principal obligations or failure modes tested; resolved
risks are not classified as extant defects.

1. **Conditional rank-two elimination.** Anchor: both principal degree_step
   proofs and rank_two_degree_step. Each component call has strictly smaller
   formula degree, arbitrary returned rank and actual CutFree premises. The
   second call consumes the returned first witness, not an assumed rank bound.
   Evidence: derivation. Scope is correct as written. Elevating it to an
   unconditional endpoint would leave A1 unproved. Repair: discharge DegreeBelow
   by outer strong induction after the all-ranks fixed-degree theorem.

2. **Original rank versus routed native rank.** Anchors:
   GentzenPositionalRoutingRanks.routed_rank_eq,
   GentzenExchangeScriptRanks and GentzenSelectedRecursion. The selected measure
   is evaluated on the original two premises; routing adds its actual exchanges.
   Equality transports and head identity add none. Evidence: derivation and
   exact public checks. No rank conflation was found. The remaining dispatcher
   must preserve this distinction, particularly with empty blocks and repeated
   labels. Impact if violated: invalid recursive descent.

3. **Post-elimination atomization is sound at the stated scope.** Anchors:
   GentzenStructuralCutReplacement.lean, same_right_eliminated/same_left_eliminated.
   The proof first obtains a cut-free child witness, applies the actual residual
   program and then atomizes the completed cut-free reconstruction. It claims
   neither an output-rank bound nor output blockedness. Evidence: derivation.
   The old counterexample to atomizer preservation therefore does not refute
   these results. Do not reopen a general Atomic-residual-route requirement.
   A witness used by a later cut still needs that later cut's own cleanliness
   and strict-bound argument.

4. **Actual categorical equations, including reflected diagrams.** Anchors:
   PrincipalConjunction.selected_equation,
   PrincipalDisjunction.selected_equation, MirrorCalculus,
   MirrorInterpretation and the native rule equations. The conjunction
   A-then-B and disjunction B-then-A constructions are proved directly in
   Reduced. The reflected interpretation proves the required laws and connects
   its diagrams to Rules.sourceConj and the actual splice; it does not assume
   an arrow-duality or G-proof-duality operation. Evidence: derivation.
   No uninstantiated coherence field was identified in these equations.
   Preserve the documented distinction from the source's displayed order.

5. **Remaining parametric and blocked cases.** Anchors:
   GentzenBlockedPatterns, the completed structural/opposite logical rank steps
   and the current coverage map. Failure mode: unproved families. Two same-side
   unary logical families have four nonprincipal tag regions; the binary
   parametric families have twelve actual branch obligations. All seven
   BlockedL and seven BlockedR reductions remain. Evidence: absence_in_text
   and constructor analysis. Severity: major construction work, not a defect
   in the completed cases. Repair: actual Reduced equations, complete inherited
   cleanliness, strict original selected-rank inequalities and reconstruction
   before assembling the dispatcher.

6. **Sequential blocked cuts need a fresh principal occurrence.** Anchors:
   GentzenFreshPrincipals and BlockedSource.disjLLast. Native fresh principals
   have one-sided rank 1; the source macro has exchanges above its logical rule.
   Evidence: derivation and structural_argument. Generic fresh-principal
   comparisons are proved, but their concrete blocked-family instantiations
   are not. Use routing below the fresh native rule and prove source/native
   correspondence. Do not infer a bound for an arbitrary returned normal form.
   Severity if omitted: invalid same-degree recursion.

## (C) Minor issues

The retained final-phase command record contains 26 commands, including ten
nonzero implementation/check attempts. The final verification and all eight
selected public-type runs have exit status zero. One retained failed exact
check was followed by the explicit-parameter repair and successful final run.
These are preserved development failures, not unresolved final failures.

The old continuation and full contract accumulated superseded "next" lists.
The successor archives the previous continuation verbatim, supplies a concise
active continuation and updates the full contract's immediate paragraph.
Category: documentation consistency, not a mathematical correction.

No change to the Lean source or manuscript is required by this review.
Proposed new constructions in the successor remain proof targets until checked.

## (D) Cross-section consistency failures

No new mathematical inconsistency was confirmed in the bounded results.
Selected deletion retains actual occurrence tags, including equal labels;
SingleFiber quantifies across labels. Fixed-context and association comparisons
are typed on both category sides. Composition remains left-argument first.
No new G constructor, unwitnessed zero or nonempty-hom-set assumption appears
in the added construction. The intended-category and milestone boundaries
remain in force.

V7's independent diff against preserved v6 consists of the date, introduction
roadmap and supplied Appendix C, with its page break. The appendix text matches
the authorized instruction exactly. All ten diagram sources, Appendices A–B,
accepted disclosure and bibliography remain unchanged. The six v4/v5/v6 blobs
are preserved in Git. Appendix C is readable and contained on PDF p.12; references
follow on p.13. The unchanged §6 still distinguishes conditional relative
maximality from an instantiated full-presentation theorem.

Appendix C's source corrections remain r' < r on printed p.260 and RIGHT rank 1
on p.262; positive side ranks make total rank at least 2. Their concrete blocked
Lean correspondences remain open. This does not make the completed manuscript
addition incomplete. Historical records must not reset these current statuses.

## (E) Acceptance conditions, non-negotiable

1. Retain the exact principal, positional, structural and opposite logical
   results and their full hypotheses; do not replace them with weaker exports.
2. Prove the remaining constructor/tag and fourteen blocked cases at their
   actual output sequents, with complete clean/rank arguments.
3. Discharge strict rank and DegreeBelow hypotheses before claiming an
   unrestricted elimination theorem; audit actual endpoint inhabitants.
4. Preserve all accepted source/native, routing, atomization, substitution,
   witnessed-zero and occurrence-tag decisions.
5. Keep all three milestones and whole-paper completion distinct; continue the
   full contract after elimination.
6. Preserve v7 and older versions. Update Appendix C's Lean ledger only when
   its concrete reductions and comparisons are proved.
7. Run local strict/dependency/type/control checks on new immutable source and
   retain the actual logs, exits and failed attempts.
8. Commit/push scoped verified work without force and deliver the new reports
   and three successor artifacts from committed bytes to Downloads.

## (F) Not checked / uncertainty log

Independent review checks actually performed:

| Item | Result and scope |
| --- | --- |
| Git delta after 1376bcb | 68 new Lean files: 63 production, five Checks. The only modified older Lean file is DosenPetric.lean, adding the new imports. No prior proof module/check was replaced. |
| Read source | All 63 new production modules and five new Checks; active instructions, correspondence and relevant implementation/review records. Unchanged dependencies retain their earlier review scope. |
| Retrieved text | 113 UTF-8 blobs independently matched their Git blob identities. |
| Checked-source inventory | 71 retrieved text entries plus v7 PDF match inventory bytes/hashes; 72 of 528 entries independently checked here. The full 528-entry match is the local run's recorded result, not a cloud replay. |
| Final-phase archives | All 26 compressed/raw log hashes match the retained archive index. Final strict, audit, presentation, manuscript and whitespace records have exit zero. |
| Final public checks | Eight recorded exit-zero files. Inspected signatures preserve the recursive hypotheses. Printed axiom lists inspected contain only the permitted propext, Classical.choice and Quot.sound; full transitive audit success is recorded locally. |
| Controls and counts | Logs record all five expected rejections, 510 screened Lean files and 11,669 audited project declarations. No build was run by this reviewer. |
| Delivery register | Uploaded register is byte-identical to committed register. All 23 listed artifacts independently match the reviewed repository bytes, lengths and SHA-256 values. |
| V7 | Source/PDF hashes verified; exact authorized addition and unchanged baseline content checked; actual p.12 and all-page layout contact sheet inspected. Local TeX log/check record reports no warnings or unresolved references. |

The register refers to proof commit 59e2c12528ec; evidence-only 67de18a explains
that anchor. Actual WSL checkout/stash, live SSH refs and Downloads storage are
not accessible in this review. Their agreement is the user's/local receipt's
claim. No independent kernel, Comparator, official/service verification,
publication or fresh whole-paper reproof was performed.

No new literature result is asserted. The prior primary-source review of
September-2007 printed pp.249, 253–262 and its two errata is retained, with PDF
SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.

The existing 23 deliveries remain recorded complete. This review, its writing
companion and CODEX_AFTER_67DE18A_CUT_ELIMINATION.txt are new; local committed-byte
Downloads delivery is pending and assigned in the successor.

Strongest confirmed blocker: the unconditional reduction/induction assembly is
unproved. Strongest suspected unconfirmed blocker: none established in the
reviewed additions. Most important unchecked item: the remaining concrete
blocked reductions and their complete induction. Unavailable-material dependency:
no for this bounded source verdict; independent verification of WSL delivery/state
would require access not available here. Final recommendation: **unknown** for
whole-paper formalization; retain the bounded results at their proved scope.
