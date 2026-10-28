# Author-side audit of selected-cut elimination progress

This audit uses [HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe).
It reviews the actual new argument, source and correspondence map after local
verification. It is not an independent review or whole-paper certification.

## (A) Kill-shots / hard blockers

No confirmed mathematical blocker was found in the bounded compiled claims.
The global cut-elimination theorem is absent and explicitly open. Anchor:
GentzenCutEliminationSpec.CutElimination/AtomizedCutElimination; these are endpoint
definitions. Claim tested: unrestricted same-sequent normalization for arbitrary P.
Failure mode if asserted now: unproved; evidence: absence_in_text of an inhabitant
of either endpoint. Downstream: coherence and full-paper completion cannot be
closed. Severity: hard blocker to such a completion claim; repairable by finishing
the degree/rank construction, not by accepting a normalizer as an input.

## (B) Major weaknesses

1. Anchor: GentzenRankTwoClassification.rank_two_classification, PrincipalPair.
   Claim tested: classification versus elimination. The atomic branch returns an
   actual Eliminated witness, whereas conjunction/disjunction return a typed
   principal pair only. Failure mode for a broader elimination claim: unproved.
   Evidence: structural_argument; the theorem's disjunction and the missing
   compound reduction equations. Downstream: outer degree induction cannot yet
   be assembled. Severity: major for global elimination, no defect in the bounded
   classification. Repair: prove the two concrete nested-cut equations and use
   strictly smaller degree without imposing a returned-rank bound.
2. Anchor: CutCommutation.opposite_left/opposite_right and SelectedRecursion.
   Claim tested: complete commuting/blocked reduction coverage. Only opposite-side
   structural equations and generic selected predecessor invariants are proved.
   Failure mode for completeness: unproved. Evidence: absence_in_text of the
   remaining logical, binary and fourteen blocked reduction equations. Downstream:
   fixed-degree all-ranks induction is still open. Severity: major, repairable;
   retain the explicit open coverage rather than using correspondence alone as
   a reduction theorem.
3. Anchor: Appendix C and GentzenFreshPrincipals.rank_fresh_disjL.
   Claim tested: exact source p.262 reduction correspondence. The native occurrence
   has right rank one, and every selected total rank is at least two. The source
   disjLLast wrapper has exchanges. Failure mode for identifying the wrapper with
   that native leaf: unsupported_generalization. Evidence: derivation; script rho
   increases by its actual exchange steps. Severity: major if such identification
   is used; no such identification occurs. Repair: keep the principal occurrence
   native in the actual positional blocked reduction and prove its adapters.

## (C) Minor issues

The first implementation attempts exposed dependent-context elaboration issues
and a compiler panic after malformed definitions. All corrected modules pass
warning-as-error builds and the transitive audit. Evidence: derivation and retained
failed/successful logs. This is an implementation history, not a counterexample.
Three signature launches were stopped by the lock before Lean execution; the
subsequent sequential checks pass. Retaining these exits prevents an inaccurate
all-attempts-succeeded report.

## (D) Cross-section consistency failures

No unresolved mismatch was found in the bounded exported types. Position identity
uses tags, not formula equality; neither DecidableEq P nor Nonempty P appears.
Cut output is (erase y ++ Γ, Λ ++ erase x), including empty lists. The selected
measure is computed before routing. Native routed rank is proved to add the
explicit exchange costs. AllBlockedAt uses actual whole-formula ancestry and
LowerContraction; both head correspondences and predecessor inheritance compile.
The clean normalization theorem has no rank bound and is not used to justify
same-degree rank descent. Source/native distinction, witnessed zeros, original
category coherence requirements and all earlier regressions are preserved.

Category-theory type check: arrows live in Reduced; comp f g applies f then g.
The coproduct-side fold comparison is contravariant. prefixFixed_split and
suffixFixed_split state the actual comparison squares; CutCommutation instantiates
them in typed cut equations. No missing inverse arrow is inferred from a merely
one-way arrow. The two-object one-arrow test gives no new assumption: exchanges
are supplied as explicit invertible scripts; arbitrary structural programs are
never inverted.

## (E) Acceptance conditions, non-negotiable

1. Retain all compiled public statements and full strict/type/control evidence;
   otherwise withdraw this bounded verification claim.
2. Keep compound principal elimination and all remaining commuting/blocked
   families open until actual typed Reduced equations and recursion hypotheses
   are checked; otherwise reject a global-elimination claim.
3. Complete the all-ranks inner theorem before unrestricted clean normalization
   at fixed degree; otherwise reject the claimed induction.
4. Close every actual-presentation, coherence, short-proof, model and appendix
   bridge before asserting whole-paper completion; conditional maximality or
   the new Appendix C prose does not satisfy that endpoint.
5. Deliver committed reports/reviews with byte checks, preserve the stash and
   compare checked source with committed bytes; otherwise delivery is incomplete.

## (F) Not checked / uncertainty log

No new full-paper mathematical audit, literature/novelty review, independent
kernel replay, Comparator or Palomar run was performed. No publication or contact
was made. The source errata were checked against rendered primary pages during
the earlier v7 addition; this proof checkpoint does not re-certify the entire
source's cut-elimination argument.

Strongest confirmed blocker: the global elimination endpoint remains unproved.
Strongest suspected unconfirmed blocker: none established in the bounded claims.
Most important unchecked item: the actual compound and blocked reduction equations
needed for global assembly. Recommendation depends on unavailable material: no;
its bounded evidence is retained, and missing proofs are explicitly identified.
Final recommendation: unknown for the full-paper endpoint; retain the checked
bounded statements with their stated scope.
