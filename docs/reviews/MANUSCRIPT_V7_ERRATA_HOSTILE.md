# Author-side review of the V7 errata addition

This review uses [HostileRefereeGPT — Cat/Rec](plugin://plugin_867af61c251c819194f29c5c462eafbe).
It concerns the author-requested Appendix C, roadmap sentence and their source
correspondence, not a new certification of the whole paper.

## (A) Kill-shots / hard blockers

No confirmed blocker was found in the bounded addition. Anchor: v7,
app:cut-errata, rendered p.12. The supplied corrections and mathematical
explanations occur verbatim, with their source locations, notation and existing
DP citations. Evidence: source comparison and rendered primary-source pp.260–262.
The old main results and Appendices A–B are unchanged.

## (B) Major weaknesses

The new concrete Lean correspondence remains unproved. Anchors: Appendix C's
p.260 and p.262 paragraphs, and the corresponding new claim-ledger rows.
Claim tested: the actual blocked gammaDisj recursive cuts satisfy the strict
selected-rank inequality, and the sequential blocked disjunction reduction uses
a fresh right principal occurrence of rank one. Failure mode: unproved in Lean;
evidence: absence_in_text of the assembled concrete reduction proofs and their
explicit open status. This is major for full-paper formalization, not for the
completed TeX addition. Repair: prove the selected-position interface, inherited
cleanliness, fresh-leaf and positivity laws, then the actual blocked reductions.
Do not substitute rank bounds for an arbitrary returned normal form.

## (C) Minor issues

The first rendered layout split Appendix C across pp.11–12. A clear page before
its heading now keeps both paragraphs on p.12, followed by the unchanged
disclosure. Evidence: final PDF rendering. This local layout issue is resolved;
the supplied mathematical wording is unchanged.

## (D) Cross-section consistency failures

No additional inconsistency was confirmed. The p.260 direction agrees with a
strict predecessor-rank decrease and an unchanged opposite premise. The p.262
qualification agrees with the analogous p.261 passage and positivity of both
one-sided ranks. The selected fresh logical occurrence has rank one; an exchange
wrapper above that rule would require its own adapter accounting, which the
external Lean ledger keeps open.

All ten diagrams, Appendices A–B, the accepted disclosure and bibliography retain
identical source. V7 is the preserved v6 mathematics plus Appendix C; the three
milestones and whole-paper endpoint are not conflated. Existing-arrow witnesses
for zeros, empty hom-sets, occurrence tags and composition conventions are retained.
The source/PDF hashes and active records agree with the local build evidence.

## (E) Acceptance conditions, non-negotiable

1. Retain exact supplied wording and roadmap, with resolved DP and appendix
   references. Verified in the final source and rendering.
2. Preserve the six older manuscript blobs, disclosure and diagrams. Their
   hashes/source comparisons pass.
3. Build and inspect the actual v7 PDF; keep Appendix C in the specified order.
   The final thirteen-page PDF passes the recorded local checks.
4. Keep new concrete Lean correspondences open until proved. Current claim
   rows distinguish these from the completed manuscript addition.
5. Commit and deliver the actual checked bytes, with conflict-preserving copy
   verification. The subsequent delivery receipt supplies that separate status.

Failure of the first three conditions would invalidate completion of the bounded
addition; failure of the fourth would invalidate its formalization status.

## (F) Not checked / uncertainty log

Read the complete supplied addition, surrounding roadmap/appendix/disclosure
passages, source diff and active claim/correction records. The unchanged v6
mathematics retains its previous reviews; no fresh correctness or novelty verdict
on every theorem is asserted. The primary source pages were visually checked.
The final TeX build, warnings, labels, checksums and all-page layout were inspected;
no independent Lean replay, Comparator, registry or publication operation occurred.

Strongest confirmed blocker to whole-paper formalization: global elimination
and the new concrete blocked-rank correspondences remain open. Strongest suspected
unconfirmed defect in the appendix: none established. Most important unchecked
result: the assembled blocked cut reductions in Lean. Recommendation: unknown
for whole-paper certification; the bounded manuscript addition satisfies its
local checks. Committed-byte delivery is certified only by its later receipt.
