# Local hostile review: complete paper and exact Appendix A

Scope: actual manuscript v7, the v8 status/citation refresh, the complete claim
map and the actual Lean dependency closure. This is an author-side review, not an
independent replay or an external referee report. Whole-paper mathematical scope
is locally complete subject to the immutable final verification/delivery record;
independent verification and publication are separate statuses.

## (A) Kill-shots / hard blockers

No confirmed mathematical blocker remains in the checked argument. The actual
main theorem and model corollary have no uninstantiated source/coherence/handler
inputs. Twenty-two final modules close the remaining action, profile, ordinal,
renaming, reconstruction and unnumbered-consequence obligations. The v8 scope
claim is accepted only together with the complete claim/dependency map and final
strict audit, not from maximality alone.

## (B) Major weaknesses

1. **unsupported_generalization; high; evidence: structural_argument.** Anchor:
   `PatternSubstitutionOrdinals.lean`, `chiInverse_encoding`, “exactly the actual
   left-to-right occurrence index”. Merely choosing a finite bijection would not
   identify the book's ordinal operation. Resolution: `Formula.substitution_count`
   and `substitution_index` prove actual counts and prefix offsets; the encoding,
   actual ordinal square, composite profile and skeleton reconstruction follow.
   Downstream: the whole Appendix A/book correspondence is supported.
   Repairability: resolved in source.
2. **ill_typed; high; evidence: structural_argument.** Anchor:
   `PresentationSubstitutionActionQuotient.lean`, `substitute_composition`,
   “transportHom”. Directly equating the two substitution actions would suppress
   different endpoint expressions. Resolution: raw HEq induction covers every
   constructor, and quotient equalities explicitly transport both endpoints by
   the proved Formula action equations. Downstream: no type identification is
   assumed. Repairability: resolved; a focused control rejects the omission.
3. **inconsistent_use; high; evidence: citation.** Anchor: v8 Formalization
   bibliography item, “revision”. The inherited early revision lacks the new
   proofs supporting the refreshed status text. Resolution: cite the immutable
   completed mathematical-source commit and rebuild/inspect v8. Old versions
   retain their historical reference. Downstream: reproducible correspondence
   between paper and proof source. Repairability: resolved by final citation
   record FP-CITATION-20261029, not by a self-referential commit claim.

## (C) Minor issues

**ambiguous; medium; evidence: structural_argument.** Anchor:
`PatternSubstitutionProfiles.lean`, `chi`, “choice merely names its proved unique
inverse map”. The inverse is explicit and both inverse laws are proved; chi need
not be executable for the manuscript's bijection statement. The report makes this
status clear. No unsupported computational claim is made.

**missing_definition; medium; evidence: structural_argument.** Anchor:
`CongruenceQuotient.lean`, `quotientStructure`, “beta/eta equations”. The printed
proof says products and coproducts pass to equivalence classes. Actual quotient
hom-sets, composition, structure, universal equations, zero identity and the
thin/total equivalence are now supplied, rather than leaving this solely as
congruence shorthand. The empty-hom preservation theorem prevents zero arrows
from creating missing arrows. Resolved.

## (D) Cross-section consistency failures

The final sweep matches the stated p⇒p obstruction, not only a different
exponential sufficient to disprove closure. `ExponentialGlobalPoints` proves the
printed hom-set/global-point bijection. Fixed-other-variable substitutions and
both signed context types match Proposition 4.2; the exact double-negation
rectangle is named. The finite-relation functor has explicit finite coordinates.
All ten diagrams, three appendices, both source errata and both maximality routes
remain present. The symmetric-fold route is labeled an alternative in v8.
All older open statuses are retained as dated checkpoints, superseded by the
current complete map. No target coherence or fixed-kernel closure is used.

## (E) Acceptance conditions, non-negotiable

1. Strict pinned source/build/transitive axiom audit must pass for all 883 files.
2. All 35 public checks, both boundaries and all 74 rejections must pass.
3. Every numbered/unnumbered mathematical claim and displayed identity must be
   mapped to actual declarations, with all published inputs instantiated.
4. Preserve v4–v7, all mathematical text, all appendices and ten diagrams; build
   and inspect v8, including the corrected immutable citation.
5. Compare archived, checked and committed bytes; push without force; deliver all
   reports/reviews/artifacts from committed bytes and verify conflicts/copies.
6. Preserve the original stash, unrelated checkouts and prior proof/evidence.

The final immutable evidence records each condition. No independent or service
status may be inferred from these local checks.

## (F) Not checked / uncertainty log

Independent kernel replay, Comparator, official preflight, service verification
and publication were not performed. Literature priority beyond the accepted
manuscript references was not independently reassessed. The complete cached book
§2.5 formula and the governing Mathematical Writing source were consulted; no
unavailable external review is reported as done. The proof uses core Lean only.

Strongest confirmed issue was the stale citation anchor, repaired in v8 and its
linked records. Strongest suspected mathematical failure mode was an arbitrary
finite coordinate choice; the actual substitution-index theorem closes it.
Recommendation: accept complete local mathematical formalization if the final
recorded checks, claim map and delivery verification pass. Independent
verification and publication remain outstanding statuses, not proof holes.
