# (A) Kill-shots / hard blockers

1 November 2026. Author-side AI-assisted audit using HostileRefereeGPT — Cat/Rec.
Subject: the author's manuscript v15 compared from the Lean development back
to the paper, at f869fe74e9cc713ad366b51fad16d5de357fe74a. This is not
independent peer review. The accompanying report gives exact proposed
mathematical wording; it does not release a revised manuscript.

No false central theorem, missing Lean proof or fatal correspondence defect
was established. The formalization has results that the paper does not state.
Their absence does not refute a theorem that the paper proves by another
argument or through a precise published citation.

# (B) Major weaknesses

No major correctness blocker was established. In particular, Lemma 5.1's
existing proof cites isomorphisms of the required types, uses coherence to
identify the particular arrows, and substitutes arbitrary A for p. The fact
that Lean constructs inverses directly is a reason to improve self-containedness,
not evidence that the cited proof is absent.

The paper does not claim that it prints every theorem in its development.
Accordingly, the omitted structures below are assessed as opportunities to
state mathematical content and explain the formal proof, not as unsupported
claims that such content is already in the text.

# (C) Minor issues

## C1. Substituted relations are described only at their endpoints

Anchor: v15 PDF p.5, Section 3, “For each arrow, the blocks ... describe the
occurrence sets of its substituted source and target”; Appendix A, pp.9–11.
Failure mode: ambiguous exposition if this is read as the whole-arrow
substitution theorem. Evidence: absence_in_text plus direct source statement.
Presentation.occurrence_substitute_expanded describes every edge, using the
labelled dependent blocks. The endpoint statement is true but weaker.
Downstream impact: the relation-level compatibility with composition remains
unexplained. Severity: minor exposition omission. Repair: report R1 supplies
the typed relation, the equality in E_sigma, the commutative square and the
constructor-induction proof. This proposal is not yet inserted into v15.

## C2. The explicit isomorphism witnesses are mentioned but not displayed

Anchor: Lemma 5.1, PDF pp.6–7; Section 6, p.9, “with explicit inverses for
q_A and e_A.” Evidence: absence_in_text and derivation in ShortProof.qInverseTerm
and eInverseTerm. Failure mode: ambiguous exposition only in the sense that
the reader must open Lean to see the explicit construction being described.
The lemma itself has a cited proof, so this is not an unproved result.
Severity: minor; repairable by the typed witnesses and four inverse equations
in report R2. The zero in the second inverse has the explicit existing-arrow
witness Delta_A composed with pi_1:A∧top→A∧A.

## C3. Mathematical structure used in the coherence implementation is unreported

Anchor: Section 6, PDF pp.8–9, and Appendix D, pp.13–15.
Evidence: absence_in_text and the source declarations identified in report
R3–R7. Failure mode: missing_definition only if the omitted operation union
were used in the paper; it presently is not used. No error follows from
its absence. The issue is completeness of the requested account of what the
formalization contains. Severity: minor editorial opportunity.

The following facts were checked rather than inferred from filenames:

| Content | Exact mathematical boundary |
| --- | --- |
| Union | Reduced.union is associative, commutative and idempotent, has witnessed zero as identity, and composition distributes over it. Its relation is binary union. Transfer to B(P) uses the proved reduction/recovery maps; there is no separately named Presentation.union declaration. |
| Substitution action | Identity/composition/extensionality include the formula equalities transporting arrow endpoints. They differ from each individual functor's preservation of arrow composition. |
| Retracts | context_retract needs one inverse equation r∘i=1_A; the printed double-negation argument is a special case. |
| Signs and negation | Signed labels are preserved at arbitrary formula endpoints; G(neg f) is the converse of Gf at the original occurrence tags. |
| Coherence architecture | Distributive comparisons split in the specified direction; DNF/CNF expansions are retracts, not two-sided isomorphisms. Pure positive normal forms use finite unions; common atomic factorization transfers positive coherence. |

## C4. Extra consequences must retain their evidential status

Anchor: report's “Further consequences and deliberate scope.” Evidence:
derivation, not a new compiled theorem. Constant substitutions suffice in
the all_contexts argument; empty P gives empty occurrence sets and hence a
thin category; finite occurrence sets plus faithfulness bound each hom-set.
The report explicitly separates these deductions from named Lean statements.
Calling them separately registered or newly implemented would be
unsupported_generalization/irreproducible. That claim is not made.

# (D) Cross-section consistency failures

No unresolved contradiction between the paper's seven numbered claims and
the inspected formal interfaces was established. Checked correspondences:

- Theorem 2.1 uses isolation, substitution to every K_A and collapse. The
  library also has fragment maximality; Appendix D already explains that
  preservation under negation follows after the fragment dichotomy.
- Theorem 3.1 is Presentation.coherence, transferred through actual reduced
  and positive coherence. The auxiliary GeneratedModel is a separate relational
  construction and is not treated as this equation-generated presentation.
- Lemma 4.1 uses normal-form transport and original-endpoint selectors;
  Proposition 4.2 has both signs and the double-negation transport. Neither
  is an omission in v15.
- Lemma 5.1 has the particular q_A/e_A, not merely arbitrary arrows of
  isomorphic types. Lemma 5.2 uses their inverse equations and quotient
  products/coproducts. Their explicit source witnesses are report R2.
- Corollary 5.3 quantifies over all interpretations and uses native target
  products on arbitrary target arrows. Universal agreement, rather than one
  fixed kernel, supplies substitution closure.

The proposed relation R_(f,sigma) compares (label,inner occurrence) pairs
in E_sigma. This prevents an ill-typed equality between unrelated fibres.
It preserves repeated old occurrences and handles empty blocks. The union
proposal requires a witness for its empty finite union. The quotient
preserves empty hom-sets. The two-object category with its single nonidentity
arrow A→B is a check against inferring an arrow B→A from thinness or zeros;
none of the proposals makes that inference.

The retained atomizer and terminal-replacement counterexamples refute
particular implementation candidates. Their statements and reports do not
refute the existential reducibility result or establish a third published
source erratum. Appendix C remains unchanged.

# (E) Acceptance conditions, non-negotiable

These conditions concern the audit deliverables, not a journal acceptance.

1. Supply a reverse inventory outside the five selected imports. Completed:
   850 modules are inventoried, including the 95 outside that import closure.
   Failure would invalidate a claim to have checked the broader development.
2. Distinguish absent text from an absent proof, and named results from
   transferred/derived consequences. Completed in the report and finding
   records. Failure would require withdrawing the affected conclusion.
3. Give typed statements and actual source/manuscript anchors for proposed
   additions. Completed for R1–R7. Failure would make an addition unreviewable.
4. Preserve frozen source, prior releases and the stash. Checked separately
   in provenance. No new manuscript revision is presented as built or released.
5. Record source-reading limits, retain the report and both reviews, deliver
   committed-byte copies and synchronize authorized main. Scope is stated
   here; delivery and push are recorded separately. Failure of delivery or
   push must be reported, not represented as completion of that stage.

# (F) Not checked / uncertainty log

The complete v15 manuscript and the module/declaration inventory were compared.
Detailed source reading covers the mathematical entry points and candidate
results listed in the scope record. The inventory/import analysis accounts
for all modules; it is not an independent line-by-line proof audit of all
719 Gentzen support files. Reusing the previously successful kernel and service
checks is not a new verification claim. No build or verification was rerun.

No revised manuscript PDF was built. V15's prior successful build and visual
inspection apply to its preserved bytes. Proposed wording in the report has
been checked for types and deductions, but not released as v16. No exhaustive
new literature/priority search was performed. The book passages on union were
checked; no novelty is inferred from their absence in this paper.

Self-audit: strongest confirmed blocker, none exhibited. Strongest suspected
but unconfirmed mathematical blocker, none exhibited. Most important thing
not checked: an independent proof-term review of the complete coherence/cut
development. A publication recommendation would require expertise and checks
beyond this reverse content audit. Final recommendation: unknown; the report
establishes omitted mathematical content without establishing an error in the
main theorem or a missing Lean proof.
