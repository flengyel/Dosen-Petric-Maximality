# (A) Kill-shots / hard blockers

1 November 2026. Author-side AI-assisted audit using HostileRefereeGPT — Cat/Rec.
Input: v14 at 9e46cdca7f2fe2f59983ecf324e08a80ad09c81a; output: v15,
16 pages. This review checks Appendix D and its correspondence to the existing
Lean source. The exact comparison verifies preservation of the remaining
v14 argument, whose prior review remains in force. This is not independent
peer review or a new kernel replay.

No fatal blocker was established. Each of the five stated propositions agrees
with its selected declaration. In particular, generated equality is not replaced
by the kernel of an interpretation, and neither totality nor a zero arrow is
used to infer that an empty hom-set has an element.

# (B) Major weaknesses

No major mathematical weakness was established. The principal possible
failure was a circular argument about negation: PrimitiveCongruence does not
assume preservation under negation. Appendix D.2 applies maximality to the
composition/pairing/copairing fragment. D.3 then uses the dichotomy to obtain
negation preservation, since equality and totality each preserve every arrow
operation. This agrees with Presentation.fragment_maximality and
ProofCongruence.of_closed_fragment. No full-congruence assumption is smuggled
into the fragment proof.

The model corollary is correctly identified as an additional result. The appendix
does not assert that it is a dependency of the five selected entry points.

# (C) Minor issues

## C1. The substitution quantifiers must remain distinct

Anchor: D.1 substitution square, PDF p.13; D.3 first paragraph, p.15.
Evidence: source typing and derivation. Term substitution allows
σ:P→Form(Q), whereas R.Closed concerns a relation over P and permits
σ:P→Form(P). Applying that relation after arbitrary change of variable set
would be ill-typed. The final text explicitly restricts the latter square to
Q=P. Disposition: resolved; no such assertion remains in the release.

## C2. Long code identifiers exceeded the margin in a preliminary render

Anchor: D.3 final paragraphs, PDF p.15; preliminary LaTeX logs.
Evidence: rendering, not a mathematical defect. The final text separates
the two theorem correspondences from the collapse correspondences, states
the common namespace once, and permits line breaking at namespace separators.
Disposition: resolved; final manuscript and extracted-package logs have no
box warning, and the full page was inspected.

## C3. One new claim-map identifier required correction

Anchor: the new Appendix D row in MANUSCRIPT_COMPLETE_CLAIM_MAP.md, concerning
the symmetric fold. Evidence: direct declaration lookup. A draft row used
the nonexistent name Presentation.symmetricFold_eq_fold. It now names the
existing Presentation.fold_manuscript and Presentation.fold_symmetric.
The manuscript itself did not contain the erroneous identifier.
Disposition: resolved before release; the equations were checked in
PresentationSymmetricFold.lean and Collapse.lean.

# (D) Cross-section consistency failures

No unresolved inconsistency was found. The following correspondences were checked.

| Appendix statement | Checked hypothesis, type and conclusion |
| --- | --- |
| D.2 maximality | P nonempty; primitive R, Closed, parallel f,g, R f g and not Derives f g; concludes Total by the symmetric-fold route. |
| D.2 short_maximality | The same type; literal isolation and all_contexts feed ShortProof.total. It is the q_A/e_A route of Section 5. |
| D.2 congruence_dichotomy | P nonempty and Closed; R=Derives pointwise or Total. Induction on Derives gives the included relation. |
| D.2 identity_ne_zero | Given p:P, id_p and primitive zero are not Derives-related. Presentation.zeroConstruction_eq identifies that zero with equation (2). |
| D.2 no_top_to_bot | Every P, including empty; no term top→bot. Truth assigns True to every variable and Term.preserves_truth rules out such a term. |
| D.3 descent and pullback | Derives⊆R gives representative independence; quotientRel_ofTerm, fragment_closed, ofFull and the totality equivalences give the stated relations. |

Composition in Lean applies f and then g, as the appendix explicitly states.
The new square has endpoints over Q after substitution. The relation R is
typed only on parallel terms. Pairing and copairing preservation follows from
comp/tensor with fixed diagonals/codiagonals. The inequality 1_p≠0_p is an
equality question in the original category; coherence is not applied in a
collapsed quotient. The existing Section 6 computations match second_block,
fold_top and terminal_retraction after the fold_manuscript identification.

The earlier v14 review's C4 now explicitly calls its issue an omitted written
calculation and records the existing Lean proofs. An exposition omission does
not establish an unproved formal claim. No such claim is made here.

# (E) Acceptance conditions, non-negotiable

These are author-side completion conditions for the requested appendix.

1. State all five selected types with their quantifiers and distinguish terms
   from quotient arrows. Completed in D.1–D.2 and checked against the declarations.
2. Explain representative independence, self-substitution closure and the
   direction of the negation argument. Completed in D.3; no circular assumption.
3. Preserve the preceding mathematics and frozen proof inputs. The exact
   inverse text comparison, seven statement bodies, twelve numbered displays,
   ten prior diagrams, thirty prior labels, 83 release files and 856 registered
   proof/input blob identities pass their preservation checks.
4. Build and inspect the manuscript and independently extracted upload archive.
   Both have matching 16-page layout text and no final warnings. All pages
   were inspected, including D.1–D.3 individually.
5. Keep credentials, private service material and review-process narration out
   of the manuscript and public proof inputs. No private material is used or
   staged; the manuscript adds only mathematical exposition and its code references.

# (F) Not checked / uncertainty log

The new appendix, its pointer and current correspondence map were examined
against the retained source. Preservation checks cover the unchanged v14 text;
this is not a fresh independent reproof of every old statement. No new literature
claim is introduced. The prior v14/v13 citation-review limits remain unchanged.
The governing writing source and Došen–Petrić source comparison are documented
in the writing review and earlier source record.

All sixteen pages were inspected on four contact sheets. Pages 13–15 were
also viewed individually. No clipping, diagram collision or unreadable code
reference was found. The independently extracted archive's layout text agrees.

No Lean/kernel replay, Comparator run, preflight, service verification or
registration was repeated. Previously successful statuses are preserved, not
reported as newly performed. Independent reproof of the published coherence
theorem and an exhaustive priority assessment are outside this appendix task.

Self-audit: strongest confirmed blocker, none exhibited; strongest suspected
but unconfirmed blocker, none exhibited. Most important unperformed mathematical
check: an independent reproof of the full coherence argument. The five entry
points do not delimit the complete Lean development. Final recommendation:
unknown; no rejection ground was established in the added exposition, and
the stated completion conditions are met subject to the separately recorded
delivery and remote synchronization.
