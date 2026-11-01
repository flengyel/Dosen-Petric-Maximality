# (A) Kill-shots / hard blockers

Author-side AI-assisted audit of the author's arXiv draft, using the
HostileRefereeGPT — Cat/Rec plugin. This is not independent peer review.
Input: manuscript v13 at 50d613e, 964 source lines, 14 PDF pages.
Output inspected: manuscript v14, 14 pages. The exact source identities and
diff are in provenance/manuscript-v14-review-20261101/.

No fatal mathematical blocker was established. The main theorem's hypotheses,
the occurrence-selection construction, both projection-equality arguments and
the model corollary were examined. The requested exposition defects below do
not establish a false theorem or an ill-typed composite. Every item records
its input anchor and the implemented disposition.

# (B) Major weaknesses

No major mathematical weakness was established in this audit. In particular,
the main proof uses the particular isomorphisms q_A and e_A in the original
category, and uses their inverse equations in the quotient. It never applies
Boolean Coherence in the quotient. The added detail in the alternative proof
explains deductions already present in the retained Lean source; it introduces
no new hypothesis or formal proof obligation.

# (C) Minor issues

## C1. The abstract names an equation without stating it

Anchor: v13 PDF p.1, abstract; source lines 31–38, “a contextual equation on a
signed literal.” Failure mode: ambiguous exposition. Evidence: absence_in_text
in the abstract, with the equation supplied later in Section 4. The summary
also attributes the passage from a negative literal to arbitrary A simply to
substitution, although the body uses double-negation isomorphisms.

Repair: v14 states the equation between the projection followed by the injection
and the zero arrow, and names both uniform substitution and double negation.
The definition of a zero arrow remains conditional on an existing arrow.
Impact: the reader can identify the reduction without supplying a meaning for
“contextual.” Severity: minor; resolved without changing the theorem.

## C2. The name of d does not follow the cited presentation

Anchor: v13 PDF p.2, Section 2, source line 155, “The distributor is an arrow”;
parallel occurrences occur on p.7 and p.12. Failure mode: inconsistent_use of
source terminology, not an established typing error. Evidence: citation.
Došen–Petrić, Proof-Theoretical Coherence, September 2007, printed p.234
(PDF p.246), calls these dissociativity arrows and gives their type.

Repair: use “dissociativity arrow” throughout, including the generator list, retaining
d:A∧(B∨C)→(A∧B)∨C and its first-injection equation. This does not rename or
alter a Lean declaration, nor assert that d is invertible. Impact: avoids
suggesting the usual distributivity map to (A∧B)∨(A∧C). Severity: minor;
resolved by matching the source's defined structure.

## C3. Several arrow actions and comparisons leave endpoints implicit

Anchors: v13 PDF pp.2–5, Section 2 lines 151–170, Section 3 lines 260–261 and
365–374; PDF p.5, Lemma 4.1 proof lines 410–412; PDF p.7, model discussion
lines 576–595. Failure mode: ambiguous exposition. Evidence: structural_argument.
The objects and operations are already defined; no ill-typed expression was
exhibited. The omitted information has to be reconstructed during composition.

Repair: v14 gives the endpoint types of f∧g and f∨g, the contravariant action
¬f:¬C→¬A, Gf⊆Occ(A)×Occ(C), f[σ]:A[σ]→C[σ], and both normal-form witnesses
and their composites. It names I_v:B(P)→C for v:P→Ob(C), and writes the
valuation p↦I_v(σ(p)) inducing I_v∘F_σ. The negative-literal proof names its
precomposition and postcomposition explicitly. Severity: minor; resolved.
The ten existing typed diagrams are preserved byte-for-byte.

## C4. The alternative proof suppresses two computations

Anchor: v13 PDF p.8, Section 6, source lines 633–650:
“K_A and Boolean Coherence … give” and “using the first-injection equation.”
Failure mode: unproved intermediate calculation in the compressed exposition.
Evidence: derivation and source correspondence, not a counterexample.
The main proof in Section 5 is independent and already supplies the theorem.

Repair and checked derivation:
- Define v_A:A∧A→(A∧⊥)∨A. Copairing and K_A give
  j_A h_A ≡ [0,j_A]v_A. In the original category, the latter relation contains
  exactly the pairs from the second source copy to the A target summand, so
  coherence gives j_A π₂.
- Keep the precomposition yielding equal injected projections and the
  precomposition with ⟨1_A,0_A⟩ yielding j_A≡ι₂!_A.
- Display 1_(A∨⊤)≡ι₂!_(A∨⊤) and !_(A∨⊤)ι₂=1_⊤, which establish terminality.
- Define w_A:A∧A→A∧⊤. Substitution of the second-injection equation into the
  expression with B=⊤, followed by the first-injection equation and the product
  equation, gives h_A≡π₁. Symmetry then equates the projections.

These are the deductions in ContextualCollapse.second_block,
terminal_injection, terminal_retraction, other_injection, fold_top and
equal_projections in DosenPetric/Collapse.lean. The displayed mix identification
agrees with DosenPetric/PresentationSymmetricFold.lean. No source proof was
edited or rebuilt. Severity: minor in a paper whose main proof is complete;
the alternative proof's exposition is now explicit.

## C5. Names add an avoidable layer between the reader and defined functions

Anchors: v13 PDF p.10, Appendix A.2, lines 777–809, “block encodings” and
“block locator”; p.11, line 836, “target encoding”; PDF p.2, Section 1,
lines 100–101, the list of source-specific category names. Failure mode:
ambiguous exposition and unnecessary terminology. Evidence: absence_in_text
for explanations of the named external axiom systems, and the displayed
definitions of θ_D, θ_C and the unique block index.

Repair: describe consecutive numbering by the two explicit bijections, specify
the unique r with s_(r−1)<x≤s_r, refer to θ_C by its name, and state the
proof-net comparison without importing its unused axiom-system names.
Appendix A now calls its explicitly defined functions occurrence maps rather
than introducing “profiles,” and states that their values are placeholder
indices after enumeration. The source's technical terms needed for the
argument, including zero identity, mix, coherence and skeleton, retain their
definitions or citations. Severity: minor; resolved.

# (D) Cross-section consistency failures

No discrepancy in literal signs, composition order, equality notion or diagram
endpoints was established. The term “signed literal” was redundant with the
definition p or ¬p; it has become “literal” throughout the revised manuscript.
Both signs remain in the isolation lemma and the separate negative-substitution
case. Removing the word does not remove its sign.

The phrases “actual” and “genuine” were already absent from v13. The audit does
not claim to have removed occurrences that were not there. Their absence was
checked again in v14. Mathematical qualifications, including structural
induction on a specified formula and the empty-set cases, remain.

The previous v13 review's correction of the negation-free hypothesis in the
Lemma 6 comparison is retained. Its counterexample is not downgraded or
reintroduced. Earlier literature comparisons and both source errata remain.

# (E) Acceptance conditions, non-negotiable

These are completion conditions for this revision, not a journal decision.

1. Deliver the explicit calculations and types in C1–C4. Failure would leave
   the requested exposition repair incomplete; it would not alone refute the
   independently proved main theorem. Completed in v14.
2. Preserve hypotheses, quantifiers, both proof routes, all defining displays
   and all diagrams. Failure would prevent describing the release as an
   exposition revision. Seven statement bodies agree after the literal synonym
   and lemma-caption normalization; 12 numbered displays, ten diagrams and
   30 labels are byte-identical.
3. Compile the revised manuscript and the separately extracted four-file
   archive, resolve warnings and inspect the render. Failure would prevent a
   claim of a prepared arXiv package. Both compile to matching 14-page layout
   text; final logs have no citation/reference or box warnings.
4. Preserve v13, earlier releases, registered sources, author disclosure, the
   supplied Palomar BibTeX and the stash. Completed; source/preservation
   evidence is recorded separately.
5. Keep all review and revision reporting outside the manuscript. Completed.

# (F) Not checked / uncertainty log

The complete v13 source was read, followed by the complete revised source and
the rendered v14 pages. All 14 pages were inspected on four contact sheets;
the expanded proof on p.8 was also inspected as a full page. The seven
numbered claims were checked as follows.

| Claim | Hypotheses and checked argument |
| --- | --- |
| Theorem 2.1 | P≠∅; a congruence invariant under uniform substitution equating distinct parallel arrows. Lemma 4.1 supplies a literal equation, Proposition 4.2 supplies K_A for every A, and Lemma 5.2 makes the congruence total. |
| Boolean Coherence, Theorem 3.1 | The original equation-presented category and its occurrence functor. The statement agrees with the cited published result; its full cut-elimination proof was not reproved in this editorial audit. |
| Lemma 4.1 | Distinct parallel arrows. Faithfulness gives a differing pair; normal forms preserve its literal; the inductively constructed i and r have singleton relations. Original coherence proves both equations, including the zero alternative. |
| Proposition 4.2 | The congruence is invariant under substitution. The positive case substitutes A; the negative case substitutes ¬A and composes with double-negation isomorphisms at the displayed types. |
| Lemma 5.1 | P is the fixed nonempty variable set. The cited isomorphisms for p and the two-element permutation argument identify the particular q_p and e_p; substitution preserves their inverse equations for arbitrary A. |
| Lemma 5.2 | K_A for every A, with a congruence preserving the arrow operations. The q inverse makes A∨⊤ terminal; the e inverse makes π₁ invertible; its diagonal inverse equates π₁ and π₂. Pairing equates arbitrary parallel arrows. |
| Corollary 5.3 | P≠∅ and equality under all interpretations in C. The all-interpretation relation is preserved by operations and by substitution through I_v∘F_σ. Assigning an arbitrary target object to p gives equal target projections; pairing equates arbitrary target arrows. |

Small-case checks included empty occurrence sets, repeated equal labels,
negative literals and noninjective renaming. The two-object one-arrow category
is a check against inferring arrow existence from an empty relation:
a faithful functor need not be full. The manuscript never uses faithfulness
to fill an empty hom-set; its zero arrows have existing-arrow witnesses.

The ten diagrams were checked at their displayed endpoints. Appendix A's
coordinate equation has the same prefix sums, index bounds and eight worked
outputs; intervening empty blocks contribute no source position. Appendix C's
two source-rank corrections are unchanged.

This is not a fresh Lean/kernel replay, a complete re-audit of every cited
publication, an exhaustive novelty search or an independent peer-review verdict.
Došen–Petrić's relevant presentation and equation passages, and the retained
Lean deductions used in the expanded proof, were inspected. Other unchanged
literature claims retain the documented v13 review scope.

Strongest confirmed blocker: none exhibited. Strongest suspected but
unconfirmed blocker: none exhibited. Most important unperformed check:
independent reproof of the published coherence theorem. A publication
recommendation also depends on expertise and literature assessment beyond this
audit. Final recommendation: unknown; the requested exposition repairs are
complete, and no mathematical rejection ground was established here.

