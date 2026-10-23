# (A) Kill-shots / hard blockers

No fatal defect was established in the current mathematical argument. This is an author-side hostile audit, not independent peer review. The complete v5 TeX was read; the core proof was checked against its types, equations, and cited presentation. All ten PDF pages were inspected across the review, with separate detailed checks of the proof and appendix. The full PDF text was read.

Reviewed source: `url-v5/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex`, SHA-256 `1e828807a1351be5aba3d446a6e275c6699d23c9fbdde73ea0d121fac054e2e2`. The review concerns the source at commit `cfa37604e539dc85d854959b20aca752d06774ce`. PDF SHA-256: `482b75840f70d9808ecc213dbb66cc8ec19a277ad2d14e859375aae449537906`. Date: 23 October 2026. The explicitly requested [hostile-review plugin](skill://plugin_867af61c251c819194f29c5c462eafbe/instructions/SKILL.md) was applied. No manuscript text was changed during the initial review; the authorized revision is assessed in the final follow-up below.

The main theorem is a statement about the specified Došen–Petrić category and substitution congruences. It does not assert that every arbitrary congruence collapses the category. Its use of published Boolean Coherence is explicit. The unfinished Lean reconstruction of that published theorem does not supply a counterexample to the manuscript's argument.

# (B) Major weaknesses

No major weakness was established in Sections 2–5. The following audit records what was checked, rather than replacing absent findings with speculative defects.

| Manuscript anchor | Claim and explicit hypotheses | Typed check and proof sketch | Status |
|---|---|---|---|
| §2, pp.2–3, lines101–167, equations (1)–(3) | The specified freely generated zero-identity Boolean category has the stated distributor and witnessed zero arrows. | The zero composite starts at `A`, passes through `A∧top`, `A∧(¬A∨A)`, `(A∧¬A)∨A`, and `bot∨A`, and ends at `A`. For an existing `f:A→C`, `(0I)` makes `f∘0_A` independent of the chosen witness. Composition supplies witnesses at every endpoint used in the absorption laws. | Well typed. The source's §14.2 p317 and §14.3 p322 agree with this presentation. |
| §3, pp.3–4, lines224–256, Theorem3.1 | `G:B(P)→Rel_fin` is faithful. | This is cited as the published Boolean Coherence theorem, not proved from the new maximality theorem. The manuscript uses its relational coordinates for identities, composition, projections, injections, pairing, copairing, and the distributor. | Published input identified correctly at §14.2 p321. |
| §3, p.4, lines258–273 | An arrow between negation normal forms preserves signed literal labels along every edge. | Normalization compares arbitrary formulas with signed-literal formulas by isomorphisms. In the reduced presentation, the positive structural primitives preserve each literal label; zero endomorphisms and atomic `η,ε` have empty relations. Both tensors and composition preserve this property. The reduced/full comparison preserves occurrence coordinates. | The reduced category and comparison are present in the cited pp.318–321; no new coherence assumption is smuggled into the manuscript. |
| §3, p.4, lines279–327, equations(4)–(5) | Substitution gives occurrence blocks and a functor `F_σ:B(P)→B(Q)`. | The block set consists of `(x,t)` with `x` an occurrence of the old formula and `t` an occurrence of its substituted formula. The two paths in the square map `(x,t)` to `λ_A(x)`. Substitution respects defining equations by the stipulated substitution rule; it acts on the entire typed arrow term. | Correct. The square is expressly one of sets and functions; `P` and `E_σ` need not be finite. |
| Lemma4.1, p.5, lines344–400 | Distinct parallel arrows admit a signed-literal selector and coselector isolating one differing edge. | Conjugating by `a_A,a_C` is invertible and preserves distinctness. A differing edge has a common signed literal `ℓ`. The fillers `κ_V∘π₂:ℓ∧bot→V` and `ι₂∘!_V:V→ℓ∨top` exist independently of arbitrary zero hom-sets. Recursion through conjunction and disjunction retains exactly one tagged edge. Composing the selector and coselector with the original arrows yields singleton and empty relations, hence the two stated equations by coherence. | Complete at the paper's level of detail. All endpoints agree. |
| Proposition4.2, pp.5–6, lines402–434 | A substitution congruence identifying distinct parallels satisfies every contextual equation `K_A`. | Composition transports the new equation to `K_ℓ`. For `ℓ=p`, substitute `A` for `p`. For `ℓ=¬p`, substitute `¬A` and transport the resulting `K_{¬¬A}` by `n_A^{-1}∧1_bot` and `n_A∨1_top`. Their composite with the nonzero side equals `K_A`; absorption transports the zero side. | Substitution closure is used precisely here. No cancellation of injections or quotient faithfulness is used. |
| Lemma5.1, p.6, lines442–465 | `h_A^B:A∧A→A` is independent of `B` and symmetric. | `u_A^B` sends the first `A` block to the `A` component of the left coproduct summand and the second block to the right summand. Copairing folds these to the same `A` coordinate. Thus the relation is the fold from two tagged copies, independent of `B` and invariant under swapping them. Coherence applies to parallel arrows in `B`. | Correct, including empty occurrence sets and repeated equal labels. |
| Lemma5.2, pp.6–7, lines467–544 | A proof congruence satisfying all `K_A` makes the quotient thin. | Copairing and `K_A` give `j_Ah_A≡j_Aπ₂`; symmetry gives `j_Aπ₁≡j_Aπ₂`. Precompose with `〈1_A,0_A〉` to obtain `j_A≡ι₂!_A`. Coproduct uniqueness then makes `A∨top` isomorphic to `top` in the quotient, so `top∨A` is terminal. Reevaluate the same `h_A` with `B=top`, replace its second injection by `ι₁!_A`, and apply equation(1), obtaining `h_A≡π₁`. Symmetry gives `π₁≡π₂`, and pairing gives equality of every parallel pair. | All equalities and congruences have the indicated status. Products and coproducts descend because their operations and equations descend. |
| Theorem2.1, p.3; proof p.7, lines546–551 | For nonempty `P`, every nonidentity substitution congruence on `B(P)` is total. | Lemma4.1 and Proposition4.2 establish the hypotheses of Lemma5.2. Nonempty `P` also supplies a generator whose two product projections have different relations, establishing that the starting category is nonthin. | Follows from the preceding results. |
| Corollary5.3, p.7, lines553–577 | If a zero-identity Boolean category satisfies a new equation under every interpretation, it is thin. | The intersection of interpretation kernels is a proof congruence. Composing an interpretation with an endosubstitution proves substitution closure. Theorem2.1 gives equality of the two projections on `p∧p`. Interpreting `p` as arbitrary `X` gives equal projections on `X∧X`; pairing arbitrary `Y→X` arrows proves thinness. Other generators can be interpreted by any fixed object, for example the specified terminal object. | Quantifier “every interpretation” is essential and retained. No fullness of an interpretation is assumed. |

Edge-case tests:

- Empty hom-sets are not silently populated. All nonendomorphism zeros used have explicit existing-arrow witnesses.
- If a formula has no variable occurrences, its relevant relation is empty; the collapse proof remains valid. A differing edge in Lemma4.1 cannot occur at an empty endpoint, as required.
- Repeated occurrences of the same literal remain separate through tags. The relation of `h_A` identifies the copies only in its target, as its formula specifies.
- The negative-literal case uses an isomorphism and zero absorption, not equality of a formula with its double negation.
- The two-object one-way-arrow diagnostic does not expose an illicit reverse arrow: the proof never infers one merely from a relational model. Its filler arrows use the explicitly supplied initial and terminal structure.
- Coherence is invoked only in the original category. The quotient can identify relations, so it would be invalid to use its faithfulness; the manuscript does not do so.

# (C) Minor issues

**M1 — Pattern versus skeleton.** Anchor: PDF p.9, Appendix A.2, paragraph following equation (13), “the substituted pattern as its skeleton.” Failure mode: `ambiguous`. Evidence: `structural_argument`. The preceding sentence defines a skeleton by erasing placeholder names; a named substituted pattern and its skeleton are consequently different descriptions. The displayed coordinate formula is unaffected. No counterexample to the maximality theorem follows. Severity: **minor**. Repairability: a local wording change. Replace the sentence by:

> In that notation, the generalized composite is represented by the skeleton of the substituted pattern together with the profile δ.

**M2 — Indexed local placeholders.** Anchor: PDF p.8, Appendix A.1, the definition of `Q_i`. Failure mode: `ambiguous`. Evidence: `absence_in_text`: outer placeholders are explicitly distinct, whereas the local sets are said only to be pairwise disjoint. The intended reading of indexed formal placeholders is distinctness within each set as well. This is an optional clarification, not a demonstrated gap. Severity: **minor**. Repairability: add “distinct” before “local placeholders.” The profile and renaming maps then have an explicit unambiguous indexing convention; no theorem statement changes.

**M3 — Scope of substitutions.** Anchor: PDF p.3, §2, definition of substitution congruence, compared with the `F_σ:B(P)→B(Q)` construction on p.4. Failure mode: `ambiguous` only on a reading detached from the fixed-category convention. Evidence: `structural_argument`: a congruence on `B(P)` is preserved by endosubstitutions `σ:P→Form(P)`; the general functor permits a different target alphabet. The proof uses endosubstitutions correctly. Severity: **minor**, optional precision. Repairability: state that type explicitly in the definition. There is no exhibited failure of the argument.

**M4 — Standalone corollary hypothesis.** Anchor: PDF p.7, Corollary 5.3. The assumption that `P` is nonempty is inherited from §2 and is used when choosing `p∈P`. Failure mode: `ambiguous` only if the corollary is quoted in isolation; no hypothesis is missing from the paper's actual context. Evidence: `structural_argument`. Severity: **minor**, optional exposition. Repairability: repeat the nonempty-variable assumption in the corollary. Its mathematics remains unchanged.

These findings do not require reconstruction of the proof. No incorrect use of “canonical” was found: the occurrence bijection is specified recursively. The direct v8 URL is correctly typeset with `\url`.

# (D) Cross-section consistency failures

None confirmed. The definition of maximality in §2, Theorem2.1, Proposition4.2, and Corollary5.3 all retain the same substitution-closed scope. `=` denotes equality in the source category and `≡` denotes quotient equality where the distinction matters. The contextual equation is first declared as an equation to be imposed, not as an existing equality of `B`.

The object operation of negation is treated contravariantly. The source writes it as `B→B^op`, while v5 uses the equivalent convention `B^op→B`; both assign `f:A→C` an arrow `¬C→¬A`. No direction mismatch occurs in the proof.

The Appendix was read. Its maps are functions between tagged sets; neither their uniqueness nor the commutative squares asserts fullness of `G`. Constant patterns and empty blocks are expressly allowed. No additional mathematical hypothesis from the Appendix is required in the collapse argument.

The Appendix was checked in detail against the source's finite-ordinal formula and the public v8 note, §9.1–§9.4:

| Construction | Check |
|---|---|
| Equation (4), occurrence blocks | Structural recursion retains one separately tagged block for each occurrence, including repeated labels. |
| Equations (5) and (10), block projections | Both routes return the label or outer profile value. These are squares of sets, which need not all be finite. |
| Equation (9), fibre maps | The source injections cover disjoint blocks; the stipulated restrictions define exactly one function `γ`. |
| Equation (11), occurrence-label map | The coordinate bijection preserves the indicated label in the tagged placeholder set. |
| Equations (12)–(13), ordinal coordinates | Cumulative sums give disjoint nonempty intervals; zero-sized blocks contribute no points. The coordinate formula agrees with the source block-locator formula. |
| Worked example | Source sizes `3,2,3` give profile `4,3,4,1,2,4,3,4`; position 2 maps to 3. |
| Equation (14), shared variables | Structural induction proves substitution followed by renaming equals the combined substitution. Noninjective renaming changes labels, not positions. |
| Empty and negative cases | Zero arities are allowed only when the indicated profiles exist. The negative-literal substitution produces double negation and uses the displayed typed isomorphism. |

A supplementary finite arithmetic check examined 1,860 admissible profile systems and 4,940 source points, including 412 empty sources and 663 systems with empty selected blocks. All assertions passed, exit 0. This is a finite consistency check, not a proof of the general statement; the general argument is the disjoint-interval and structural-induction reasoning above. The script and output are retained in `provenance/manuscript-v5-full-review/`.

# (E) Acceptance conditions, non-negotiable

1. Retain the specified zero-identity Boolean presentation and substitution-congruence hypothesis in the main theorem and abstract. This is met; broadening either without proof would invalidate the reviewed endpoint.
2. Retain Boolean Coherence as an attributed published input and the original-category/quotient distinction. This is met; claiming faithfulness of a nontrivial quotient from the same interpretation would invalidate the argument.
3. Retain explicit witnesses for nonendomorphism zeros and the signed-literal normalization step. This is met; arbitrary zeros or an unsigned selector would require a new argument.
4. Identify the exact TeX and PDF reviewed in the final combined report. The hashes above identify the unchanged source and PDF. Git blob hashes match the reviewed remote tree; a fresh successful rebuild has identical extracted text and no warnings. This condition is met. This condition concerns evidence attribution, not a missing mathematical proof.

# (F) Not checked / uncertainty log

The pinned September2007 book was retrieved from `https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf`, saved at `full-review-v5/evidence/coh-september-2007.pdf`, and hashed as `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`. Source checks covered printed p60 (occurrence interpretation), p194 (model formulation of maximality), pp215–216 (contextual equation), p234 (first-injection equation), and the relevant normalization/presentation/coherence passages of pp313–322. Printed p317 was rendered and visually checked. This audit did not reprove the book's entire chain of coherence and cut-elimination theorems.

The final verification includes a successful fresh LaTeX rebuild, no unresolved references or citations, no box warnings, and inspection of all ten original PDF pages. Nine citations match nine bibliography entries; the literal v8 URL and hyperlink destination agree. An intermediate rebuilt PDF and one PNG were found truncated despite successful process statuses; rerunning produced readable complete outputs, and the original committed manuscript was unchanged. The exact commands, statuses and inspection results are retained separately.

The three supplied full papers and bounded prior-art comparisons are documented in the preserved `docs/PRIOR_ART_UPDATE_V5.md`; the current paragraphs were reread. This review does not claim a new exhaustive search of all subsequent literature. No required claim-bearing passage was available only as an abstract.

No Lean build, axiom audit, arXiv submission check, or external human peer review was performed in this review. The theorem-by-theorem reasoning above is a mathematical audit, not machine certification. Bibliographic completeness and the current state of the entire literature remain open to an independent specialist search.

**Authorized revision: final follow-up.** All four local recommendations were applied. Final TeX SHA-256: `1ccd5983ff7ec0c5280685f81683cbb03d9b3b9a150d50376c2721e4924b7d0c`. Final PDF SHA-256: `f80bdb653dab799236833b40e8e77828407624fce7e13706dbd3191a543b487d` (11 pages). The author also requested typed TikZ diagrams for equations (1)–(3). The §2 remark points to Appendix B. Equation (2) retains its expression and number, split across two lines, with explicit type `0_A:A→A`. The zero-identity diagram has six vertices, five constituent arrows and direct `0_A` as the other path. The zero-law square has independent parallel arrows `f,g:A→C`, with `g` on the left and `f` on the right.

The revised source diff and rendered pages were checked again. Arrow directions, domains, codomains and adjacent composite types agree. No equation or theorem was weakened or strengthened; no additional law was introduced. Findings M1–M4 are resolved. No new mathematical or layout defect was found. The complete zero-identity diagram is on p.10; its explanation continues on p.11. The inherited disclosure and literal v8 URL are unchanged. No process commentary was inserted in the manuscript or source comments.

Some intermediate files were truncated despite successful LaTeX process statuses. Those files were rejected by integrity checks. Final direct passes 7–8 exited0; outputs were flushed, independently reopened and parsed. The final PDF is 11 pages, 428,101 bytes; the final log has no warnings, unresolved references or box warnings. Nine citation keys match nine entries, and equation numbering and the Appendix B reference were checked. The final hashes above supersede intermediate PDF hashes. Evidence is retained in `provenance/manuscript-v5-diagrams/`. No Lean verification or external peer review is claimed.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none supported by the inspected argument. Most important unchecked matter: independent specialist assessment of the new collapse argument and its relation to all subsequent literature. The audit's conclusion does not depend on an unavailable claim-bearing passage of the pinned book. The recommendation is the audit's bounded verdict, not a publication rejection or an acceptance certificate. Final recommendation: **unknown**; no rejection-level mathematical defect was found in the reviewed proof.
