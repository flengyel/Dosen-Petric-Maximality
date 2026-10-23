# Mathematical-writing review of the complete current v5

Date: 23 October 2026. Author-side editorial review. The initial review and subsequent authorized revision are distinguished below. Applied the explicitly requested [mathematical-writing plugin](skill://plugins_6abdaee576ac8191ba3f7c46784e1f59/revise-mathematical-prose/SKILL.md).

The exposition follows the dependencies of the proof and does not require a new outline. The main theorem, the use of published Boolean Coherence, the reduction to a contextual equation, and the collapse argument are separated. The occurrence diagrams distinguish positions from variable names. One minor wording correction is indicated in Appendix A.2: a named substituted pattern is distinct from its skeleton. No layout fault was established. Three small precision edits are also available; none repairs a demonstrated gap in the maximality proof. The inherited AI-use disclosure needs to be treated according to the author's disclosure instructions, separately from the mathematics.

Reviewed manuscript: *Maximality of the Došen–Petrić Boolean Category*, v5, dated 23 October 2026, at repository commit `cfa37604e539dc85d854959b20aca752d06774ce`.

- LaTeX SHA-256: `1e828807a1351be5aba3d446a6e275c6699d23c9fbdde73ea0d121fac054e2e2`.
- PDF SHA-256: `482b75840f70d9808ecc213dbb66cc8ec19a277ad2d14e859375aae449537906`.
- Scope: the complete LaTeX source and all ten rendered PDF pages, including the abstract, MSC line, disclosure, and references.

## Actual outline and dependencies

| Part | Function and dependencies |
|---|---|
| Abstract, p. 1 | States maximality under proof operations and uniform substitution, identifies the conjecture, and gives the three main proof steps. |
| §1, Introduction, pp. 1–2 | States the problem and contribution; gives the two-stage roadmap; acknowledges cartesian, lattice, dicartesian, and relational antecedents; distinguishes other Boolean-category axioms; explains the occurrence-coordinate appendix and source pagination. |
| §2, The Boolean proof category, pp. 2–3 | Fixes the formula category and composition convention; records the typed structural arrows, zero law, and witnessed zero arrows; defines congruences and maximality; states Theorem 2.1. |
| §3, Occurrences and substitution, pp. 3–4 | Defines tagged occurrence sets, labels, and the relation functor; states the cited Boolean Coherence theorem; records normalization and signed-literal preservation; describes occurrence blocks and the substitution functor. |
| §4, Isolating an occurrence, pp. 5–6 | Introduces the contextual equation. Lemma 4.1 uses normalization, signed-literal preservation, relational composition, and coherence to isolate a differing edge. Proposition 4.2 uses substitution and double-negation transport to obtain the contextual equation for every formula. |
| §5, Contextual collapse, pp. 6–7 | Lemma 5.1 constructs the symmetric arrow using the distributor and coherence. Lemma 5.2 uses the contextual equations, quotient products and coproducts, and the first-injection law to identify the product projections. The proof of Theorem 2.1 combines Proposition 4.2 with Lemma 5.2. Corollary 5.3 translates the conclusion into universal validity under interpretations. |
| Appendix A.1, Profiles and their fibres, pp. 7–8 | Defines finite profiles, source blocks, target placeholder blocks, their maps, and the occurrence-to-profile comparison. |
| Appendix A.2, The finite-ordinal presentation, p. 9 | Changes block coordinates to consecutive position numbers, gives the formula for generalized composition, and checks it in an example. |
| Appendix A.3, Shared variables and the maximality argument, pp. 9–10 | Defines noninjective renaming and its substitution square; applies the coordinates to the positive- and negative-literal cases of Proposition 4.2. |
| Disclosure and references, p. 10 | Records AI assistance and supplies nine bibliographic entries. |

The central question is whether a new substitution-closed equation forces the specified Boolean category to become thin. The proposed contribution is the affirmative answer, obtained by contextual isolation and collapse. The appendix explains coordinates used in the argument; it does not substitute for a missing collapse proof.

## Comparison with the governing source

Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts's *Mathematical Writing* was consulted in the [119-page MIT CSAIL/JMLR course-report copy](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf), §1 and §§4–5. The relevant passages are §1, points 5, 10–17, 24, and 26, and the discussion of definition timing in §§4–5. Printed pages 1–6 correspond to PDF pages 3–8; printed pages 9–13 correspond to PDF pages 11–15. The consulted copy was also cached: SHA-256 `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6` (555,031 bytes). No byte identity with the Stanford-hosted file or the later MAA edition is asserted. Earlier access records remain historical records.

The following principle descriptions are paraphrases. The judgments about this manuscript and the reporting format are editorial applications, not rules attributed to the course report.

| Manuscript anchor | Observation or difficulty | Verified principle or independent rationale | Action |
|---|---|---|---|
| Abstract and §1 opening, p. 1 | The theorem and the substitution closure are stated before the technical setup. The roadmap names the two stages. | §1, points 12 and 24: orient the reader and make the opening effective. | Retain. |
| §1 literature paragraphs, pp. 1–2 | Each citation has a stated role: antecedent, related construction, alternative axioms, or coordinate description. | Editorial rationale: comparisons should identify the feature being compared. | Retain the bounded comparisons; do not expand this into an unsupported survey. Mathematical source verification is a separate task. |
| §2 definition of substitution congruence, p. 3; source lines 169–176 | The fixed category implies substitutions into `Form(P)`, but §3 subsequently treats substitutions into `Form(Q)`. | §1, points 11 and 17: introduce variables near use and avoid ambiguity. | Optional: write the endosubstitution type explicitly at the definition. |
| Theorem 2.1, p. 3 | The statement repeats the nonempty-variable assumption and spells out maximality. | §1, point 5: theorem statements should ordinarily be self-contained. | Retain. |
| §3 signed literals and normal forms, p. 4 | Definitions precede the invariant used in Lemma 4.1. The source and role of coherence are stated. | §1, point 11; §§4–5: place definitions before or near use, with context-sensitive judgment. | Retain. No requirement to reproduce the entire cited book presentation in this short paper follows from this writing principle. |
| §3, equation (4), p. 4; source lines 279–294 | The word “canonical” is followed by recursive clauses determining the bijection without an additional choice. | Independent terminology check requested by the author. | The adjective is justified here. No replacement is needed. |
| §§4–5, pp. 5–7 | Equations are connected by explanations of the selected edge, zero relation, symmetry, terminality, and the projection consequence. | §1, points 10 and 13: connect formulas by prose that remains readable when formulas are skimmed. | Retain. |
| Corollary 5.3, p. 7; source lines 560–565 | The statement inherits the nonempty set `P` from §2 rather than repeating it. | §1, point 5. | Optional standalone-reading improvement: repeat that assumption. This is not evidence that the corollary is false. |
| Appendix A, pp. 7–10 | Each diagram is preceded by the object and map definitions and followed by the elementwise identity it states. | §1, points 10–11; independent typed-diagram convention of the plugin. | Retain the diagrams and worked example. |
| Appendix A.1, p. 8; source lines 603–607 | The indexing of local placeholders is used as if it lists distinct elements, while only disjointness between different sets is explicit. | Editorial rationale: make the indexing convention explicit where a profile is defined. | Add “distinct” before “local placeholders.” This makes the intended enumeration explicit without changing the construction. |
| Appendix A.2, p. 9; source lines 717–721 | “The substituted pattern as its skeleton” conflates a named pattern with the result of erasing its placeholder names. | §1, points 14 and 17: distinguish related notation and avoid ambiguity. | Use the full-sentence replacement below, which distinguishes the pattern from its erased skeleton. |
| Appendix A.2, p. 9 | Nested profile indices are necessary to show the source's formula. Prose and the example explain them. | §1, points 14–15: consistent notation and economical indices. | Retain; replacing the indices would obstruct the source comparison. |
| “Use of AI tools,” p. 10; source lines 782–784 | The paragraph describes assistance with proof development, manuscript preparation, and checking. It is a conventional disclosure, not an instruction to an LLM or a claim of independent review. | Current plugin disclosure exception and the author's instruction to exclude process commentary; this is not a KLR rule. | Preserve during this review-only task. It is an inherited conventional disclosure, not a demonstrated instance of prohibited revision narration. Its retention is a separate author or publication decision; the present request does not authorize its automatic deletion. |
| Reference [9], p. 10 | The literal v8 URL is typeset with `\url`; its punctuation is outside the link. | Independent LaTeX and source-identification check. | Retain the exact URL supplied by the author. No custom display label or added commas are needed. |

## Definition order and notation

| Notation or term | First introduction and assessment |
|---|---|
| `P`, `Form(P)`, `B(P)`, and `B` | §2 opening, p. 2. The nonempty assumption and abbreviation are explicit. |
| Products, coproducts, `π_i`, `ι_i`, pairing, copairing, `!`, `κ`, `1` | §2, p. 2, before their use. Projections and injections have displayed types. Ordinary pairing and copairing notation is appropriate for the intended audience. |
| Composition and tensor operations | §2 explicitly says that `g∘f` applies `f` first; `f∧g` and `f∨g` are assigned to the bifunctors. Later path descriptions respect that convention. |
| `d`, `n_A`, `η_A`, `ε_A`, `0_A` | §2, p. 2. Types and the zero-identity composite precede the zero law and the proof. |
| `0_{A,C}` | §2, pp. 2–3. It is defined only when an arrow already exists. No definition silently asserts that every hom-set is inhabited. |
| Proof congruence, substitution congruence, total, thin, preorder, maximal | Defined together in §2, p. 3. The stronger substitution requirement is distinguished from proof congruence. |
| `Occ`, tagged union, and `λ_A` | §3, p. 3. Positions and variable labels are explicitly distinguished; repeated labels are allowed. |
| `Rel_fin`, `G`, Boolean Coherence | §3, pp. 3–4. The category, arrow interpretation, and cited faithfulness statement appear before use. |
| Signed literal, negation normal form, `a_A:A→A°` | §3, p. 4. Adequately introduced for the cited normalization construction. |
| `σ`, `D_{A,σ}`, `E_σ`, projections, `λ̂`, `F_σ` | §3, p. 4. Their types and the square's pointwise identity are given. `E_σ` may be infinite when `P` is infinite; the text correctly calls this a square of sets and functions, not a diagram in `Rel_fin`. |
| `j_A`, `(K_A)`, `i`, `r`, `b_V`, `t_V` | §4, p. 5. Introduced before use, with endpoints. The positive and negative literal cases are separated. |
| `u_A^B`, `h_A^B`, `h_A`, `τ_A`, `≡` | §5, p. 6. Independence of `B` is proved before suppressing it; quotient equality is distinguished from equality in `B`. |
| Interpretation and the category `𝒞` | §5, p. 7. Introduced before Corollary 5.3. Distinct typography prevents confusion with a formula denoted `C`. |
| Patterns, profiles, `D`, `C`, `a_r`, `b_i`, `γ`, `p_D`, `p_C`, `Φ_0`, `χ` | Appendix A.1, pp. 7–8. Local definitions precede the diagrams. The reuse of `C` for a set is confined to a fresh appendix setup and is unambiguous. |
| `s_r`, `t_i`, `θ_D`, `θ_C`, `δ` | Appendix A.2, p. 9. Defined before use; the cumulative sums and local coordinates have separate roles. Empty blocks are addressed explicitly. |
| `ρ` and the renamed `σ` | Appendix A.3, pp. 9–10. Types distinguish renaming from formula substitution; noninjectivity changes names without identifying occurrences. |

The abstract and Introduction preview terms later defined in the body; that is appropriate for this research-paper genre. No additional glossary is needed. The word “usual” is absent. The one occurrence of “canonical” passes the choice-independence check above. The source contains no LaTeX comments. Apart from the separately discussed disclosure, no instructions, review findings, drafting history, or formalization-progress narration appear in the manuscript.

## Outline recommendation

Retain the outline. Moving Appendix A into §3 would delay the isolation argument without changing its dependencies. The related-work paragraphs belong after the roadmap, where the reader can identify the aspects being compared. A separate literature-survey section is not warranted by the current text.

## Prioritized exact wording

The confirmed minor wording correction concerns the last sentence of the first source-comparison paragraph in Appendix A.2 (source lines 719–721). Replace that sentence with:

```latex
In that notation, the generalized composite is represented by the
skeleton of the substituted pattern together with the profile $\delta$.
```

This distinguishes the erased connective pattern from its named occurrences. It does not change the displayed map or the maximality argument.

The following precision edits are optional; they should not be presented as repairs of failed mathematics.

1. In §2, replace the sentence defining substitution congruence with:

   ```latex
   A \emph{substitution congruence} is a proof congruence also preserved
   by every uniform substitution $\sigma:P\to\FormulaSet(P)$.
   ```

   Keep the following sentence explaining that substitution acts on the entire arrow term and its endpoints. This distinguishes the congruence on one fixed category from the more general functor in §3.

2. Begin Corollary 5.3 with:

   ```latex
   Let $P$ be a nonempty set of propositional variables, and let
   $f,g:A\to C$ be distinct arrows of $\B(P)$.
   ```

   Leave the remainder unchanged. This repeats an existing assumption; it neither strengthens nor weakens the result.

3. In Appendix A.1, replace “a set $Q_i=\{q_{i,1},\ldots,q_{i,\ell_i}\}$ of local placeholders” with “a set $Q_i=\{q_{i,1},\ldots,q_{i,\ell_i}\}$ of distinct local placeholders.” This states explicitly that the displayed indices enumerate the local set without repetition.

No replacement of “canonical” or of the reference [9] URL is recommended. The disclosure issue should be resolved as a disclosure decision rather than disguised by new prose elsewhere in the paper.

## Scope and verification

The complete source and all ten current PDF pages were read. The PDF has no observed clipped text, overlapping diagram labels, broken display alignment, or bibliography overflow. The direct v8 URL is visible and line-breaks within the bibliography; the source uses `\url` correctly. The diagrams' arrows and labels remain legible at normal page scale. The page break within Proposition 4.2 is ordinary continuation and does not obstruct its argument.

The review ran `pdftotext -layout`, rendered all ten pages with `pdftoppm`, and verified the source and PDF hashes against the remote Git tree. A fresh LaTeX rebuild also succeeded, with no warnings or unresolved references and with extracted text identical to the committed PDF. Nine citation keys match nine entries. The exact v8 hyperlink destination was checked. An intermediate truncated build output and PNG required regeneration; the successful final checks and the intermediate failures are recorded in the verification evidence. The original manuscript source and PDF were not replaced. No Lean command was run. This is an editorial assessment, not certification of mathematical correctness, novelty, or a completed formalization. The citations' mathematical content is being checked separately in the hostile/source review; this report does not claim a fresh full-text audit of every referenced work.

The earlier v5 writing report is historical and names a different source hash. Its findings have not been silently transferred to the present bytes. This report records a fresh complete reading and rendering inspection of the hashes stated above.

## Authorized revision and final inspection

**Authorized revision: final follow-up.** All four local recommendations were applied. Final TeX SHA-256: `1ccd5983ff7ec0c5280685f81683cbb03d9b3b9a150d50376c2721e4924b7d0c`. Final PDF SHA-256: `f80bdb653dab799236833b40e8e77828407624fce7e13706dbd3191a543b487d` (11 pages). The author also requested typed TikZ diagrams for equations (1)–(3). The §2 remark points to Appendix B. Equation (2) retains its expression and number, split across two lines, with explicit type `0_A:A→A`. The zero-identity diagram has six vertices, five constituent arrows and direct `0_A` as the other path. The zero-law square has independent parallel arrows `f,g:A→C`, with `g` on the left and `f` on the right.

The revised source diff and rendered pages were checked again. Arrow directions, domains, codomains and adjacent composite types agree. No equation or theorem was weakened or strengthened; no additional law was introduced. Findings M1–M4 are resolved. No new mathematical or layout defect was found. The complete zero-identity diagram is on p.10; its explanation continues on p.11. The inherited disclosure and literal v8 URL are unchanged. No process commentary was inserted in the manuscript or source comments.

Some intermediate files were truncated despite successful LaTeX process statuses. Those files were rejected by integrity checks. Final direct passes 7–8 exited0; outputs were flushed, independently reopened and parsed. The final PDF is 11 pages, 428,101 bytes; the final log has no warnings, unresolved references or box warnings. Nine citation keys match nine entries, and equation numbering and the Appendix B reference were checked. The final hashes above supersede intermediate PDF hashes. Evidence is retained in `provenance/manuscript-v5-diagrams/`. No Lean verification or external peer review is claimed.

The outline now places Appendix B after Appendix A and before the disclosure and references. The diagrams expose the intermediate types without interrupting the main proof. The four exact prose repairs above are implemented. No further editorial correction is recommended.
