# V5 sentence-level writing review

The revision removes misleading source comparisons and distinguishes maps from diagrams and pairing from composition. The mathematical argument and its hypotheses are unchanged. The complete final manuscript was read through the sentence audit; all replacement passages were rechecked. Review commentary is confined to the reports and evidence.

Source: *Maximality of the Došen–Petrić Boolean Category*, v5, 23 October 2026. Baseline commit: `c03fb490a799eb0cbbd762aaf3bc927e2abad806`. Final TeX SHA-256: `66e7e3c24dcf986d7f424421903a79a41156282b56c7d6f0b36c1fe8b4b044ea`. Final PDF SHA-256: `2a44447a3cf511acf6828aba851f3582f506e3e26f9676113887aed2c38160f6`.

## Actual outline

| Part | Function and dependencies |
| --- | --- |
| Abstract and metadata | State maximality under substitution closure; identify proof steps, MSC codes and subject terms. |
| §1 Introduction | State the source conjecture, proof strategy and specific relationships with prior work. |
| §2 Boolean proof category | Define the category, structural maps, witnessed zeros and substitution congruence; state Theorem 2.1. |
| §3 Occurrences and substitution | Introduce tagged occurrences, published Boolean Coherence, signed normalization and the substitution functor. |
| §4 Isolating an occurrence | Construct selectors/coselectors; obtain every contextual equation by substitution and double-negation transport. Depends on §3. |
| §5 Contextual collapse | Construct the symmetric distributor composite; prove thinness, finish Theorem 2.1 and derive the interpretation corollary. |
| Appendix A.1 Profiles and their fibres | Define tagged substitution blocks and their profile maps. |
| Appendix A.2 Finite-ordinal presentation | Compare block coordinates with the source's profile formula and calculate an example. |
| Appendix A.3 Shared variables | Prove the renaming square and relate it to the contextual substitution step. |
| Appendix B Structural equations | Give typed diagrams for equations (1)–(3). |
| Disclosure and references | Retain the conventional disclosure and give nine source records. |

The main contribution is the collapse from the contextual equation to equality of projections in the specified zero-identity Boolean category. The outline preserves its dependencies; no reordering is needed.

## Governing source and comparison

Knuth–Larrabee–Roberts, *Mathematical Writing*, was consulted in the verified 119-page course-report copy at `https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf`, SHA-256 `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`. Section 1, particularly points 11, 14, 16 and 17, supplies advice about complementary explanation, consistent notation, displays and unambiguous reading. The existing source-based review had also consulted the contextual discussion of definition placement in §§4–5. No byte identity with the Stanford scan or the published MAA edition is claimed. Historical Stanford access failures remain in earlier records.

The mandatory typing and TikZ conventions are supplementary instructions of the mathematical-writing skill and the author's requirements; they are not attributed to Knuth–Larrabee–Roberts.

| Location | Actual difficulty | Principle or editorial rationale | Applied action |
| --- | --- | --- | --- |
| §2 after (2)–(3) | “Written explicitly” implied an omission in a source that already displays the unit maps. | Exact attribution and unambiguous prose. | State the notation change; cite the two source equations separately. |
| §2 congruence definition | Primitive and derived operations were not distinguished in the list. | Preserve the kind of mathematical object being described. | Identify the listed operations as derived. |
| §3 signed-label paragraph | Generator terminology and operation closure were less precise than the source grammar. | Consistent terminology and accurate description of a construction. | Name structural/zero/atomic families and composition/both tensors. |
| Lemma 5.1 | Swap type was implicit; the proof described postcomposition loosely as “copairing with”. | Author's explicit-typing requirement and precision about operations. | Type the swap and the copairing arrow; name the postcomposition. |
| Corollary 5.3 proof | Pairing was grammatically applied “with” projections. | Unambiguous order and kind of operation. | Form the pair, then compose with projections. |
| Appendix A.2 | Our notation was attributed to the source; the square's scope was overstated. | Consistent notation; distinguish a component from the complete construction. | State notation correspondence and identify the occurrence-profile component. |
| Appendix A.2 example | A square was described as acting on a point. | Distinguish a diagram from its functions. | Name `γ`, then `θ_C`, and calculate both images. |
| Bibliography [1] | Publisher name was abbreviated. | Bibliographic precision. | Spell out King's College Publications. |

## Definition order and notation

The category and composition convention precede the structural equations. Projections, injections, terminal and initial maps are typed before use. Equation (2) still has the explicit type `0_A:A→A`; no break was inserted into its single-line display. Witnessed zeros are defined before their absorption laws. Substitution congruence explicitly uses endosubstitutions `P→Form(P)`; the later general functor permits a different target alphabet.

The signed-literal and normal-form definitions precede their role in occurrence isolation. The selector and coselector have explicit endpoints. The swap now has an explicit signature. Appendix maps, profiles and coordinate bijections are introduced with their domains and codomains before their equations. Repeated equal labels keep separate tags. The remaining occurrence of “canonical” describes the recursively determined occurrence-block bijection; it is not used as a substitute for defining that map. The manuscript does not use “usual”.

No revised outline is warranted. Equation (2) remains in the main text and its fully typed diagram remains in Appendix B. The bibliography begins on its own page, avoiding a lone final reference after the revised prose.

## Exact principal replacement

```tex
Equation~\eqref{eq:zero-identity} is $(0\eta\epsilon)$ of
\cite[\S14.2, p.~317]{DP}. Its product and coproduct unit isomorphisms
are expressed here in pairing and copairing notation.
Equation~\eqref{eq:zero-law} is the zero-identity law $(0I)$;
see \cite[\S14.3, p.~322]{DP}.
```

Every other replacement and its assessment is recorded in the [sentence ledger](V5_SENTENCE_LEDGER_2026-10-23.md); the [hostile report](V5_SENTENCE_HOSTILE_2026-10-23.md) distinguishes confirmed imprecision from optional precision.

## Verification and scope

Final pdflatex passes 7–8 exited 0. The 12-page PDF was independently reopened, rendered and inspected. There are no LaTeX warnings, unresolved citations/references or box warnings. Nine citation keys match nine bibliography records. The public v8 URL remains exactly the author's supplied URL, typeset with `\url`, and the PDF hyperlink destination matches. Both new manuscript hashes were checked, and the v4 manifest entries remain unchanged.

The final ledger contains 303 units covering every sentence plus displays, metadata and bibliography records; every quoted passage matches the final source. The exact-source coverage check reports no uncovered authored lines. All four review follow-ups name the final source hash. The complete source contains no comments and no inserted revision-process commentary. The inherited conventional disclosure is unchanged.

This writing review is not an independent mathematical certification or a complete novelty search. All claim-bearing literature comparisons had full-text evidence; the public v8 note was checked from its full TeX. No Lean verification or Windows Downloads delivery was performed in this cloud environment. Repository reports and the finalized downloadable files are retained; earlier review and access records are preserved.
