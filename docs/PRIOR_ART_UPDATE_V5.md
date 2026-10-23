# V5 prior-art update

Date: 23 October 2026 (UTC). Baseline: `2d240b2aa578b84277f59524d9f8819a41273a0d` in `flengyel/Dosen-Petric-Maximality`.

## Scope and result

The Introduction now credits the Cartesian maximality argument and acknowledges the Lamarche–Straßburger and Führmann–Pym presentations. Three bibliography entries were added. The title, abstract, MSC classifications, Sections 2–5, Appendix A and AI disclosure are unchanged. The version remains v5.

## Source comparison

All three supplied papers were read in full. Their access status supersedes the earlier abstract-only screens; the historical access records remain in the initial literature report.

| Paper | Checked claim and boundary |
| --- | --- |
| Došen–Petrić, *The Maximality of Cartesian Categories*, §5, preprint p.6 | Coherence, uniform substitution and typed pre/postcomposition reduce a new Cartesian equation to equality of projections. Validity quantifies over every Cartesian interpretation. Its language does not contain arbitrary Boolean terms; the manuscript's isolation and contextual-collapse arguments supply that reduction. |
| Lamarche–Straßburger, *Constructing Free Boolean Categories*, Theorem 3.5.4 | The free-category result is for the authors' specified graphical, Δ–∇-strong K-autonomous axioms, with the stated unit variants. The introductory phrase “for their Boolean-category axioms” retains that restriction without introducing their notation. |
| Führmann–Pym, *Order-enriched categorical models of the classical sequent calculus*, Theorems 6.4–6.5 and (11), printed p.28 | Ordered soundness and completeness concern their net theories. Precomposing (11) with the inverse right unit isomorphism gives an identity endomorphism. Under the corresponding structural notation, the same composite defines DP's zero identity. The comparison does not attribute DP products or coproducts to their models. |

The source-comparison reviewer checked the final Introduction and bibliography against the baseline and found no remaining correction within this scope. This was an AI-assisted author-side review, not independent peer review. It does not certify exhaustive novelty or the complete mathematical argument.

## Writing review

The actual order is: Introduction (question, proof roadmap, antecedents, alternative presentations, occurrence coordinates); Boolean proof category (definitions and main theorem); Occurrences and substitution (coherence and coordinates); Isolating an occurrence (contextual equation); Contextual collapse (proof and model corollary); Appendix A (profiles, finite ordinals, shared variables); disclosure and references. No change of outline was needed.

Knuth–Larrabee–Roberts, *Mathematical Writing*, §1 and the relevant discussion in §4, were consulted in the 119-page course-report copy at https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf. The Stanford URL timed out during this consultation. This records the actual accessible copy, not byte identity with the Stanford scan; previous access records are preserved.

| Location | Finding and disposition |
| --- | --- |
| Introduction, Cartesian paragraph | Attribute the proof method and identify its Boolean extension. The reference contributes mathematical context, rather than an originality claim. |
| Introduction, alternative presentations | Name the results and state the difference in the negation equation. No evaluative adjectives or new display were added. |
| Notation | The comparison points to the existing zero-identity definition. No new symbol is introduced. “Canonical” was not added; its existing use describes the recursively specified occurrence-block bijection. “Usual” is absent throughout the manuscript. |
| Bibliography | Added complete author names, titles, publication details and links for the three papers. Nine citation keys resolve to nine entries. |

These are applications of the source's advice on connected exposition, readable sentences, restrained evaluation and bibliographic accuracy, together with the user's requested vocabulary constraints. Review and revision commentary remains outside the manuscript and its LaTeX comments.

## Verification

Two `pdflatex -interaction=nonstopmode -halt-on-error` passes exited 0. The exact command arrays and exit codes are in `provenance/manuscript-v5-prior-art/commands.json`. The PDF has 10 pages. The final log has no LaTeX warnings, unresolved citations or references, overfull boxes or underfull boxes. All ten pages were rendered and inspected in a contact sheet; pages 1, 2 and 10 were also inspected at full-page resolution. No clipping, overlap or missing glyph was observed.

`git diff --no-index --check` exited 1 with empty output: the files differ, without whitespace diagnostics. The abstract/preamble, mathematical body and disclosure were compared directly. The source diff changes only the Introduction and bibliography. No Lean file, toolchain or dependency is changed; Lean verification was not rerun for this prose revision.

| Item | SHA-256 |
| --- | --- |
| Revised v5 TeX | `007e90e1822ada6914ce5e052251b89f79e390f010d67dd882d7b9c1caee8418` |
| Revised v5 PDF | `b92405c1d9f4a9ad23d8ad44b44b8c0460eeae7570c39487e156e04a2791dd55` |
| Unchanged Section 2 through Appendix A | `696ae7de13f7cf5f1be7f29bd6a873417273400f73a16a303c46daadc418289b` |
| Došen–Petrić, Cartesian maximality | `16e6cec4341111cbec57c65ebe9ba925e0aa69e4371cfc189c57a33efd743d9c` |
| Lamarche–Straßburger | `a620cca2cdd128926be7688b3262ca8df101cee0416864046e138cb7aa6f939b` |
| Führmann–Pym | `f4b780a95f4492e21edae838fe5ffd5b06628f909169579734eb2c77dc176ae9` |

The repository manuscript checksum file is updated for the two revised files; its v4 entries are retained. The earlier v5 build evidence is retained separately. Delivery to Windows Downloads is unavailable in this cloud workspace; no WSL copy is claimed. The finalized repository files and downloadable copies are the delivery for this revision.

## URL typesetting correction

After commit `7ddaebb23da983f14cc04ad9e24d070e171f1aa6`, the bibliography's custom link label was replaced by `\url{https://github.com/flengyel/notes/blob/main/logic/The-Unbearable-Notation-of-Logic_v8.pdf}`, using the direct PDF URL supplied by the author. The repository directory was inspected and contains the cited v8 PDF and TeX source; its PDF blob is `7415c7c3c5bd841bec867cb8e69f145109401e60`, matching the previously cited version. The title, version, date, section and all other manuscript text are unchanged. The historical pinned URL remains in the earlier records.

Two LaTeX passes exited 0, with no warnings or overfull/underfull boxes. The 10-page PDF's bibliography displays the supplied URL and its hyperlink has the same destination. The source diff changes one bibliography line; the whitespace check has no diagnostics. Commands and logs are retained under `provenance/manuscript-v5-url/`. The bibliography page was visually inspected. A preliminary text-extraction check failed because it did not allow a line break in a URL; the final check removes extraction whitespace and separately checks the exact hyperlink destination.

Current TeX SHA-256: `1e828807a1351be5aba3d446a6e275c6699d23c9fbdde73ea0d121fac054e2e2`.

Current PDF SHA-256: `482b75840f70d9808ecc213dbb66cc8ec19a277ad2d14e859375aae449537906`.
