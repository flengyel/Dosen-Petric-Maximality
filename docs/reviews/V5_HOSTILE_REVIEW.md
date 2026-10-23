# (A) Kill-shots / hard blockers

None confirmed in the reviewed changes.

This is an AI-assisted author-side audit of the v5 literature and classification additions, dated October 23, 2026. It is not independent peer review. The complete v5 TeX and its diff against the committed v4 text were read. No manuscript file was edited by this reviewer.

Reviewed final v5 source: `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex`, SHA-256 `5d9ab4080a52a57d0e3e69bc732ada39e6911bc63cb235bb61fea17448365d2e`.

The final check includes the more precise phrase “split equivalence relations,” removal of the redundant sentence about formula endpoints, the explicit `0912.1271v3` date, and the wording “Other axiomatizations of Boolean categories use different structures.” These refinements introduce no new mathematical claim.

# (B) Major weaknesses

None established for the scoped additions. The added prose does not claim that occurrence selection or distinguishing-edge arguments are wholly new. It attributes related constructions and confines the present argument to the specified Boolean category.

| Manuscript anchor | Claim checked | Primary-source evidence | Result |
|---|---|---|---|
| Introduction, lines 62–65 | Lattice maximality and relative dicartesian maximality concern the setting without distribution. | Došen–Petrić, *Bicartesian Coherence Revisited*, [arXiv:0711.4961v3](https://arxiv.org/pdf/0711.4961v3), abstract and §§8–10. Section 8 explicitly requires substitution closure; §9 treats lattice maximality, §10 relative dicartesian maximality. | Supported. |
| Introduction, lines 65–66 | Related occurrence-selection constructions occur in Lemma 6 of *Isomorphic Formulae*. | [arXiv:0912.1271v3](https://arxiv.org/pdf/0912.1271v3), Lemma 6 and proof, printed pp.12–13, constructs an arrow linking chosen occurrences under its stated tautology hypothesis. | Supported as a related construction; the manuscript does not assert an identical theorem or drop the source's hypothesis. |
| Introduction, lines 66–68 | Distinguishing an edge proves maximality of presentations for split preorders, split equivalence relations, and binary relations. | [arXiv:0902.0742v7](https://arxiv.org/pdf/0902.0742v7), §16, printed pp.55–58: maximality of PF, EF and RB via their relational presentations and selected differing pairs. | Supported. The manuscript does not infer maximality of the formula category merely from faithfulness into Rel. |
| Introduction, lines 70–75 | Straßburger's hierarchy uses different structures, namely star-autonomous categories with monoid and comonoid structure. | [arXiv:cs/0512086v3](https://arxiv.org/pdf/cs/0512086v3), abstract, introduction, and Definition 5.5 with the following duality observation. | Supported. No equivalence, inclusion, or generalization between the two frameworks is asserted. |

# (C) Minor issues

No correction is required by the inspected evidence.

The classifications at lines 37–38 are legitimate MSC2020 entries and fit the subject: 03G30 for categorical logic, 03F07 for structure of proofs, and 18A32 for congruences and quotient structures. The codes were checked against the [AMS MSC2020 classification](https://mathscinet.ams.org/msc/pdfs/classifications2020.pdf).

The bibliographical volume, year and page data of the three added Došen–Petrić papers agree with the [author's publication list](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/publications.htm), entries 78, 86 and 89. All three explicit arXiv version dates agree with their PDF headers, including `0912.1271v3`, October 4, 2010. The Straßburger publication data agree with the [journal's abstract record](https://tac.mta.ca/tac/volumes/18/18/18-18abs.html).

# (D) Cross-section consistency failures

None confirmed. An exact text comparison found that Section 2 through the end of Appendix A is identical to v4. The preserved portion has SHA-256 `696ae7de13f7cf5f1be7f29bd6a873417273400f73a16a303c46daadc418289b`.

The nonempty-variable hypothesis, substitution-congruence scope, witnessed-zero convention, signed-literal argument, theorem statements, proofs and substitution diagrams therefore remain unchanged. The abstract also remains unchanged. The new literature paragraphs neither remove the substitution requirement nor claim complete Lean verification.

# (E) Acceptance conditions, non-negotiable

1. Retain the theorem's substitution-congruence scope and the specific zero-identity Boolean-category presentation. This endpoint is met by the reviewed text; broadening either claim would require another mathematical audit.
2. Retain the explicit attribution of prior occurrence-selection and relational maximality arguments. This endpoint is met; omitting it while claiming the entire technique is novel would require correction.
3. Verify the final rendered v5 PDF, cross-references and bibliography against the final TeX bytes. This is a separate production check, not a mathematical defect established here.

No scoped finding requires reconstruction of the manuscript or completion of the Lean formalization before circulation as a mathematical preprint.

# (F) Not checked / uncertainty log

This audit verifies the added descriptions against the cited portions of primary sources. It is not an exhaustive search proving that no other relevant publication exists. It does not certify the entire published Boolean Coherence proof, the final PDF layout, arXiv compilation, or repository/Downloads delivery. The primary Wiley DOI endpoint did not load in this review; author-side publication data and the arXiv text were accessible. TAC's PDF endpoint also failed, so the structural claim was checked in its arXiv author version and the publication details in the journal record.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none supported by the inspected evidence. Most important unchecked matter: exhaustive novelty and independent specialist assessment of the main theorem. The scoped recommendation does not depend on an unavailable source passage. Final recommendation on unrestricted publication certification: **unknown**; the scoped v5 changes have no confirmed rejection-level defect.

Final production check: removal of the extra blank line at end of file made no prose or mathematical change. The source hash above includes that whitespace correction.
