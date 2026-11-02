# Manuscript v20: descriptive collapse statement

1 November 2026. V20 states the result directly and explains the term
maximality afterward. The universal quantifier and both closure conditions
remain explicit. This is an equivalent statement of the proved result.

## Wording and mathematical correspondence

The abstract now says:

> We prove that adjoining any equation between parallel arrows that does not
> follow from the defining equations, and closing under the arrow operations
> and uniform formula substitution, collapses this category to a preorder.
> All arrows with the same source and target then become equal.

The preceding sentence identifies the category and its nonempty set of free
generators. The introduction states the same descriptive result, names
maximality and cites the conjecture. It retains the distinct projections
showing that the original category is nonthin.

Section 2 defines the quotient before Theorem 2.1 and explains that its
thinness is equivalent to totality of the congruence. The theorem reads:

> Let P be a nonempty set of propositional variables, and let B(P) be the
> freely generated zero-identity Boolean category of Došen and Petrić.
> For every substitution congruence θ on B(P) that identifies two distinct
> parallel arrows, the quotient B(P)/θ is a preorder.

The following paragraph explains maximality as collapse for every
nonderivable parallel-arrow equation, with closure under arrow operations
and uniform substitution; it gives the equality/total-congruence equivalent.
The theorem proof uses Lemma 5.2's existing quotient conclusion. The model
corollary proof and Appendix D.4 explicitly connect that conclusion to totality.
The eight before/after edits are in the provenance.

The bridge is already proved by
`DosenPetric.Congruence.quotient_thin_iff_total` in
[CongruenceQuotient.lean:93](../DosenPetric/CongruenceQuotient.lean),
unchanged at registered source 5dbee39bea09539bd130f729e82636419f71f920.
The forward implication applies quotient equality to the classes of arbitrary
parallel representatives; the reverse implication applies totality to arbitrary
representatives of two quotient arrows. The statement needs no inhabited
hom-set. Both existing maximality routes give that totality. The complete
claim map now records the bridge alongside those routes.

This description agrees with Došen–Petrić's definition in §9.3, printed p.194
of the September 2007 revision of
[Proof-Theoretical Coherence](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf#page=206).
The model corollary retains its quantification over every interpretation.

## Files and checks

- [PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v20.pdf)
- [LaTeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v20.tex)
- [Four-file arXiv package](../submission/arxiv-v20/Dosen-Petric-Maximality-v20-arxiv-source.tar.gz)
- [Writing review](reviews/V20_WRITING_REVIEW_2026-11-01.md)
- [Validation](../provenance/manuscript-v20-review-20261101/validation.json)

The manuscript compiles through pdfLaTeX/BibTeX and two further passes.
The archive is independently extracted and compiled through three passes;
both PDFs have matching 23-page layout text. Final logs have no citation,
reference, box or duplicate-destination warnings. All 23 rendered pages were
viewed on six contact sheets; pages 1 and 3 were also viewed individually.
The main statement and explanation fit together on page 3. The D.5 comparison
definitions and E.1 u_A path remain on one line each at the existing size.

Undoing the eight edits and restoring version/bibliography suffixes recovers
v19 byte for byte. Theorem 2.1 is restated equivalently; the other six numbered
statement bodies are byte-identical. Twelve numbered displays, thirteen
diagrams, 34 labels, seventeen footnotes, both proof routes, Appendix A and
its main-text references, and the authorized disclosure remain. Both BibTeX
databases and the rendered bibliography are byte-identical to v19. The exact
author-supplied Palomar v2 entry and all 49 declaration URIs remain.

All 153 preceding manuscript/submission files are byte-identical to the input
commit. The 857 registered proof/input blobs, scripts, workflows and stash
are preserved. All active links, abstract representations, version/date and
file-hash fields are synchronized. The abstract is ten sentences, 186 words.
The preceding preparation report is preserved byte for byte under docs/history.
This focused mathematical-writing review includes a continuous source prose
pass and the changed correspondences; it is not a new independent proof-body
audit or hostile review. Existing successful verification and registration
are reused. No arXiv upload has occurred.

## Hashes and delivery

Source SHA-256: `42abb5430593d6c2fadd8287bc2b59d607c4441c4996aa03169b91cd26b865ed`.
PDF SHA-256: `3d7525719527c0db09033fadef8610035f98b314cc25a451c048d83a79b3ad9a`.
Archive SHA-256: `c9e35dd27d483d59bd3f95401479740339e5e887c1970db0bc4796e990bb39fa`.

Reports and release files are delivered from committed bytes under
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v20-20261101/`.
The report and writing review retain their names there. Exact paths, hashes
and byte comparisons are in the
[delivery receipt](../provenance/manuscript-v20-review-20261101/delivery-receipt.json).
Differing existing copies are preserved. The release and receipt commits are
pushed to main; its remote ref and clean working tree are checked before completion.
