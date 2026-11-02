# V23 implementation review

2 November 2026. Author-side review under the hostile-referee and mathematical-
writing workflows; not independent human peer review. Base: v22 at
5b515365f5d5164ba65c91ab3571fd2f475a0b66. The preceding
[full review and proposed rewrites](V22_REVIEW_AND_REWRITES_2026-11-02.md)
is preserved unchanged as a historical report. Its proposed Codex handoff is
superseded by the author's instruction to implement the changes directly.

## A. Hard blockers

None confirmed in the changed text. The main mathematical claims are preserved.

## B. Mathematical check

The introduction includes substitution and double-negation transport. For a
negative literal, substitution alone produces K_(not not A); transport gives K_A.
Appendix C defines L,R,r and r-prime, states the lexicographic induction and
proves strict rank descent in both cases. The p.262 cut has rank L+1<L+R
because the original right rank exceeds one. This explains the existing
induction; it does not replace the rank measure or cut reductions.
All seven statement environments, six proof environments, twelve numbered
equations, 77 displayed formulas, thirteen diagrams and 34 labels match v22
byte for byte. Both maximality routes and all five appendices remain.

## C. Writing check

The full revised source was read. The introduction leads with the result and
proof. Detailed comparisons move beside their mathematical uses. The redundant
proof-net paragraph is removed; its database entry remains uncited. Section 6
names the second proof. Raw terms becomes arrow terms; the empty union is the
zero arrow on a nonempty hom-set. Appendix D.5 names all equational inputs
used to derive the union-zero law and retains independence from faithfulness.
No further empty modifier was identified. Mathematical qualifications such as
uniform, nonempty and positive are retained with their defined meanings.

## D. Citations and correspondence

The relocated comparisons agree with the primary passages checked in the v22
review. The negation-free hypothesis in Lemma 6 remains; pp.249 and 253 support
the rank definition and lexicographic induction. The Notation URL is pinned
to 42eaccdccf6413fe4d643a347fab33edafb1c056. The supplied Palomar BibTeX is
byte-identical. All 56 proof-link occurrences and 49 declaration destinations
are unchanged. No new priority claim is introduced.

## E. Build and layout

Three pdfLaTeX passes and BibTeX succeed for both source and extracted archive.
Both have 23 pages, identical text and coordinates, and identical bibliography.
All pages were inspected in contact sheets, with Appendix C and final pages
also inspected individually. One underfull bibliography paragraph from the
pinned URL is visually acceptable. No unresolved citation/reference, overfull
box or duplicate destination remains.

## F. Limits

No Lean source was edited and no Lean build, kernel replay or new registration
was performed. The earlier primary-source review and proof verification are
reused; this is not a fresh transitive proof audit or exhaustive priority search.
The findings do not establish a defect in the registered formal proof.
Windows Downloads is unavailable here; no Windows delivery is claimed.
