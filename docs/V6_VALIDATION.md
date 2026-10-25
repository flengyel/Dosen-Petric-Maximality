# Manuscript v6 revision and validation

Revision date: 25 October 2026.

The revised manuscript retains the maximality theorem and model corollary, replaces the contextual-collapse proof with an argument from two published structural isomorphisms, distinguishes its hypotheses from Joyal's cartesian closed setting, and describes the conditional Lean contribution. The novelty assessment now separates derivability from earlier results from an earlier publication of the theorem. No earlier explicit statement was located in the documented search; this is not a proof of priority.

## Source and scope

The baseline was GitHub main `0af6a0e83fdcbb5ec3d98103cbb36b8f2b30dec6`, tree `4a66308ca23710a5fede7b5cfe6f4d4d64cae913`. The corresponding v5 source has SHA-256 `50f92e84c8ccc5a14e8e403b89f4dbd68e798bacce32dd57f40f990de7d06de7`. The authoritative saved source agreed with that baseline. Versions v4 and v5 are preserved.

The Lean baseline remains `1e967bcb913a74ae590dde940f246acaddce1fba`; its immediate manuscript-only successor changed no Lean source. No Lean file is changed in this revision. No fresh Lean build, axiom audit, negative-control run, or independent kernel replay is claimed. Earlier verification remains attached to its original immutable source.

## Checks performed

- The complete v6 source and v5-to-v6 changes received the mathematical-writing review. The revised mathematical argument received a separate hostile review. The abstract and §6 were compared with the actual Lean declarations and instances.
- The new q_A/e_A proof was checked for exact source and target types, identification of the particular structural isomorphisms, use of substitution, preservation of products and coproducts in the quotient, and the final projection-equality argument. Coherence is used only in the original category.
- The Joyal comparison was checked through the hom-set obstruction: at most one arrow from the terminal object to any object, but two distinct endomorphisms of a variable.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex` completed with exit code 0. The final LaTeX log contains no warnings, overfull or underfull boxes, or undefined references.
- All 12 PDF pages were rendered. Both all-page contact sheets and full-size pages 6, 7, 8, and 12 were inspected; no clipping, overlap, broken diagrams, or unreadable bibliography entries were observed.
- All 41 internal references resolve to the 29 unique labels, and all citations resolve to the ten bibliography entries. Source checks found no unfinished markers or editorial-review instructions in the paper.
- Appendices A and B and the existing author-approved disclosure are byte-identical to v5. The bibliography adds the immutable Lean-source reference; prior mathematical citations are retained.
- Revised source and documentation were checked for trailing whitespace. The SHA-256 inventory preserves the v4 and v5 entries and adds v6.

## Final manuscript bytes

| File | Bytes | SHA-256 |
|---|---:|---|
| `Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex` | 39,816 | `2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0` |
| `Maximality_of_the_Dosen_Petric_Boolean_Category_v6.pdf` | 433,598 | `3385c2c2a34482d62de2182e84f2a9c393649e7c9256eadbbd8f8346ada7f0a5` |

These hashes identify the repository artifacts. A separately delivered PDF may carry added provenance metadata; that does not change the repository PDF or its checksum.

## Reviews and delivery boundary

Retained repository reports:

- `docs/DOSEN_PETRIC_MAXIMALITY_NOVELTY_REVIEW_2026-10-25.md`
- `docs/reviews/V6_HOSTILE_REVIEW.md`
- `docs/reviews/V6_WRITING_REVIEW.md`
- `docs/reviews/V6_LEAN_SCOPE.md`
- `docs/V6_VALIDATION.md`

The revised source and PDF replace the existing saved manuscript identities; the corrected novelty report replaces its existing identity. The other reviews receive separate delivered copies.

The WSL repository path `/home/flengyel/src/Dosen-Petric-Maximality` and Downloads directory `/mnt/c/Users/fleng/Downloads` are not accessible from this environment. No WSL copy, local-main synchronization, SSH verification, or byte-for-byte Downloads verification is claimed. Repository delivery uses GitHub, with a guarded update of main and verification of the committed blob identities. The intended Downloads destinations are the five report filenames above under `/mnt/c/Users/fleng/Downloads/`; those copies remain undelivered.
