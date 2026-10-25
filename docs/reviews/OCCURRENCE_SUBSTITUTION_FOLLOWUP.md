# Occurrence-substitution follow-up

No necessary mathematical or writing correction was identified in the reviewed
occurrence-substitution passages. The tagged-block construction, the ordinal
coordinate formula and the renaming argument agree with the cited source. The
instructions now preserve this exposition as required content and require its
formal correspondence, together with verification of any future corrections.

Reviewed on 25 October 2026: manuscript v6, §3's occurrence substitution,
Proposition 4.2 and Appendix A. The source is fixed by commit
`810dcdbccc76a4307028773c561f36b910b5170c` and SHA-256
`2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0`.
The saved complete v6 writing and hostile reviews were consulted for outstanding
repairs; neither records one. This follow-up is a focused check, not a new
complete-manuscript review.

## Outline of the reviewed material

| Passage | Mathematical function |
|---|---|
| §3, equations (4)–(5) | Describe substituted occurrences by pairs, distinguish positions from labels, and display the block-label square. |
| Proposition 4.2 | Apply uniform substitution to a contextual equation, treating positive and negative literals and double-negation transport. |
| Appendix A.1 | Define profiles, source and target blocks, the unique map gamma, its two block squares, and the actual-substitution bijection chi. |
| Appendix A.2 | Change to ordinal coordinates, recover the published formula, relate skeletons to profiles, and compute the eight-position example. |
| Appendix A.3 | Permit shared variable names through noninjective renaming and connect the construction to Proposition 4.2. |

The order introduces the mathematical data before their coordinate encoding.
No rearrangement is needed.

## Source comparison and findings

The primary comparison used Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007, §2.5, printed pp.45–46 (PDF pp.57–58), including the displayed
generalized-composition formula and block locator. On printed p.46 the authors
describe that definition as “pretty opaque.” The source is available at
<https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf>.
This wording confirms the source description; it need not be inserted in the
manuscript, whose construction already explains the relevant structure.

The writing check used the supplied Knuth–Larrabee–Roberts, *Mathematical Writing*,
§1, especially points 10–15: connected explanations, complementary descriptions,
reader motivation, consistent notation and economical indices. The specific
formalization requirements below are project requirements, not claims about
KLR's instructions.

| Manuscript anchor | Finding and evidence | Action |
|---|---|---|
| §3, `eq:occ-substitution`, `eq:block-square` | The pair (x,t) keeps the outer occurrence and the position within its substituted copy. The square records the variable whose block is used; it does not identify repeated source occurrences. | Preserve the construction and its explanation; prove the stated bijection and square in Lean. |
| Appendix A.1, `eq:app-fibre`, `eq:app-profile` | Every source pair lies in exactly one a_r block. The required restriction on that block uniquely defines gamma(r,t) = (o_M(r), o_(o_M(r))(t)); both displayed routes have the stated types. | No repair required. Formalize existence and uniqueness, not only a function with the intended name. |
| Appendix A.1, `eq:app-occurrence-labels` | Renaming local placeholders to (i,s) gives the stated chi bijection and label identity. Repeated values of the outer profile retain separate source blocks. | Preserve explicit placeholder and occurrence distinctions. |
| Appendix A.2, `eq:app-ordinal`, `eq:app-coordinate` | Delta is theta_C composed with gamma composed with the inverse of theta_D. For a source position x, the unique nonempty block has s_(r−1) < x ≤ s_r, reproducing the book's locator and both offsets. Empty blocks cause no ambiguity. | No repair required; retain the exact source correspondence and verify both coordinate inverses. |
| Appendix A.2, reconstruction and example | A fixed placeholder indexing, skeleton and occurrence profile reconstruct the pattern. The computed profile is (4,3,4,1,2,4,3,4), so delta(2)=3 as stated. | Keep the reconstruction claim and the worked calculation in the full-paper obligations. |
| Appendix A.3, `eq:app-renaming` | Structural induction proves substitution followed by rho-renaming equals the stated substitution. Rho need not be injective; renaming changes labels while retaining the occurrence positions. | No repair required; do not introduce an injectivity hypothesis in Lean. |
| Appendix A.3 and Proposition 4.2 | The positive substitution gives A∧bot → A∨top; the negative case first gives ¬¬A∧bot → ¬¬A∨top and then uses the typed double-negation square. Constants contribute no extra occurrences. | No repair required. |

## Definition order and notation

The reviewed passages define profiles, dependent block sets, injections, block
projections, coordinate encodings and renaming maps before their mathematical
use. The source position, index of an inserted pattern and index of a local
placeholder have distinct roles. The skeleton/profile sentence uses the
placeholder indexing already fixed in A.1. All displayed maps remain defined
when some blocks are empty, subject to the stated existence of the profile maps.

These complementary descriptions serve different purposes: the block maps
describe substitution; ordinal encodings recover the source formula; the
example checks the offsets; renaming handles repeated actual variable names.
They are not redundant exposition. The manuscript's existing organization and
wording can be retained.

## Required instruction changes

The full-paper contract now explicitly treats the tagged-block and diagrammatic
presentation as an expository contribution whose exact mathematical
correspondence must be verified. An implementation of the ordinal formula alone
does not discharge that requirement. It also includes necessary corrections to
statements, proofs, correspondence, citations and exposition, with an external
correction record and a verification requirement before completion.

No change to the manuscript is required by this focused check.

## Scope

This check compared the mathematical source passages and the cited printed
formula, including the empty-block and repeated-label cases. It inspected the
source page containing the original formula. It did not rebuild the unchanged
manuscript, inspect every rendered v6 page again, rerun Lean, reprove Boolean
Coherence, or establish priority for the occurrence-coordinate presentation.
The final v6 compilation and layout checks remain recorded in
[V6_VALIDATION.md](../V6_VALIDATION.md).

The WSL Downloads directory is inaccessible in this environment. The retained
report is `docs/reviews/OCCURRENCE_SUBSTITUTION_FOLLOWUP.md`; the requested
Downloads copy of that filename has not been delivered or verified.
