# Focused mathematical-writing review of manuscript v17

1 November 2026. Author-side AI-assisted review of the eight author-requested
prose/layout changes to v16, input commit
7a5d1cf43aaf1cd5d7497fd5c75034839dedb030. Output: v17, 23 pages.
The revised wording names the relevant maps and equations; the path defining
u_A fits on one line. No unresolved editorial issue was identified in these
changes. This is a focused revision, not a new whole-library mathematical audit.

## Governing source and actual outline

The governing source is Knuth, Larrabee and Roberts, Mathematical Writing,
[Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
Section 1 was consulted in the retained retypeset copy, with particular
attention to points 10–17 and 26. Its advice concerns connected explanation,
declared notation and avoiding unnecessary jargon. The particular objection
to “structural” comes from the author; it is not attributed to the book.
The official/retypeset source identities are distinguished in
provenance/manuscript-v14-review-20261101/source-review-record.json.

| Existing part | Function, retained in v17 |
| --- | --- |
| Abstract and Introduction | State maximality and its relation to the conjecture and literature. |
| Sections 2–3 | Define the category, congruences, occurrences, coherence, signs and substitution. The two generator-case explanations now name their maps. |
| Sections 4–5 | Prove isolation, all K_A, the q/e collapse and the model corollary. |
| Section 6 | Explain the formalization, alternative fold proof and union algebra. |
| A.1–A.3 | Give occurrence maps and fibres, finite-ordinal coordinates, examples and shared-variable substitution. Retained; one induction adjective is removed. |
| Appendices B–C | Give defining diagrams and the two source rank errata. |
| D.1–D.5 | Define terms/equations, read Lean declarations, state the five selections, give congruence correspondence and explain coherence. D.5 now names the maps meant. |
| E.1–E.3 | Construct the q/e inverses and split comparisons. The title names q_A/e_A; the q path occupies one line; the final deduction names its equations. |
| Disclosure and bibliography | Preserve the authorized disclosure and all thirteen bibliography entries. |

The organization is unchanged. No alternative outline is needed for these
local corrections. The prior paragraph-function records remain applicable;
the replacements retain each paragraph's mathematical function.

## Anchored wording review

| Anchor and difficulty | Source principle or explicit rationale | Implemented wording |
| --- | --- | --- |
| p.4, sign proof: “structural generators” does not identify the cases | Author instruction; Section 1 points 11 and 26 support declared, intelligible terminology | The sentence lists the map families and says that they preserve the variable and its sign. |
| p.6, relation proof: the same adjective hides which constructors act on blocks | Same rationale; preserve distinctions between relations and functions | The cases are named and act by “the same tagged relations”; double-negation/De Morgan bijections and empty zero/eta/epsilon relations are specified separately. |
| p.13, A.3: the induction object is already explicit | Author's request for specific wording; economy | “Induction on the formula” retains the exact induction object and deduction. |
| pp.18–19, D.5: “structural arrows/terms” leaves the operations unspecified | Author instruction; consistent terminology and connected explanation | Name the operations sharing notation, then composites, products and coproducts of the maps defining the splitting. |
| p.20, Appendix E title: “two structural isomorphisms” lacks the names | Author instruction; a heading should identify its mathematical objects | “Inverses of q_A and e_A”. Associativity and symmetry are auxiliary maps in the constructions, not the two isomorphisms of Lemma 5.1. |
| p.20, u_A: the path needlessly uses two display lines | Author's layout preference, checked against the rendered page | One unscaled line preserves the four objects, three arrows and their labels. |
| p.22, E.3: “structural arrows and their equations” hides the laws used | Author instruction; specific justification at the point of use | Name the product, coproduct, associativity, symmetry, dissociativity and mix equations. |

These repairs preserve the source/target types and equality directions.
The generator lists refer to the already defined presentation; no new arrow
operation or undefined mathematical term is introduced. The title names
objects already defined in Lemma 5.1. The original label/reference keys remain
unprinted and unchanged, so internal references keep their targets.

The author confirmed that Appendix A belongs in the paper. Its references
from Section 3 and Proposition 4.2 remain. The ordinal substitution comparison
is retained alongside the block substitution used in the main proof; the
question about its use does not authorize removal of any of its mathematics.

## Verification and scope

The complete revised source was searched for the adjective, including headings
and appendices. There is no visible occurrence in the source or PDF text.
The eight replacements were read in context. Undoing them and restoring
suffixes recovers v16 exactly, so unchanged paragraphs retain the prior
complete-source reading and mathematical-function classification.

All seven statement bodies, twelve numbered displays, thirteen diagrams and
34 labels are identical; only the u_A path's alignment markup changes among
its mathematical display tokens. Both bibliographies and the generated
bibliography are byte-identical. The seventeen footnotes and all 49 exact
source URIs remain. No cross-reference or declaration name is renamed.

The manuscript and independently extracted four-member archive compile to
matching 23-page text. All commands returned zero; final logs contain no
reference/citation, box or duplicate-destination warnings. All pages were
inspected on six contact sheets; p.20 was also viewed individually. No
clipping, overlap or unreadable formula was found. The path uses the existing
font size and the bibliography remains on p.23.

This review does not repeat the v16 hostile review, the earlier literature
search, independent checking of every Lean proof body, or Lean/kernel/Palomar
verification. No new mathematical milestone is claimed. The arXiv server
preview remains uninspected because no upload has occurred. The release
provenance records exact edits and build/preservation evidence; the delivery
receipt records committed Downloads copies and verification.
