# V11: supplied BibTeX and prose review — 31 October 2026

V11 uses the author's exact Palomar BibTeX entry and completes a further source
pass for empty qualifiers, unexplained terminology and progress narration. It is
based on the published v10, including the intervening terminology corrections;
it does not restore an older draft over them. Mathematical statements, equations,
diagrams, qualifications and both proof routes are preserved.

## Outline and paragraph functions

| Part | Function |
| --- | --- |
| Abstract and introduction | State maximality, explain isolation/collapse, compare sources and describe occurrence coordinates. |
| 2. Boolean proof category | Define the presentation, zero arrows on inhabited hom-sets, congruences and maximality; state the main theorem. |
| 3. Occurrences and substitution | Define coordinates and labels, state coherence, explain the exponential obstruction and construct substitution blocks. |
| 4. Isolating an occurrence | Construct the two arrows isolating an edge and derive the contextual equation for every formula. |
| 5. Contextual collapse | Establish the two isomorphisms, projection equality, maximality and the model corollary. |
| 6. Lean formalization | Describe syntax and quotient, the theorem hypotheses and their application, both proof routes and registered statements. |
| A.1–A.3 | Define profiles and fibres, ordinal coordinates, skeletons and shared-variable substitution; give the worked example. |
| B. Diagrams for three defining equations | Display and type the distributor, zero-identity and zero-law equations. |
| C. Source corrections | State and explain the two cut-rank errata. |
| Disclosure and references | Retain the author-requested AI disclosure and identify the mathematical and formalization sources. |

The entire source was reviewed across the original text and intervening patch,
including the abstract, proofs, appendices, disclosure and bibliography. The
working source-block function map is retained outside the paper. No reordering
is needed. Mathematical distinctions and explanations used in subsequent
inferences are retained; repeated implementation inventories are shortened.

## Findings and repairs

| Anchor | Difficulty | Decision |
| --- | --- | --- |
| Abstract; introduction | Empty structural qualifiers and a repetitive collapse recap | Preserve v10's removals and remove the recap; state occurrence substitution in finite-ordinal coordinates directly. |
| Introduction; isolation proof | Selector/coselector appeared without explanation | Use precomposition/postcomposition and the already typed arrows i and r. |
| Section 3 | Tensor operations had not been named as such | Say product and coproduct operations. Preserve v10's full, source-checked generator enumeration, including mix and unit maps. |
| Substitution bijection | Canonical added no specified property beyond its construction | Keep the bijection, its tagged definition and proof; omit the adjective. |
| Section 6 | A substitution-closed equation left the object of closure unclear | State totality of a substitution congruence identifying distinct parallel arrows. |
| Section 6 | Normalization and signed-label preservation were used as unexplained field names | Say isomorphisms to negation normal forms and preservation of signed literals along occurrence-relation edges. |
| Section 6 | Implementation inventory and completion phrasing | State the quotient laws, mathematical hypotheses and their application to B(P), preserving substitution on arrow terms and both endpoints. |
| Section 6 | Full interpretations could be confused with full functors | Preserve the intervening wording: interpretations preserving the specified operations. |
| Appendix A.2 | Skeleton was used after an unnamed description | Define skeleton expressly at first use and retain the skeleton/profile correspondence. |
| Appendix A.3 | The object of induction could be stated | Retain the standard term structural induction and add on the formula. Preserve the intervening variable-of-Q paragraph. |
| Bibliography | The hand-written Palomar item differed from the provided entry | Use the supplied entry verbatim through BibTeX, including its key and exact /entry URL. |

Technical qualifications are judged by their mathematical function, not a banned
word list. The sole visible occurrence of structural is now structural induction
on the formula. Internal label keys remain unchanged for correspondence.

## Definition and notation checks

Proof/substitution congruence, thinness/preorder, totality, signed literal,
negation normal form, occurrence profile and substitution are defined before
use. The skeleton definition is now explicit. Mix has its type and formula.
Faithful is explained by the coherence statement; natural has its standard
categorical meaning; uniform is essential to substitution closure and repeated
occurrences. Those qualifications remain. The explicit inverse constructions,
signed-literal cases and inhabited-hom restriction remain.

The descriptions of normalization and relative maximality were checked against
DosenPetric/NormalForm.lean and Substitution.lean: Normalization supplies inverse
arrows to normal forms, and the maximality theorem requires occurrence,
normalization, label, substitution, double-negation and congruence data. This
was a signature/correspondence check, not a new full proof-dependency audit.

All seven theorem/lemma/proposition/corollary statements, displayed mathematics,
ten diagrams and labels match v10 byte for byte. Appendix C and the authorized
AI disclosure are unchanged; MSC codes and the October 31 manuscript date remain.
All earlier manuscript files and packages are preserved.

## Source and inherited decisions

The governing source is Knuth, Larrabee and Roberts's Mathematical Writing,
consulted from the supplied Stanford-course report, Section 1, especially points
8 (padding), 17 (unambiguous reading) and 26 (unnecessary jargon). These support
contextual economy, not a blanket ban on a particular adjective. The specific
repairs above apply the author's instruction and the mathematical context.
Source PDF SHA-256: 9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6. Printed and PDF page numbering differ.

The intervening review docs/reviews/V9_TERMINOLOGY_2026-10-31.md and commits
fd29c0c, 9590145, fd62d26 and 89ebf83 were read and incorporated. Its checked
Došen–Petrić generator enumeration, theorem-hypothesis application, interpretation
wording, variable-of-Q explanation, Appendix B title and version-preservation
policy were kept. The local source was developed in an isolated checkout after
those commits arrived. No additional findings are attributed to the separate
GPT-6 Astra Max session beyond materials actually available in the repository.

## BibTeX, build and scope

manuscript/palomar_v11.bib contains exactly the supplied @misc entry. It is a
standalone database used by the bibliography, not an unused copy. The ten other
sources retain their bibliographic facts. Numeric natbib citations use unsrtnat;
labels now follow citation order. The registered-source note previously added to
the manual Palomar item is attached to the Lean-source reference, so the supplied
Palomar entry has no added fields.

BibTeX and three PDFLaTeX passes returned exit 0. All references and citations
resolved, and the PDF annotation matches the supplied URI. The PDF has 13 pages;
rendered pages 4, 7, 8, 10 and 13 were inspected before a metadata-only
version correction; the final v11 front page was then inspected. No overfull box or BibTeX warning
was found. Four inherited duplicate-destination warnings for equation.6 remain,
as recorded in the intervening baseline review; the disabled-shell-escape
notice also remains. Successful compilation is not described as warning-free.

The arXiv archive contains main.tex, main.bbl and the two .bib databases; all
members are byte-verified. The registered Lean source, toolchain and verification
inputs are unchanged. No Lean rebuild, arXiv upload or registration change ran.
This editorial pass does not newly certify mathematical correctness or novelty.
Process records, source-access information and review status stay outside the
manuscript. Further external-review findings can be reconciled when supplied.
