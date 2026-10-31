# Došen–Petrić v9: terminology revision, 31 October 2026

The supplied terminology findings are resolved by eleven local replacements.
The organization, mathematical statements and proofs remain intact. Section 3
identifies the generator class; Section 6 now describes the hypotheses and their
application directly and uses “interpretations preserving the specified
operations.” The economy edits are editorial choices, not mathematical objections.

The starting source is
[`678ea6d3e15d64ff7dcfb69859ab9723671f0125`](https://github.com/flengyel/Dosen-Petric-Maximality/blob/678ea6d3e15d64ff7dcfb69859ab9723671f0125/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v9.tex),
Git blob `6948568b318b713b582a735cafe3da564de03144`. The revised file is
`manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v9.tex`.
Its title, version and October 30 manuscript date are retained. The editorial
work is dated here rather than narrated in the paper.

## Actual outline and paragraph functions

| Part | Function and dependency |
| --- | --- |
| Abstract and introduction | State maximality, outline isolation and collapse, compare related results, and explain the occurrence-coordinate appendix. |
| §2, The Boolean proof category | Define the formula language, presentation, zero identity and inhabited-hom zero arrows, congruences and maximality; state Theorem 2.1. |
| §3, Occurrences and substitution | Define tagged occurrences and their relations; state Boolean Coherence; explain nonthinness and the exponential obstruction, signed literals, normalization and substitution blocks. |
| §4, Isolating an occurrence | Construct selectors and coselectors for a differing edge, then transport the contextual equation to every formula, including the negative-literal case. |
| §5, Contextual collapse | Establish the two isomorphisms, prove projection equality and maximality, then derive the model corollary. |
| §6, Lean formalization | Describe indexed syntax, the general theorem and its instantiated inputs, both collapse routes, appendix correspondences and the five registered declarations. |
| A.1, Profiles and their fibres | Define profiles and block maps and explain the typed commutative squares. |
| A.2, The finite-ordinal presentation | Relate tagged coordinates to consecutive positions; give the substitution correspondence and a worked example. |
| A.3, Shared variables and the maximality argument | Prove the renaming square by structural induction and apply the construction to the contextual substitution. |
| B, Diagrams for three defining equations | Display and type the first-injection, zero-identity and zero-law diagrams. |
| C, Two corrections to the cut-elimination proof | State the two source errata with their rank explanations. |
| Disclosure and bibliography | Retain the author-authorized acknowledgment and identify mathematical, formalization and registration sources. |

The complete source, including appendices, disclosure and bibliography, was
read. Its prose paragraphs define, construct, prove, apply, compare sources or
guide the reader through dependencies. The occurrence distinctions and the
inhabited-hom restriction serve subsequent inferences. No paragraph was removed
as mere reassurance, and no reorganization was warranted.

## Source basis and decisions

The consulted governing source is Knuth, Larrabee and Roberts,
[*Mathematical Writing*](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1, points 8 and 26 (printed pp. 2 and 5), and §§4–5 (pp. 9–13), particularly
the discussion of nearby definitions, precision and comprehensible sentences.
These support economy and clarity; they do not prohibit particular adjectives.
The replacements below are contextual editorial judgments.

| Manuscript anchor | Difficulty or rationale | Implemented decision |
| --- | --- | --- |
| Abstract, “Two structural isomorphisms” | Unspecified qualifier adds no property. | “Two isomorphisms”. |
| §1, “corresponding structural composite” | The equation already identifies it. | “corresponding composite”. |
| §3, “positive structural generators” | Unintroduced generator class. | Identify identities and the conjunction, disjunction and truth-constant generators, with their names. |
| §6, opening paragraph | “Structural operations” has no defined extension here. | “operations of the presentation”. |
| §6, general theorem paragraph | Describe mathematical hypotheses directly. | Replace “Its arguments include” by the specified hypotheses. |
| §6, presentation paragraph | “Instance of every hypothesis” misdescribes application. | State that the constructed data verify the hypotheses and that `Presentation.maximality` proves maximality of the presentation. |
| §6, model corollary | “Full” could suggest a full functor. | “interpretations preserving the specified operations”. |
| §6, appendix correspondence | “Concrete source” is uninformative and ambiguous. | “cut reductions and rank comparisons discussed in Appendix C”. |
| A.1, substitution paragraph | “Actual” adds no distinction. | “pattern substitution”. |
| A.3, renaming paragraph | Name the variable set instead of using “actual”. | Say that a variable of Q can occur in several patterns while pairs distinguish its occurrences. |
| Appendix B heading | Name its three displayed equations. | “Diagrams for three defining equations”; keep its label. |
| A.3, induction argument | A standard proof-method name with stated cases. | Retain “structural induction”. |

The generator clarification was checked against the September 2007 author
version of Došen and Petrić,
[*Proof-Theoretical Coherence*, §14.2, printed p. 318](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf#page=330).
The primitive families there are `1, b, c, w-k, m, d, δ-σ, 0`, followed by the
literal-indexed eta and epsilon arrows. This supports the enumeration while
keeping the three empty-relation cases separate. The source's formula language
uses signed literals as object generators.

## Definition order and notation

The formula language and B(P) are introduced in §2, followed by the zero identity,
the nonempty-hom condition for zero arrows, proof and substitution congruences,
thinness and maximality. §3 introduces occurrence coordinates and labels before
the signed-literal and normal-form discussion. Its canonical substitution
bijection has a recursive explanation. Interpretation is defined immediately
before Corollary 5.3, so the revised §6 phrase refers to specified preservation
laws without adding a fullness assumption.

Appendix A.1 defines profiles and block maps before their use; A.2 explains
erasing placeholder names before using “skeleton.” A.3 introduces Q and the
renaming map before the edited sentence. “Exactly one,” the explicit inverses,
tagged occurrences and all typed diagrams are retained. Abstract and introduction
previews do not create missing definitions. No new terminology or mathematical
hypothesis is introduced by these edits.

## Principal replacement passages

Section 3:

```latex
Indeed, the equivalent presentation of \cite[\S14.2, pp.~318--321]{DP}
has signed literals as generators. The identity arrows and the generators
for conjunction, disjunction and the truth constants (associativity,
symmetry, diagonals and codiagonals, projections and injections, mix,
distribution and unit maps) preserve these labels. Zero endomorphisms
and the arrows $\eta_p$ and $\epsilon_p$ have empty relations.
```

Section 6:

```latex
For the presentation defining $\B(P)$, the development proves cut
elimination and Boolean Coherence and constructs normalization,
signed-label preservation, and uniform substitution on arrow terms
and their source and target formulas. These constructions verify the
hypotheses of \texttt{relative\_maximality}. The theorem
\texttt{Presentation.maximality} proves maximality of $\B(P)$.
```

The model-corollary sentence is now:

```latex
The model corollary is proved using interpretations preserving the
specified operations and their composition with substitution.
```

The pertinent declaration signatures and applications were inspected in
`DosenPetric/Substitution.lean`, `PresentationMaximality.lean`,
`SemanticInterpretation.lean` and `SemanticModelCorollary.lean`.
They support these local descriptions. This was not a new audit of every Lean
claim in §6 or of the full proof dependency closure.

## Verification, scope and delivery

`latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error`
compiled the revised manuscript successfully. The package's identical `main.tex`
also compiled successfully. Both PDFs have 13 pages with resolved references and
citations and no overfull boxes. Rendered pages 1, 4, 7, 8, 10, 11, 12 and 13
were inspected for the changed passages, diagrams, disclosure and bibliography;
no clipping or overlap was observed there.

The final log has four duplicate-destination warnings for `equation.6` and one
underfull bibliography line (badness 7291). Compiling the exact original source
reproduced both. The present edit does not change the hyperlink machinery.
These inherited warnings are recorded rather than reported as a warning-free
build.

Byte comparisons preserve all 10 TikZ diagrams, 12 numbered equation
environments, all unnumbered displays, 2 theorem environments, 1 proposition,
3 lemmas, 1 corollary and 6 proof environments. Existing inline formulas remain
in order; only B(P), B(P) and Q were added to the explanatory prose. All labels,
reference and citation commands, the bibliography and disclosure are identical.
The two proof routes and all mathematical qualifications are retained. Printed
prose has no remaining “actual,” “full” or “concrete”; “structural” remains in
“structural induction.” Labels and reference keys are deliberately unchanged.

The arXiv archive contains only `main.tex`, byte-identical to revised v9.
Its abstract text, JSON fields and recorded source/PDF/archive hashes are
synchronized. No Lean source, comparator or toolchain is edited, and no Lean
rebuild was needed. The registered source citation remains
`2e771844077fd8cebfbe365230f13d4dd13a75b1`.

This closes the supplied editorial findings. It does not certify mathematical
correctness or novelty, reaudit Appendix C's errata, recertify registration, or
perform an arXiv upload. Other cited literature was not reread for this revision.
No correctness or novelty claim was withdrawn on the basis of the prose review.

The retained report is `docs/reviews/V9_TERMINOLOGY_2026-10-31.md`.
Its Downloads counterpart is
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-v9-terminology-20261031.md`.
The delivery register records exact committed-byte copies and their SHA-256
values, preserving differing older Downloads files. Compact source, build and
package records are under `provenance/wsl-v9-terminology-20261031/`.
