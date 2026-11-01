# Mathematical-writing review of manuscript v14

1 November 2026. Input: v13 at 50d613e; output: v14, 14 pages. This author-side
AI-assisted review applies the mathematical-writing plugin. It covers the
complete manuscript, abstract, appendices, diagram explanations and authorized
disclosure, not only a list of suspect words.

The main need was to replace labels with mathematical assertions and to show
the calculations hidden in the alternative proof. No occurrence of “actual” or
“genuine” was found in v13. The revision therefore does not claim to remove
those words from that input. It removes other unnecessary descriptions and
adds types without changing the mathematical claims.

## Governing source and actual outline

The governing source is Donald E. Knuth, Tracy Larrabee and Paul M. Roberts,
Mathematical Writing, Stanford CS report, especially Section 1 and Sections 4–5.
The official [Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)
was consulted; a locally retained retypeset copy supplied the same Section 1
points and the discussions in Sections 4–5. The file identities, editions,
printed/PDF locations and inspected passages are recorded in the source record.
Advice below is paraphrased, not quoted. The preference for Došen–Petrić's
terminology is the author's instruction, rather than a rule attributed to Knuth.

The existing organization works and is retained.

| Part | Function and dependencies |
| --- | --- |
| Abstract | State maximality, identify the literal equation and explain how equal projections follow. |
| 1 Introduction | State the conjecture, outline the argument and distinguish relevant categorical antecedents. |
| 2 The Boolean proof category | Define the presentation, arrow operations, witnessed zeros and congruences; state Theorem 2.1. |
| 3 Occurrences and substitution | Define occurrence sets, labels and G; state coherence; explain nonthinness, normal forms and whole-arrow substitution. |
| 4 Isolating an occurrence | Construct the typed i and r; derive K_A for all A using both literal cases. |
| 5 Equality of the product projections | Prove the particular q/e isomorphisms and projection equality; deduce the main theorem and model corollary. |
| 6 Lean formalization | Identify the formal statements and inputs, give the alternative mix argument and describe the registered selection. |
| A.1 Occurrence maps and their fibres | Define the finite occurrence/placeholder functions, D,C and γ; identify the substituted occurrences. |
| A.2 The finite-ordinal presentation | Define θ_D, θ_C and δ; derive the one-based formula and compute an example. |
| A.3 Shared variables | Give the renaming square and its application to both literal cases. |
| B | Display three typed diagrams for the defining equations. |
| C | State the two precisely cited rank corrections and their reasons. |
| Disclosure and references | Retain the author-authorized disclosure and bibliography. |

The central question is whether adjoining any new equation, with closure under
the arrow operations and uniform substitution, makes the presented category a
preorder. The prerequisites are original-category coherence, literal-preserving
normal forms, occurrence selection, substitution and the q/e isomorphisms.
The alternative mix proof is retained as a separate deduction.

## Source comparison and implemented repairs

Section 1 point 5 recommends self-contained theorem statements. Points 10–11
connect formulas with explanatory prose and introduce variables where used.
Point 13 concerns reading prose while skimming formulas. Points 14–15 concern
consistent notation and economical indices. Point 17 concerns unambiguous
sentences, point 24 the opening, and point 26 unnecessary jargon.
Sections 4–5 qualify definition placement and discuss breaking down long
formula manipulations. These are contextual principles; the report's
organization and the author's vocabulary preferences are independent choices.

| Input location | Difficulty | Source principle or independent rationale | Implemented action |
| --- | --- | --- | --- |
| Abstract, p.1, lines 31–38 | “contextual equation” conceals which equation; the negative case is compressed into “substitution.” | Section 1 points 11,13,24; mathematical precision. | State ι₁π₁=0 at the literal endpoints and name double-negation isomorphisms. |
| Section 1, p.2, lines 100–101 | Several external axiom-system names are used without explanation and never used in the proof. | Section 1 point 26. | Describe the proof-net construction and retain its exact theorem citation. |
| Section 2, p.2, line 155 | “distributor” differs from the cited book's name for this particular map. | Author's Došen–Petrić model; book p.234. | Use “dissociativity arrow” in Section 2, the model definition and Appendix B. |
| Sections 2–3, pp.2–5 | The morphism signatures of operations and functors are implicit. | Section 1 points 11,14. | Give types for f∧g, f∨g, ¬f, Gf and f[σ]. |
| Lemma 4.1, pp.5–6 | The normal-form witnesses and their composites must be reconstructed; “tagged path” compresses the recursion. | Section 1 points 10–11,17. | Type both witnesses and composites; name induction on A and on C. |
| Proposition 4.2, p.6 | “Transport” suppresses the two compositions, though the square contains them. | Section 1 points 10–11. | Name precomposition by n_A⁻¹∧1 and postcomposition by n_A∨1. |
| Model discussion, p.7 | “Another interpretation” leaves the substituted valuation implicit. | Section 1 points 11,14. | Type I_v and write p↦I_v(σ(p)); explain operation compatibility. |
| Section 6, p.8 | Two invocations of equations suppress the intermediate terms and the relation calculation. | Section 1 points 10–11; Sections 4–5 on manageable formula manipulation. | Define typed v_A and w_A; display each equality and the terminal inverse equations. |
| Appendix A, pp.9–11 | “Profile,” “encoding” and “locator” add names beside already defined functions. | Section 1 points 13,26 and the author's request. | Use occurrence map, bijection, the function name and the explicit index inequality. |
| Across Sections 3–6 | “Signed literal” adds a redundant modifier to the definition p or ¬p. | Consistent terminology; independent editorial preference. | Use literal throughout, retaining both signs and the negative case. |

## Definition order and notation

The abstract previews literal, projection and injection in their familiar
logical/categorical senses. Their conventions are formally fixed before the
proofs use them. The extra signatures supplement existing definitions rather
than allege that every previously implicit type was a mathematical gap.

| Object or notation | First definition and later use | Disposition |
| --- | --- | --- |
| B(P), arrow equality | Section 2: terms modulo the cited defining equations. | Retained. The proof never substitutes a semantic kernel for this equality. |
| π_i,ι_i,pairing,copairing,!,κ,1 | Section 2, before the equations. | Existing types retained; identity and bifunctor signatures expanded. |
| d | Section 2, with its source and target. | Correct source terminology; unchanged equation and diagram. |
| ¬,n_A | Section 2. | Contravariant arrow action is explicit; n_A and its inverse retain their direction. |
| 0_A and 0_(A,C) | Section 2; the latter requires B(A,C) nonempty. | Retain the existence condition and absorption argument. |
| Congruences and maximality | Section 2, before Theorem 2.1. | Retain operation and substitution closure; do not replace them by composition closure alone. |
| Occ,λ,G | Section 3, before isolation. | State Gf's relation type. Repeated tags and empty sets are retained. |
| Literal,normal form,a_A | Section 3, before Lemma 4.1. | Use literal for p or ¬p; give the normal-form witness types in the proof. |
| F_σ | Section 3, with P,Q,σ. | Give f[σ]'s endpoints; Q may be empty. |
| j_A,K_A | Section 4. | Refer to the displayed equation rather than create another descriptive name. |
| q_A,e_A | Lemma 5.1. | Their full types and inverse argument remain. |
| I_v | Model discussion before Corollary 5.3. | Name and type the functor; explain how its composite with F_σ is induced. |
| h_A,m_A,C,v_A,w_A | Section 6. | Each new intermediate arrow is typed before use; B is the auxiliary formula in the expression for mix. |
| o_M,o_i,D,C,γ | Appendix A.1. | The occurrence maps record enumerated placeholder indices; λ records variable labels. All ranges and the unique-coordinate equations remain. |
| θ_D,θ_C,δ | Appendix A.2. | Keep one-based indexing, zero lengths and the exact coordinate formula. |
| Skeleton,ρ | Appendix A.2–A.3. | Both are defined before the deduction using them; retain skeleton reconstruction and noninjective renaming. |

The ten diagrams still express the same typed equalities. The composition
convention remains g∘f, applying f first. The proof distinguishes equality in
B from equality modulo the congruence. The latter is denoted ≡ after its
declaration. The corrections do not remove any empty-hom qualification,
negative literal, zero-length case or condition on source-variable nonemptiness.

No alternative outline is recommended.

## Priority repairs and exact wording

The principal replacements are implemented, not left as suggestions.

- “The distributor is an arrow” becomes “The dissociativity arrow is,” followed
  by the unchanged typed display.
- “The block encodings are the bijections” becomes “Numbering each disjoint
  union consecutively gives bijections.”
- “Their block locator selects the unique r” becomes “For x∈underline(s_m),
  let r be the unique index with s_(r−1)<x≤s_r.”
- The Section 5 title becomes “Equality of the product projections.”
- The abstract displays the literal equation; the substitution sentence names
  the double-negation isomorphisms.
- The expanded Section 6 proof gives both factorisations and identifies the
  occurrence relation used for coherence.

The exact TeX replacements, the complete final diff and the paragraph-function
record are retained in provenance/manuscript-v14-review-20261101/. The
paragraph-function check includes comparison, motivation, definitions,
construction, proof, example, diagram, source erratum and the authorized
disclosure. It identifies no paragraph whose sole function is an editorial
status update. No such update was inserted.

## Verification and limits

All seven statement bodies are unchanged after normalizing the literal synonym
and the two lemma captions. The 12 numbered displays, ten diagrams and 30 labels
are byte-identical to v13. All bibliography entries and the supplied Palomar
entry are byte-identical. Appendix C and the authorized AI disclosure are
byte-identical. Appendix B's wording uses dissociativity; its mathematics and
diagrams are unchanged.

The manuscript and independently extracted four-member archive compile to
14 pages with identical layout text and 13 bibliography entries. Final logs
have no citation/reference, box or duplicate-destination warning. All 14
rendered pages were inspected on contact sheets; p.8 was additionally viewed
at full-page size. The archive is prepared locally, not uploaded.

Došen–Petrić's relevant definitions and equations were compared with the
September 2007 source, and the expanded alternative deduction was compared
with the retained Lean source. This is not a new exhaustive literature
search, a full re-audit of every citation, a Lean/kernel replay, or mathematical
certification. The earlier citation qualification concerning negation-free
formulas remains in the introduction. No Lean proof, dependency, registered
input, manuscript v13 artifact or prior arXiv package was modified.

