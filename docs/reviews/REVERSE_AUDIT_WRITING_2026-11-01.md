# Mathematical-writing review: Lean to manuscript

1 November 2026. Manuscript: Maximality of the Došen–Petrić Boolean Category,
v15, 16 pages, at f869fe74e9cc713ad366b51fad16d5de357fe74a. Author-side
AI-assisted review applying the mathematical-writing plugin. This is a content
audit with exact proposed additions, not a new manuscript release.

The useful change in direction is to ask what the formal mathematics contains
that a mathematical reader cannot find in the paper. A list of Lean identifiers
does not by itself explain those constructions. The report supplies the
statements, types and deductions for seven candidate additions and distinguishes
them from proof machinery that can remain in the library.

## Governing source and actual outline

The governing source is Knuth, Larrabee and Roberts,
[Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
Section 1 and Sections 4–5 were consulted in the official source and the
retained retypeset copy. Section 1 points 5 and 10–11 support complete
statements, formulas connected to prose and variables introduced before use.
Points 14–15 support consistent notation; point 26 concerns jargon.
Sections 4–5 distinguish mathematical exposition from program notation and
treat definition placement in context. These principles guide the proposed
wording; the source does not prescribe this report's format or demand that
every auxiliary Lean lemma appear in a paper.

The current outline is retained.

| Part | Function |
| --- | --- |
| Abstract and Introduction | State maximality, reduction to a literal equation and the literature comparison. |
| Section 2 | Define the category, witnessed zeros and congruences; state Theorem 2.1. |
| Section 3 | Define occurrences, G, coherence, normalization and substitution. |
| Section 4 | Isolate one occurrence and obtain K_A for every A, with both signs. |
| Section 5 | Prove q_A/e_A invertible, collapse products, deduce maximality and the model corollary. |
| Section 6 | Describe formal statements and the symmetric-fold proof. |
| Appendix A | Relate tagged occurrence substitution to finite ordinals and shared variable names. |
| Appendix B | Give three typed defining diagrams. |
| Appendix C | Give the two precisely cited source-rank corrections. |
| Appendix D | State the five selected Lean declarations and the term/arrow correspondence. |
| Disclosure and references | Retain the authorized disclosure and sources. |

The central question remains whether a new parallel-arrow equation under
uniform substitution makes the presented category thin. Its short proof needs
isolation, substitution and the particular q_A/e_A isomorphisms. The new
audit does not change that theorem or its dependencies.

## Comparison and recommended action

| Manuscript location | Actual omission or distinction | Rationale and concrete action |
| --- | --- | --- |
| Section 3, p.5 | Blocks describe the substituted endpoints without stating which substituted occurrences are joined | Add R1's relation formula and square; compare pairs in E_sigma to preserve typing. |
| Lemma 5.1, pp.6–7 | Explicit inverses are in Lean, while the paper uses a cited existence argument | R2 gives the actual inverse terms and four equations; a typed five-step composite explains the map inside e_A inverse. |
| Section 6, pp.8–9 | Mix is defined but the induced union on parallel arrows is absent | R3 gives the binary operation and its laws, cites its antecedent, and states the witness needed for zero. |
| Section 3 / D.1 | Functoriality in an arrow is stated; the laws for composing substitutions are absent | Add R4 next to R1, with both formula equalities identifying endpoints. |
| Proposition 4.2, p.6 | Only the double-negation instance of retract transport is used | R5 gives one short lemma with r∘i=1_A; the current special-case proof remains adequate. |
| Section 3, p.4 | Equal literal labels are stated only at normal-form endpoints | R6 records sign preservation on arbitrary formulas and the converse relation under negation. |
| Section 6 / D | Coherence is said to be proved without describing its constructed comparisons and normal forms | R7 supplies a mathematical proof outline; keep the hundreds of indexed reduction lemmas in the code. |

The first two proposals are the clearest improvements to self-containedness.
R4 belongs with R1. R3 and R7 are useful if the paper is to explain more of
its formal coherence proof. R5 and R6 can remain brief. No rearrangement of
the main proof or wholesale new section is required.

## Definition order, notation and typing

Confirmed existing definitions include parallel arrows, proof/substitution
congruence, the total congruence, literal, occurrence tags and labels, witnessed
zero, the substitution functor, the occurrence maps and ordinal coordinates.
The review does not call these undefined or remove their substantive hypotheses.

The proposed R1 uses the already defined common disjoint union E_sigma when
comparing inner occurrences. An equality t=u without their common label
would suppress a necessary type condition. The square is explicitly in the
category of finite sets and relations; its vertical bijections are regarded
as their graphs.

R2 defines every auxiliary arrow before using it. Its associativity arrow has
source (X∧Y)∧Z and target X∧(Y∧Z); its coproduct symmetry has source U∨V
and target V∨U. Each step of the mixed comparison has its endpoints printed.
The inverse of e_A uses the witnessed zero from A∧top to A∧A, for which
Delta_A∘pi_1 is explicitly supplied. These formulas do not rely on an
unexplained term such as “comparison” in place of its definition. The q_A
inverse is displayed directly so it does not reuse the paper's normalization
symbol a_A for a different map.

R3 distinguishes the theorem in the reduced category from its transfer to
B(P). It gives a definition in B(P) and explains reduction/recovery before
passing the laws across. R4 distinguishes equality of formulas, equality of
arrows and the endpoint identifications needed for the latter. R5 uses a
retraction rather than demanding an unnecessary two-sided inverse. R6 defines
occurrence sign by parity before stating its preservation. R7 distinguishes
DNF/CNF retracts from the NNF isomorphisms used earlier in the paper.

“Only constant substitutions are used,” the empty-variable case and finite
hom-set bounds are marked as deductions or possible sharpenings. They are
not labelled separately registered Lean results. Appendix D already explains
the weaker congruence fragment; that explanation is not reported as missing.

## Proposed wording and scope

Exact mathematical wording, equations and the new square are supplied in
[the audit report](../FORMALIZATION_TO_MANUSCRIPT_AUDIT_2026-11-01.md), R1–R7.
The leading prose states what each construction does and why it belongs at
the proposed location. No report terminology or review-process narrative is
proposed for the manuscript. The supplied BibTeX and author-authorized disclosure
remain unchanged. The new writing avoids empty adjectives and does not import
the code's internal replacement/routing names into mathematical exposition.

The complete v15 source was read for content and absence searches. The reverse
inventory covers all production modules; detailed source reading is recorded
separately. No independently rechecked proof of every internal Gentzen lemma
or complete new literature search is claimed. The primary book source was
checked for the union antecedent, so its omission is not described as a new
discovery. The existing paper's cited proof is not called unproved.

V15 and its PDF/source package are preserved byte-for-byte. Their successful
build and inspection are reused. No revised paper or report PDF was compiled;
the proposed additions have been checked mathematically and remain in this
review report. A later manuscript release incorporating them must be v16 or
later, preserving v15. Delivery and remote synchronization are separate recorded
steps, not material for the mathematical text.
