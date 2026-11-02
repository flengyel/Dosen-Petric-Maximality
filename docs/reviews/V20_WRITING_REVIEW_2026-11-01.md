# Mathematical-writing review of manuscript v20

1 November 2026. Author-side AI-assisted review using the mathematical-writing
skill. Input: v19 at e1b4a6bdd49be2b7f99342cce30879c494ae909e.
Output: v20, 23 pages. The descriptive statement now precedes its technical
name, and its quantification over every nonderivable equation is visible.
No remaining defect was identified in the changed wording and correspondence.

## Source, scope and actual outline

Governing source: Knuth, Larrabee and Roberts,
[Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
Section 1 was consulted in the retained retypeset copy: point 5 on
self-contained statements, 10–11 on connected exposition and complementary
explanations, 12–13 on the reader and prose around formulas, 17 on parsing,
24 on openings and 26 on jargon. These contextual principles support stating
the result and then explaining its conventional name. They do not prescribe
the exact words or this report format. The author's preference for descriptive
collapse language determines the local repair. The prior v18 consultation of
the official report's abstract discussion remains applicable; its exercise
length is not treated as a universal rule.

The outline remains: abstract (context, result, proof method, model and Lean
scope); §1 Introduction (problem and literature); §2 category, congruences and
main theorem; §3 occurrences, coherence and substitution; §4 isolation and
all K_A; §5 q/e collapse and model corollary; §6 formalization, symmetric fold
and union; A.1–A.3 occurrence maps/fibres, ordinals and shared variables;
B three defining diagrams; C two source corrections; D.1–D.5 terms, reading
Lean, selected statements, congruence correspondence and coherence proof;
E.1–E.3 q/e inverses and split comparisons; disclosure and references.

The question is whether every nonderivable parallel-arrow equation forces
thinness after the specified closure. Theorem 2.1 answers it affirmatively.
Its proof needs coherence, literal isolation, uniform substitution, double
negation and the q/e isomorphisms. The model corollary uses the congruence
defined by agreement of every interpretation. The existing order supplies
these dependencies; no reorganization is needed.

## Diagnosis and repairs

| Anchor | Difficulty | Source principle or rationale | Implemented repair |
| --- | --- | --- | --- |
| Abstract and §1, p.1 | “Is maximal” names the result before describing it; a shorthand proper-extension claim conceals the quantifier at issue. | §1 points 12–13, 24, 26; author's specific instruction. | Say that any parallel equation not following from the defining equations causes collapse under both closure conditions; explain equality of all arrows with the same endpoints. |
| §2, p.3 | Totality language requires the reader to translate the conclusion into categorical collapse. | §1 point 11, complementary explanations. | Define the quotient and say it is a preorder exactly when the congruence is total. |
| Theorem 2.1, p.3 | Conclusion stated by the technical name and an equivalent congruence assertion. | §1 point 5, self-contained statement; preserve quantifiers. | Retain P nonempty, freeness and every substitution congruence identifying a distinct pair; conclude that its quotient is a preorder. |
| Paragraph after Theorem 2.1, p.3 | The conventional name still needs its mathematical meaning. | §1 points 10–11; author's instruction. | Explain maximality through collapse for every nonderivable equation and the equality/totality dichotomy. |
| Main and model proofs, p.9; D.4 p.18 | Subsequent uses must match the restated conclusion. | Definition/notation consistency and elementary quotient reasoning. | Use Lemma 5.2's thinness conclusion; explain the thinness/totality conversion where needed. |

The exact result wording is reproduced in the
[release report](../MANUSCRIPT_V20_REPORT.md). The eight replacements are
recorded in [edits.json](../../provenance/manuscript-v20-review-20261101/edits.json).
The descriptive sentence is the principal repair; the three proof/correspondence
changes make its mathematical translation visible at the points of use.

## Definition order, typing and quantifiers

Parallel means same source and target, defined before Theorem 2.1.
Proof congruence and substitution congruence retain their definitions before
the theorem; substitution acts on the term and both endpoint formulas.
Totality concerns every pair in each hom-set. Thin/preorder means at most
one arrow, so empty hom-sets remain allowed. The quotient now has its same
objects and equivalence-class arrows stated before its first theorem use.
The conventional name maximality is informally explained in §1 and precisely
explained after Theorem 2.1. Abstract previews of these terms are appropriate.

The theorem quantifies over every substitution congruence with the distinct-pair
hypothesis. The explanatory equation is an equation of parallel arrow terms
outside the defining equality, rather than an equation already true of its
classes. Closure under every arrow operation and uniform formula substitution
is retained. The original category's nonthinness and the model corollary's
universal interpretation hypothesis remain. No type, quantifier, equality
direction or inhabited-hom requirement is lost.

The thinness/totality equivalence was checked against the existing proof in
CongruenceQuotient.lean:93, unchanged at registered source 5dbee39bea09539bd130f729e82636419f71f920.
It uses equality of quotient classes in one direction and equality induced by
related representatives in the other. The comparison with Došen–Petrić's
[§9.3 definition](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf#page=206),
printed p.194 of the September 2007 revision, retains the same universal
condition. No new bibliography claim or primary-source reference is introduced.

## Prose pass and verification limits

The complete source, including appendices, comments and the authorized
disclosure, was read continuously for dependencies, vague qualifiers and
editorial narration. Existing paragraph classifications are retained for the
unchanged text. The revised paragraphs introduce the problem, state the
result, define quotient objects/arrows, explain the conventional name, or
deduce the restated conclusion; their functions are recorded separately.
No process commentary was added to the paper. The earlier adjective repairs
and the single-line comparison/path layouts are preserved.

The source and independently extracted archive compile to matching 23-page
layout text without final warnings. Six contact sheets cover all 23 rendered
pages; pages 1 and 3 were also inspected individually. Statement, equation,
diagram, label, footnote, URL and prior-release preservation checks are in
[validation](../../provenance/manuscript-v20-review-20261101/validation.json).
Theorem 2.1 is logically equivalent; six other statement bodies are unchanged.

This is a focused writing and correspondence review with a whole-source prose
pass, not an independent new proof-body audit, novelty review, hostile review
or mathematical certification. Lean builds, kernel replay, Comparator and
Palomar checks/registration were not repeated. Previous reviews retain their
original scope. The manuscript has not been uploaded to arXiv.

Retained review: docs/reviews/V20_WRITING_REVIEW_2026-11-01.md.
Delivered review: /mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v20-20261101/V20_WRITING_REVIEW_2026-11-01.md.
Delivery is from committed bytes, verified in the release receipt.
