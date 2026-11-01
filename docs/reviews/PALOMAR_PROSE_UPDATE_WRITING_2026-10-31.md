# Palomar public prose: mathematical-writing review

The revised opening and abstract state the presentation and maximality results directly. The supplied opening, abstract, PrimitiveCongruence definition and Total definition are retained verbatim. The additional mathematical scope is stated in metadata with manuscript and Lean references. This review covers registration prose, not a new mathematical milestone or an independent proof certification.

## Source and outline

The governing source consulted is Knuth, Larrabee and Roberts, Mathematical Writing, Stanford CS-TR-89-1193, Sections 1 and 4–5. The Stanford PDF SHA-256 is 646072129e5c74443447d5de1f8343626bcb7cdefb97758721d3ec15d044f5e0. Section 1 was read in the available text edition and checked against the Stanford source; Sections 4–5 were read from the Stanford PDF. Printed pages and PDF pages differ by two.

Challenge proceeds through formulas and tagged occurrences; binary operations and arrow terms; defining equations; Derives; uniform substitution; primitive congruences, closure and totality; and the five selected statements. Metadata proceeds through project and authorship, classifications, sources, scope, automation, fidelity, review and alignment. This order is retained. The central contribution is maximality of the freely generated zero-identity Boolean category, with two proof routes and its congruence dichotomy.

## Findings and repairs

| Location | Difficulty | Source principle or editorial rationale | Repair |
| --- | --- | --- | --- |
| Challenge opening | Compressed terminology and an ambiguous untyped composition convention | Section 1, points 17 and 24: readable sentences and an effective opening | Insert the author's two paragraphs and typed convention verbatim. |
| PrimitiveCongruence, Total and Derives | Empty qualifiers and an incomplete prose account of generated equality | Section 1, points 5 and 11: self-contained claims and explanation of definitions | Define the equivalence relation, its closure operations and totality explicitly. |
| Project description | Registry selection and wider development were mixed | Editorial rationale: state the selected results and their hypothesis together | Use the author's complete abstract; place the broader results in scope and alignment. |
| Source, fidelity and alignment notes | Empty uses of actual and an opaque phrase about diagrams | Section 1, point 26: avoid unnecessary jargon | Name the quotient relation, proof operations, diagram identities and rank inequalities. |
| Release and review status | Earlier release decisions and pending initial registration were stale | Factual correction from the public version record and existing release evidence | Retain Apache-2.0, authorship, source attribution and AI disclosure; identify version 1 and the proposed ordinary update separately. |

## Definitions and correspondence

Formula and Term precede the defining equations. Derives follows those equations and precedes PrimitiveCongruence and the five statements. The opening previews its meaning, and its docstring defines the generated equivalence relation and operation closure. Closed specifies uniform substitution on terms and endpoint formulas. Total quantifies over parallel terms. Empty hom-sets and occurrence tags retain their mathematical meanings. The nonempty-variable hypothesis remains in the three relevant theorem types and the registry abstract. Source-reference labels attached to individual equations are preserved as citations.

The complete revised Challenge documentation and every metadata value, including unchanged automation and source attribution fields, were read in order. The corresponding comments in PresentationSyntax, PresentationEquations, PalomarDefinitions, PalomarCorrespondence and PalomarMaximality were checked and revised consistently. The precise new text and every old/new block are in PALOMAR_PROSE_UPDATE_BEFORE_AFTER.md. No revised outline is warranted.

## Verification scope

YAML passed the pinned v0.4 schema and the official Palomar loader. The full required local check and separate Challenge/Solution targets passed. Source comparison covers every registered Lean file; only comments differ in six. Lean expression serialization additionally confirms identical types and values for 26 declarations, including the five selected proof terms. All manuscript and arXiv-package files remain unchanged. The HTML and Markdown artifacts preview the prepared text; they are not a Palomar Verso rendering. No service review or registration of this update has occurred.
