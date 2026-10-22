# Contextual factorization: mathematical-writing review

The construction descriptions now state four unconditional reduced equalities,
with the source's atomic η/ε instances identified explicitly. They distinguish
the printed base-case discrepancy, syntactic equality and occurrence comparison.
The exposition does not promote these results to reduced faithfulness.

This is an author-side, AI-assisted review of the five new modules, the new
correspondence section, scope maps and contextual factorization report.
The manuscript is Florian Lengyel, *Maximality of the Došen–Petrić Boolean
Category*, v4, 21 October 2026; its text, figures, references and comments are
unchanged. No whole-manuscript editorial judgment is made.

The governing Knuth–Larrabee–Roberts *Mathematical Writing* source was consulted
directly in `.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf`,
SHA-256 `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
It is the 119-page MIT-hosted typeset course report, not a verified byte copy
of the Stanford scan or the MAA edition. Section 1 and §§4–5 were consulted;
§1 points 5 and 10–15 occur on printed pp.2–3 / one-based PDF pp.4–5,
and §§4–5 on printed pp.9–13 / PDF pp.11–15. Historical provisional reviews
and access records remain unchanged. This review is source-grounded for those
passages; the applications and report format are editorial judgments.

## Actual outline and contribution

| Existing sequence | Function |
| --- | --- |
| Report: proved endpoint and exact hypotheses | States arbitrary P, existing h/f, equality in Reduced.Hom, atomic specializations. |
| Source correspondence and discrepancy | Fixes composition notation and all recursive intermediate types before using the factorization displays. |
| Structural, context and zero derivations | Explains congruence preservation, quotient action and the direct proof replacing the source's coherence invocation for these instances. |
| Occurrence coordinates | Separates tag embeddings from labels and compares relations only after explicit endpoint embeddings. |
| Verification and remaining work | Supplies evidence and preserves the boundary to common atomic factorization, §12.5 and Boolean Coherence. |

The contribution is an unconditional contextual factorization, not an
equality-reflecting functor. This order follows the dependencies. No revised
outline or manuscript diagram is warranted; the typed paths already expose
the intermediate objects that matter.

## Comparison with the governing source

| Anchor | Difficulty / risk | Verified source principle or independent rationale | Applied wording or decision |
| --- | --- | --- | --- |
| Report, exact hypotheses | “gη is proved” could conceal a coherence assumption or a unit-domain restriction. | §1 point 5: statements should ordinarily state their own assumptions. | State every P, K, existing h and f; specify the ambient Reduced.Hom equality and atomic specializations. |
| Correspondence, notation before tables | Reverse mathematical composition and Lean execution order can interchange arrows. | §1 point 14: consistent notation; independent typing rationale. | Define semicolon as execute the left arrow first, and list every intermediate type. |
| Disjunctive hole row | Silently changing top to bot would hide a discrepancy in the reference. | Independent source-fidelity rationale; §1 point 11 supports complementary explanation. | State the rendered display, general type, Table 2 unit definition and implemented typed map separately. |
| Structural proof paragraph | A dense chain could hide the actual input replacing the source's coherence step. | §1 points 10, 12–13: connected explanatory prose and motivation for formulas. | Explain naturality, unit components, reduced uniqueness and composed forms in that order. |
| Occurrence comparison | “Same pairs” suppresses a changed domain/codomain. | Independent typing rationale; §1 point 14. | Use `Sum.inl x` or `Sum.inl y` at the relevant endpoint. |
| Scope maps, next task | Contextual equality could be mistaken for faithfulness of all arrows. | Independent mathematical-scope rationale. | State that common atomic factorization, §12.5 coherence and Reduced.Faithful remain open. |
| Definition placement | Repeating all earlier categorical definitions would obscure the new point. | §§4–5 treat placement in context, rather than as a rigid rule. | Reuse existing NormalForm, Term, Derives and Hom; define K, X/Y, E/D and execution order locally. |

## Definition-order and notation audit

NormalForm, the restricted Term grammar, Equation/Derives and the quotient
precede every new construction. Context precedes plug and mapTerm;
map_derives precedes map. Raw and quotient functor laws precede use of the
quotient action in the g identities. Both source g recursions precede their
naturality and unit components. Reduced terminal/initial/zero uniqueness
is proved before the factorization argument uses it.

Fixed tags, encode/decode and embeddings precede occurrence_map. An occurrence
tag and its signed literal are different data. Fixed formulas can repeat the
inserted formula without becoming holes. The top/bot occurrence lemmas
explicitly eliminate empty hole occurrences. These definitions are confirmed,
not missing-definition findings.

The report uses h for the generalized unit-domain/codomain arrow and f for
the additional composed arrow, and names the atomic η/ε instances separately.
The table defines source/Lean symmetry conventions before the paths. It does
not call object duality a contravariant arrow operation.

## Prioritized wording

The consequential wording is retained directly: “The four contextual
factorizations are equalities in the equation-generated reduced quotient,
without a coherence hypothesis.” Follow it by: “The source's atomic cases
are specializations to h = η_p or h = ε_q.” For the relation comparison use:
“The input x corresponds to Sum.inl x,” and the dual sentence for y.
For the limitation use: “Common atomic factorization and the §12.5 coherence
input remain open.” These repairs are in the actual correspondence and scope
records; no manuscript revision is needed.

## Scope

The complete new construction and its descriptions were reviewed. The cited
book pages and cached governing writing passages were available and consulted.
This is neither a whole-paper review nor independent mathematical certification.
No fresh manuscript compilation/layout audit, novelty search, independent
kernel replay or service verification was performed. Existing manuscript hashes
passed. Historical source-access records and all earlier review reports are
preserved. Review/process commentary remains outside manuscript v4.
