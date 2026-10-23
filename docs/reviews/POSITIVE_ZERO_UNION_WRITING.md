# Positive zero and union: mathematical-writing review

The report leads with the proved algebra and its exact witness requirements.
Typed paths explain the derived union before the laws; the dependency table
separates this algebra from unconstructed Gentzenization and coherence. The
organization is suitable for the next proof session without revising manuscript v4.

This is an author-side, AI-assisted review of ReducedZeroAlgebra, ReducedUnion,
ReducedUnionOccurrences, their correspondence section, report and scope maps.
The manuscript is Florian Lengyel, Maximality of the Došen–Petrić Boolean
Category, v4, 21 October 2026. Its text, diagrams, Appendix A references and
comments are unchanged. No whole-manuscript editorial judgment is made.

The governing Knuth–Larrabee–Roberts Mathematical Writing was consulted
directly from `.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf`,
SHA-256 `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
This is the 119-page MIT-hosted typeset course report, not a verified byte copy
of the Stanford scan/MAA edition. Section 1, printed pp.1–6 / PDF pp.3–8,
was consulted, particularly points 5 and 10–15 on printed pp.2–3 / PDF pp.4–5.
Sections 4–5, printed pp.9–13 / PDF pp.11–15, give contextual advice on
placing definitions near use. Historical provisional reviews and access
records remain unchanged. This review is source-grounded for those passages;
the workflow and mathematical-scope decisions are editorial judgments.

## Actual outline and contribution

| Existing report sequence | Function and prerequisites |
| --- | --- |
| Exact endpoints and hypotheses | States arbitrary P, witnessed zeros, both-zero tensors, parallel union laws and pointwise interpretation. |
| Source correspondence and direct derivations | Identifies the source's two syntaxes, composition order, typed intermediate objects, and the p.291 proof. |
| Proved declaration inventory | Locates the implementation and separates quotient algebra from raw positive membership. |
| Verification and evidence | Gives actual exits, counts, control outcomes, hashes and verification boundaries. |
| Remaining dependency table | Defines proposed types before the typed open statements and their predecessors. |
| Remaining obligations and next theorem | Names Gentzenization first and preserves the distinction between coherence and maximality. |

The contribution is zero/union algebra inside the existing reduced syntactic
quotient, with its occurrence interpretation. No revised outline is needed.
The explicit linear typed paths suffice here; no new diagram or manuscript
layout change is warranted.

## Comparison with the governing source

| Anchor | Actual exposition risk | Verified principle or editorial rationale | Applied wording / decision |
| --- | --- | --- | --- |
| Exact endpoints | A bare zero symbol could conceal a required arrow witness. | §1 point 5: self-contained theorem statements. | Define `z_f := zero A ; f` with f : A → B; state independence of f separately. |
| Tensor law | “Tensor absorbs zero” suggests the false one-zero rule. | §1 points 11 and 14: explain symbols and use consistent notation; independent scope check. | Say “both tensor factors are zeros” and display the two-zero equation. |
| Union definition | Prose connectives in a path could be read as conjunctions of claims. | §1 points 10–11: complement formulas with connected explanation. | Use the exact path A → A∧A → B∧B → B∨B → B. |
| Source p.220 versus p.291 | An alternative Gentzen axiom could be mistaken for a Reduced generator. | Independent source-fidelity rationale. | State that union and its unit law are derived in the category used here. |
| merge/pair proof | Repeated full expansions obscure associativity. | §1 points 12–13 and §5 discussion of naming a reused expression. | Define merge with type B∧B → B before merge_nat/assoc, then explain the triple-pair proof. |
| Relation theorem | Interpretation equality might be read as syntactic faithfulness. | Independent mathematical-scope rationale; §1 point 14 on distinct notation. | State the pointwise disjunction with explicit x/y, and keep the syntactic proof separate. |
| Dependency table | Proposed Lean names could appear to be implemented declarations. | §1 point 5; §§4–5 qualify definition placement. | Introduce each planned syntax and label every G0–C row open before giving its typed target. |
| Final scope | Signed-label preservation could be mistaken for fullness. | Independent logical distinction, not a writing rule attributed to the source. | Say no realization theorem for all signed-label-respecting relations is assumed. |

## Definition order and notation

NormalForm, Term, Derives and Hom precede this work. zeroOf is defined with
its witness before witness independence and tensor compatibility. Raw union
and its Positive and Derives closure precede quotient union. merge is defined
before its naturality and associativity; the exact original and source union
conventions are connected by union_source. Occurrence relations use the
existing tagged positions and are interpreted only after quotient descent.

The planned Gentzen, MixTerm, Atomic and Settled types are introduced as
unimplemented interfaces before their proposed theorem signatures. Empty
contexts have explicit top/bottom folds; singleton comparisons have unit maps,
so no hidden strict endpoint identification is implied. Positive refers to
arrow constructors, with signed literals unrestricted. These definitions are
adequately introduced; no missing-definition finding is claimed.

## Prioritized exact wording

Retain: “A zero between A and B requires an existing arrow f : A → B.”
For tensors use: “If both factors are witnessed zeros, their tensor is the
witnessed zero associated with the tensor of the witnesses.” For union use:
“Union is the derived diagonal–tensor–mix–codiagonal composite.” Follow the
interpretation statement with: “This computes the relation and does not
reflect relation equality to arrow equality.” For continuation use: “Define
the typed positive Gentzen rules and prove the existential Gentzenization
statement G1 before claiming cut elimination or positive coherence.”
The source comment was clarified accordingly before final verification.
No manuscript revision or relocated editorial commentary is needed.

## Scope

The complete new modules and the corresponding report/map additions were
reviewed. The cited source pages and verified writing cache were available.
No whole-paper reading/layout review, fresh manuscript compilation, novelty
survey, independent kernel replay or service verification was performed.
The manuscript checksum check passed; build and axiom audit evidence is
reported separately. All review/process commentary remains outside manuscript
v4 and its LaTeX comments. Historical access records are preserved.
