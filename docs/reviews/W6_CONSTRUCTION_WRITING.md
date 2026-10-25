# Mathematical-writing review of the W6 instructions

The instruction gives the exact local constructions and the reason their
rank comparisons can discharge the full descendant bound. Its scope is
implementation guidance, not a report of new checked theorems. No manuscript
revision is proposed.

## Source and reviewed scope

Reviewed the complete `docs/CODEX_W6_CONSTRUCTION.md`, the new hostile audit,
and the linked-record changes. The repository anchor is
`a17ec1b0b44c9fe7f5061bb35c2edfd1ded9ef90`.
The complete v6 TeX was read to preserve the accepted mathematical and
editorial requirements; this was not a new whole-paper correctness or novelty
review. No manuscript source was edited or rendered.

Consulted Knuth–Larrabee–Roberts, *Mathematical Writing*, §1 (printed pp.1–6,
PDF pp.3–8) and §4 (printed pp.9–10, PDF pp.11–12). The official Stanford PDF
was unavailable in this session. The
[MIT-hosted course report](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf)
was downloaded and read; SHA-256
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`
matches the copy recorded in the preceding writing review. No identity with
another scan or edition is asserted.

## Actual outline

1. Task and evidence: source anchor, division of work and unchanged endpoint.
2. Existing interfaces and missing equalities: dependencies and exact route
   variances, followed by the singleton-aware helper.
3. Left W6 with both premises: input data, endpoints, blocked construction,
   categorical equality and the macro rank calculation.
4. One-premise left cases: explicit endpoints and blocked constructors.
5. Right W6: separately typed native construction, categorical variance,
   ranks and one-premise cases.
6. Addressed conclusion: every quantified context, proof, address and position.
7. Integration and checks: remaining dispatch, local verification and delivery.

The main construction depends on the extended/prefixed selection operations,
route components, mixed-map naturality and existing Reducibility boundary
theorems. No alternative outline is needed.

## Comparison and definition-order audit

| Location | Check | Source principle or independent rationale | Result |
|---|---|---|---|
| §§2–4 input data | P, formulas, contexts, selections, arities and fixed gaps precede the constructions. | KLR §1 points 5 and 11: self-contained conditions and introduced variables. | Retain. |
| §§2 and 4 equality paths | Product and coproduct arrows have explicit endpoints and opposite composition orders. | Independent mathematical typing requirement; KLR §1 point 14 supports consistent notation. | Retain the typed route definitions; define selection/block shorthand through their routes. |
| §§2–4 ranks | δ and the selected-rank sums are defined before use. Parametric and fresh ranks have separate explanations. | KLR §1 points 10–13: connected exposition, explanatory complements and readable prose around formulas. | Retain the separate left macro and right native calculations. |
| §5 theorem template | All I,J,v,b,y and containing-cut variables are declared; the complete descendant quantifier is displayed. | KLR §1 point 5 and independent preservation of the governing theorem's scope. | Retain without an extra caller-supplied rank or entry assumption. |
| §1 API names and §§2–4 proposed equations | Existing declarations are distinguished from requested helpers and uncompiled targets. | KLR §4, notes by TLL, distinguishes mathematical statements from program notation; proof-status reporting is an independent project requirement. | Retain. |
| Task/report prose | Instructions and checking narrative appear only in external records. | Author's explicit manuscript-boundary requirement, independent of KLR. | No manuscript insertion. |

No arity-zero selection is used. The left and right
rank sums use their own explicitly typed embeddings. Singleton operations
retain the original proof through context equality; they introduce no dummy
contraction. The prose explains why a root-rank tie is compatible with strict
descent for eligible proper descendants.

## Required follow-through and limitations

The next deliverable is the local Codex implementation and its evidence.
Replace target status with exact declaration links only after local checking.
If the implementation changes a construction or exposes a rank discrepancy,
update every affected instruction, table and review in the same pass.

Source consultation and the editorial review were performed; Lean elaboration,
compilation, independent kernels, manuscript rendering and submission checks
were not. This review does not certify the proposed Lean implementation or
the full-paper formalization.
