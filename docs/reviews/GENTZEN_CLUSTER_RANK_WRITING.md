# Mathematical-writing review: Gentzen clusters and rank

The report now separates positional routing, the finite cluster and its
correctness proofs, and rank. It states the arbitrary-P scope before the
implementation and names every equality notion. The key terminology repair
is proofSize for the proof-node termination count. This is an AI-assisted
author-side review of the new construction and records, not independent
certification or a whole-manuscript judgment.

## Governing source and reviewed material

The directly consulted Knuth–Larrabee–Roberts *Mathematical Writing* cache is
`.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf`, SHA-256
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
This is the verified MIT-hosted typeset course report, not a claimed byte copy
of the Stanford scan or MAA edition. Section 1, printed pp.1–6/PDF pp.3–8,
and §§4–5, printed pp.9–13/PDF pp.11–15, were extracted and read directly.
Source access succeeded. Historical failed-access/provisional records remain
unchanged. This review is source-grounded rather than provisional.

The reviewed scope includes the full new report, actual theorem statements
and code organization in the sixteen modules, new correspondence table,
and current coverage/statement/validation/continuation changes. Manuscript
v4 is unchanged; its prose and rendered layout were not reviewed afresh.

## Actual outline and functions

The report's existing sections, in order, are:

1. Proved endpoint: central tracing, reachability, rank and cut-rank claims.
2. Baseline/interfaces: preserved inputs and scope.
3. Source correspondence: source definitions and implemented objects.
4. Positions/routing: definitions, constructor coverage and local correctness.
5. Finite tree: address/position identity, termination and global correctness.
6. Rank equations: all-node count and exact hypotheses; separate measures.
7. Focused boundaries: repeated tags, constants, signs, binary/cut cases.
8. Verification: actual results, evidence and limits.
9. Next obligation: the typed W1 instance and larger remaining dependencies.

The central contribution is a reusable, correct finite ancestry API for the
existing proof syntax, including cuts. Its predecessors are positional At
infrastructure and actual G rules; its users are the later reducibility and
blocked-contraction transformations. The current order supports that path;
no revised outline is warranted.

## Comparison with the governing text

| Anchor | Issue / clarification | Verified source principle or independent rationale | Applied action |
| --- | --- | --- | --- |
| Report opening and cut-rank signatures | Application hypotheses could be mistaken for rank-definition requirements. | §1 point 5, printed p.2, self-contained statements. | Quantify arbitrary P/proof/position; explicitly state that Topmost, Atomized and CutFree are absent from rank definitions. |
| Positions/routing and finite-tree sections | A sequence of code names would obscure what is being constructed. | §1 points 10–13, printed pp.2–3, connected explanations and reader motivation. | Explain upper-to-lower parent versus inverse predecessor enumeration before listing theorems; explain root/edge/reachability roles. |
| Rank section and proofSize declaration | “Height” could mean maximum depth although the helper sums all proof nodes. | §1 point 14, printed p.3, consistent meanings; independent mathematical terminology rationale. | Rename the helper to G.proofSize and strict-premise lemma to proofSize_lt, retain the first run, reverify final sources. |
| TraceNode / address discussion | Proof value, proof occurrence and selected position can be conflated. | §1 points 11 and 14, printed pp.2–3; independent typing rationale. | Define all three and state exactly what cluster_address proves. Avoid using address alone as node identity. |
| Source table / constructor coverage | Source order could be read as definitional list equality. | Independent endpoint/position rationale, supported by §1 point 5. | Display actual Γ++Θ versus Θ++Γ and Δ++Λ versus Λ++Δ orders; distinguish binary first/second proof arguments from context block order. |
| Rank reindexing and continuation | A structural equality could drift into denotation invariance or a decreasing elimination measure. | Independent logical scope rationale; not a purported book rule. | State equality transport/address-prefix results precisely, and keep transformation decreases and quotient descent unclaimed. |
| Definitions in reading order | Front-loading every implementation helper would delay the result. | §§4–5 printed pp.9–13, contextual placement of definitions. | Give side/position/rank conventions at their first substantive use and keep full inventories in evidence. |

The source principles are paraphrased. The mathematical typing and proof
boundary requirements are distinguished from the writing text's advice.

## Definition-order and notation audit

P, G, Place and selected C appear with the main endpoint. SequentSide/At and
the two map directions are explained before parent/fiber proofs. Premise and
branch tags precede proof addresses. TraceNode's validity is distinguished
from merely constructing a record. Leaf, Parametric and LowerContraction have
actual source-based definitions before the rank-one and sum statements.
rho, proofSize, cutCount and the later measure have distinct meanings.
Left/right cut rank versus sequent side is stated explicitly. No missing
definition was confirmed in the reviewed scope.

Future Blocked predicates, proof replacement and W1–W6 transformations are
labelled unimplemented. The new Tied predicates are identified as proved
site characterizations, not blocked transformations. Whole-formula ancestry
does not stand for the relation on literal occurrences. Both constant bases
are explained as genuine positions despite empty literal-occurrence types.

## Applied wording and scope

The consequential repairs are: “proofSize counts all proof-tree nodes”; “rank
counts all nodes, not just leaves or the longest branch”; “rank definitions
require neither Topmost nor Atomized nor CutFree”; and “arbitrary TraceNode
records are not presumed valid; cluster_address proves validity for members.”
These preserve mathematical content and avoid unsupported generalizations.
No hypothesis, equation, syntax or theorem was weakened for prose repair.

The final build, axiom audit, all five controls, manuscript hashes and
whitespace checks passed after the naming repair. No manuscript compilation,
layout inspection, independent review, novelty review or publication occurred.
No review/revision-process material was inserted into manuscript prose or
LaTeX comments. Historical access and review reports remain intact.
