# Mathematical-writing review: Gentzen proof replacement

The report leads with the exact reconstruction operation and then shows how
an existing local W5 theorem is used inside a larger proof. It distinguishes
that completed integration gate from the still-open source classification and
rank argument. No substantive editorial defect remains within scope. This is
an AI-assisted author-side review, not independent certification or a judgment
on the complete manuscript.

## Governing source and scope

The directly consulted Knuth–Larrabee–Roberts Mathematical Writing cache is
.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf, SHA256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
Section 1, printed pp.1–6/PDF pp.3–8, and §4's contextual definition-placement
discussion, printed p.9/PDF p.11, govern this review. This is the MIT-hosted
typeset course report; no byte identity with the Stanford scan or MAA edition
is asserted. Source advice is paraphrased below. Formal typing, proof-status
boundaries and this reporting format are independent requirements.

Reviewed: four new modules and all public types/proofs/examples, report,
current correspondence, statements/coverage, validation, README and continuation.
Manuscript v4/v5, diagrams and Appendix A references are unchanged. No
whole-paper/fresh-rendering judgment is made.

## Actual outline and functions

1. Exact endpoint/hypotheses: introduce the existing root, chosen occurrence,
   replacement and local denotation equality before stating outer congruence.
2. Construction/proof: one-rule reconstruction, address recursion, recovery,
   inserted path, address composition, denotation and additive/predicate laws.
3. W5 integration: arbitrary-address applications and concrete two-level
   surrounding proof, followed by binary/identical-sibling/Empty examples.
4. Source correspondence/gate status: p.250 replacement prerequisite and
   pp.251–252 W5, with unproved classification/rank/global goals separated.
5. Implementation/verification: preserved baseline, actual checks and limits,
   author-side review/evidence and the next classification checkpoint.

The central question is whether a proved local rewrite can be applied to one
specified occurrence in a larger typed proof. The outline answers this in
construction order and demonstrates the resulting integration. No replacement
outline is needed.

## Comparison with the governing text

| Report anchor | Difficulty addressed | Verified advice or independent rationale | Applied action |
| --- | --- | --- | --- |
| Exact endpoint/hypotheses | Proof value could be confused with its occurrence. | §1 point 5, printed p.2, and points 11,14; independent typing. | Give root, g, address a and replacement h at exact sequents before the conclusion. |
| Construction/proof | A sequence of API names could hide the reconstruction argument. | §1 points 10–13 on connected explanation, motivation and readable prose. | Explain root/down recursion and unchanged siblings, then recovery and composition. |
| Congruence hypothesis | Local equality might be mistaken for assumed coherence or the global theorem. | §1 points 5,11; independent proof-dependency requirement. | State the exact local equality and identify the already proved W5 theorem that discharges it. |
| Additive balances | Counts could be conflated with ranks or an elimination measure. | §1 points 11,13–15; independent mathematical scope. | Display exact Nat balances; define proofSize as node count and explicitly leave rank control open. |
| W5 integration/examples | A generic operation alone would not demonstrate use of the old library. | §1 points 11–12; independent acceptance requirement. | Show the actual surrounding proof, [0,0] address, unchanged sibling and nested signed-cut/Empty instances. |
| Source/gate status | A prerequisite could be promoted to Reducibility. | §1 points 12–13; independent proof-status requirement. | Separate reconstruction from source classification, reduct existence and all affected tied-site ranks. |

These applications do not attribute Lean conventions or formal correctness
to KLR. Section 4 permits informal previews while keeping needed definitions
available when the argument depends on them.

## Definition-order and notation audit

P, Γ/Δ, Θ/Λ, root, g, a and h are introduced before replace. Premise.rebuild
is distinguished from repeated reconstruction along ProofAddress. The inserted
proof's new address is distinct from the old typed address even though their
branch lists agree. Address append order is outer then inner; composition is
left-first. No equality test on formula labels or proof values selects the hole.

Reduced equality and tagged relation equality are distinct, with relation
consequence stated afterward. Congruence compares proofs at the same local
sequent; it creates no arrow in an empty hom-set. The Nat balances precede
predicate consequences and do not use truncated subtraction. Atomized retains
all surrounding thinning and sibling conditions. The identity-to-zero example
asserts syntactic branch distinction, not an unproved denotation equation.

The concrete surround definition and its exact output type precede the W5
instances. Cut-free and cut-containing examples serve different claims.
Whole-formula positions, proof branch addresses and literal-occurrence tags
remain separate. Empty constants need no variable inhabitant. Short typed
recursion/equations suffice here; an additional commutative diagram would
not clarify this proof-tree reconstruction.

## Consequential wording and limits

Current records replace stale reconstruction-next statements with the completed
operation and its tested W5 integration. Earlier local scopes now distinguish
mechanical replacement from still-open all-site rank control. The next prompt
requires source-faithful definitions and exhaustive case dispatch rather than
automatically selecting another isolated transformation. This updates proof
status without changing the manuscript or hiding missing cases.

Reviewed proofs/types match checked inventories. Failed elaborations and
procedural records remain outside mathematical manuscript prose and source
comments. Fresh manuscript layout/compilation, independent certification,
novelty assessment and official service verification were not performed.
