# Signed-literal reduction: hostile-referee review

## (A) Kill-shots / hard blockers

This is an author-side, AI-assisted self-audit of the new construction and
correspondence map, not independent peer review. No confirmed hard blocker
was found for the requested existential representation theorem.

Anchor: coverage map, Boolean Coherence row, and `ReducedOccurrences.lean`,
`Faithful`. The missing assertion is faithfulness of the reduced occurrence
assignment. Failure mode: **unproved**; evidence: **absence_in_text**, the code
defines the proposition and only proves transfer under an explicit hC premise.
Severity: fatal for claiming completed Boolean Coherence or actual maximality;
not a flaw in the narrower reduction endpoint. Repair: prove reduced coherence
using the remaining source argument and its earlier coherence dependencies.
No counterexample to coherence is alleged.

## (B) Major weaknesses

No major mathematical defect was confirmed in the scoped endpoint. The
following specific possible circularities and omissions were checked:

| Anchor | Claim and actual evidence | Status |
| --- | --- | --- |
| `ReducedSyntax.lean`, `Term` | 21 constructor schemas: positive families and zero, composition/tensors, atomic eta/epsilon only. No n/r/rho or compound eta/epsilon constructor. Evidence: structural_argument and exact signature inventory. | Restricted grammar matches p.318. |
| `ReducedEquations.lean`, `Equation/Derives`; `ReducedCategory.lean`, `termSetoid` | 61 inherited positive equation schemas, equivalence and operation congruence; quotient relation is Derives. Evidence: derivation and checked transcription comparison. | Neither relation equality nor equality after inclusion defines the quotient. |
| `Equation.toFull`, `Derives.toFull`, `inclusion` | Every reduced schema maps to the corresponding full schema, then derivations and quotient operations descend. Evidence: compiled proof. | Inclusion is well defined before any surjectivity/faithfulness argument. |
| `ReducedWitnesses.lean`, `mixedDisj/mixedConj`, `etaNF/epsilonNF` | Both mixed map types are explicitly indexed; witnesses recurse on signed normal forms, including negative literals and both constants. Evidence: structural_argument and compilation. | Same-connective medial was not substituted for a mixed map. |
| `Compatibility.etaNF/epsilonNF`, `Presentation.fromTop_unique` | Compatibility uses zero plus terminality/initiality, not empty interpreted relations. Evidence: derivation. | No circular invocation of faithfulness. |
| `SignedLiteralReduction.lean`, `red_sound` | All 31 full constructor schemas have branches. Structural squares use existing naturality; zero uses zero_law; comparisons use inverse equations; eta/epsilon use constructed witnesses and typed uniqueness. Evidence: derivation. | No missing primitive case or new equation. |
| `representation`, `normal_formula`, `forward_formula/backward_formula`, `transport_formula` | Quotient induction yields an existential reduced arrow, with explicit endpoint casts and identities on already normal objects. Evidence: compiled proof. | Proves surjectivity on normal-form hom-sets, not equality reflection. |

The next stronger statement, descent of the chosen red operation to quotient
arrows, is intentionally not claimed. It would require full equational
derivations to produce reduced derivations between red representatives.
Anchor: main report, remaining obligations. Failure mode if silently promoted:
**unsupported_generalization**; evidence: **structural_argument**, equality
after inclusion cannot be reflected without an additional theorem. Severity:
major for such a promoted claim; no defect in the present existential result.
Repair: prove that preservation separately, or retain the current scope.

## (C) Minor issues

The names `mixedDisj/mixedConj` identify explicitly typed chosen composites.
No general equality with a particular source e'-composite is asserted. The
resulting eta/epsilon arrows agree with the originals by the proved uniqueness
laws. This avoids treating a matching type as an equality proof.

Normal-form duality is an object operation; `negForward/negBackward` are
pointwise comparison arrows. Neither defines contravariant negation on
arbitrary arrows. Composition order remains first the first Lean argument.

## (D) Cross-section consistency failures

No remaining mismatch was found among the code, current map, and reduction
report. The previous signed-label and normalization reports remain historical.
The full presentation, manuscript v4, pinned toolchain, and dependency manifest
are unchanged. Both constants and negative literals are covered by recursion;
P can be empty and needs no decidable equality or enumeration.

The ambient reduced category has `NormalForm P` objects and syntactic quotient
arrows. Inclusion is covariant into Presentation on their formula embeddings;
it preserves identity, composition, and both tensors. No reverse arrow is
created in a two-object one-arrow test category: the representation theorem
starts with an existing full arrow, and every zero remains an endomorphism.

The reduced occurrence assignment is defined by tagged generator relations
and relational operations, then descends through already proved preservation.
Compatibility with inclusion is one-way interpretation preservation, not an
equality-reflection argument. The coordinate theorems retain every tagged
occurrence, including Empty and repeated equal labels, by reuse of the
normalizer's inverse coordinates.

The two transfer theorems take `hC : Reduced.Faithful P` explicitly. They do
not supply that proposition, a faithful-interface instance, or Boolean
Coherence. The source's subsequent argument still needs the g-eta/g-epsilon
factorizations and earlier Distributive Dicartesian and Zero-Identity
Distributive Dicartesian Coherence. Those dependencies remain open.

## (E) Acceptance conditions, non-negotiable

Failure of any condition would require withdrawing the corresponding scoped
claim until repaired.

1. A reduced quotient generated by the actual restricted grammar/equations.
   Met by 21 term and 61 equation schemas, Derives, and the compiled quotient.
2. Syntactic inclusion preserving generators, derivations, composition and
   tensors. Met by the explicit toFull and inclusion theorems.
3. Compound witnesses with correct mixed types and nonsemantic compatibility.
   Met by the indexed terms and zero-based uniqueness proofs.
4. A reduction covering every full constructor, with the exact transport
   equality and normal-form comparison identities. Met by compilation.
5. Existential hom-set surjectivity at exact normal-form endpoints. Met by
   representation; no unproved red quotient descent is claimed.
6. Occurrence and normalizer-coordinate compatibility, with faithfulness only
   conditional. Met by ReducedOccurrences and its explicit premise.
7. Required verification, source hashes, manuscript integrity and five
   expected negative rejections. Met by retained evidence and the main report.

## (F) Not checked / uncertainty log

The review inspected the seven new modules, exact endpoints, raw constructor
coverage, source pp.317–321 and normalization clauses, and the current maps.
The entire inherited positive-presentation transcription was not independently
re-audited against every earlier chapter; its prior source index was reused,
and this task checked the matching reduced schemas and their compiled
inclusion proofs. No proof of reduced faithfulness, general equality reflection,
or full red-equation preservation was found or claimed.

No independent kernel replay, Challenge/Solution comparison, Comparator,
official preflight/service verification, independent peer review, novelty
survey, new manuscript compilation, publication or visibility change ran.

Strongest confirmed blocker: reduced faithfulness is unproved, blocking an
unconditional coherence/maximality claim; none found for the representation
endpoint. Strongest suspected unconfirmed blocker: none substantiated for
that endpoint. Most important unchecked item: the source's remaining reduced
coherence proof and its positive-core dependencies. The narrow assessment
does not depend on unavailable material. Final recommendation: **unknown**
as a publication decision; the scoped reduction passes this author-side
audit. Reject a claim that Boolean Coherence or actual maximality is complete.
