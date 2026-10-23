# Positive zero and union: hostile-referee review

## (A) Kill-shots / hard blockers

This author-side, AI-assisted audit examines the three new modules, their
source correspondence and report. It is not independent peer review.
No confirmed blocker remains for the requested zero/union algebra.

Anchor: PositiveFragment.lean `PositiveCoherence`, CommonAtomicFactorization.lean
`faithful_of_positive_coherence`, and the report's dependency table G0–C.
Claim: positive coherence and Reduced.Faithful remain open. Failure mode:
**unproved** if either were promoted to an unconditional result. Evidence:
**absence_in_text** and **derivation**—there is no Gentzen syntax/cut-elimination
construction yet, and the existing transfer takes an explicit coherence premise.
Severity: fatal for a coherence/maximality claim; no such claim is made.
Repair: construct G0/G1, then the later dependencies. No counterexample to
PositiveCoherence is alleged.

## (B) Major weaknesses

| Anchor / claim | Typed check and evidence | Finding / impact |
| --- | --- | --- |
| ReducedZeroAlgebra `zeroOf`, `tensor_zeroOf` | f : A → C, g : B → D are arguments; their tensor is the witness at A ξ B → C ξ D. Witness independence and absorption follow from (0I). **derivation** | No missing witness or empty-hom-set inhabitant found. A removed witness would make a stronger claim unsupported. |
| `tensor_zero`, both cases | Product projections and coproduct injections give equality from the already derived universal laws; (0I) commutes each projection/injection with zero. **derivation** | Both-zero law proved syntactically. No equality is reflected from inclusion or occurrence relations. |
| ReducedUnion `Term.union`, `Derives.union`, quotient `union` | Derived raw path A → A∧A → B∧B → B∨B → B; Derives congruence precedes liftOn₂. **structural_argument** | No enlarged grammar or quotient by an interpretation kernel. All 21/61/19 schemas unchanged. |
| `merge_assoc`, `pair_assoc`, `union_assoc` | Source (b m), mix naturality, both diagonal associativities and tensor/category laws; typed associator is included. **derivation** | Associativity does not assume the desired algebra, lattice coherence or positive coherence. |
| `union_id_zero`, source rendered p.291 | Zero precedes inr/inl in execution order, (d k∨) replaces the next two maps, then projection/injection naturality and (w k). **citation**, **derivation** | Union unit is a theorem in the existing quotient; it was not imported as the ZIML axiom. |
| ReducedUnionOccurrences `relation_union`, `occurrence_zeroOf` | Raw tagged relation expansion and quotient induction/composition preservation. **derivation** | Interpretation compatibility is separate from syntactic equality; arbitrary and Empty occurrence types are retained. |

No further major defect was confirmed in the scoped endpoint. The full
transitive axiom audit covers these declarations and only the permitted axioms.
That audit is compiler-based local evidence, not independent kernel replay.

## (C) Minor issues

A source comment describing the union path in words made the intermediate
connectives hard to parse. It now gives the exact typed path
`A → A ∧ A → B ∧ B → B ∨ B → B`; the final strict run follows that edit.
The report distinguishes the two source syntaxes: union is derived in ML/ZIDL,
although primitive with algebraic equations in the alternative GML system.
The new merge helper is a composite, not a new structural generator.

## (D) Cross-section consistency failures

No remaining scope mismatch was found in the new report/maps. The algebra
holds for every existing Reduced arrow; positive raw closure is proved
separately. Objects can contain negative literals and both constants. No
Nonempty P, DecidableEq P, enumeration or fresh variable enters the proofs.

A concrete check prevents a false one-zero rule: take P = Unit and
L = lit (pos ()). In either tensor of zero L with id L, the edge
(Sum.inr (), Sum.inr ()) survives. The zero endomorphism of L ξ L has no
edges. Thus the one-zero annihilation equation would contradict the existing
interpretation. This is a **counterexample** to that stronger equation;
minimality is not claimed. The code proves only the two-zero law.

The two-object one-arrow test exposes the witness boundary: union is an
operation on an already chosen hom-set, and zeroOf is called with an arrow.
Nothing chooses a bottom element in an empty hom-set. No semilattice instance
or unrestricted realization/fullness claim was installed. Repeated labels do
not identify tagged positions. Existing common factorization/support are
reused unchanged, and the original presentation/manuscript are unchanged.

## (E) Acceptance conditions, non-negotiable

1. Both tensor zero laws, witnessed versions and witness independence must
   compile from existing equations: met by ReducedZeroAlgebra.
2. Union must be a typed derived composite with positive closure and Derives
   preservation before quotient use: met by Term.union/Positive.union/Derives.union.
3. All requested algebraic laws must compile without coherence: met by
   union_comm/assoc/idem/pre/post/id_zero/zeroOf and zeroOf_union.
4. The distributive union-unit law must be derived, not added as an equation:
   met by the direct p.291 proof and byte-identical ReducedEquations.
5. The relation union/empty-zero formulas must be independently proved:
   met by ReducedUnionOccurrences; no equality reflection used.
6. Zero witnesses, repeated tags, signs, constants and empty types must remain:
   met by the exact theorem signatures and tagged relation expansion.
7. Gentzen/coherence dependencies must be typed and open rather than axioms:
   met by the documentation-only G0–C table and unchanged PositiveCoherence.
8. Actual verification evidence and historical preservation must be retained:
   met by the evidence inventory, 49 files/2875 declarations and five rejections.

Failure of 1–6 or 8 would withdraw the corresponding checkpoint claim. Failure
of 7 would withdraw any promoted coherence/maximality claim.

## (F) Not checked / uncertainty log

No independent source-transcription review, independent kernel replay,
Challenge/Solution comparison, Comparator, official preflight/service check,
novelty survey, manuscript recompilation or whole-paper layout audit ran.
The source dependency inspection is not a complete verification of every
case of the published cut-elimination proof. The proposed Gentzen interfaces
are documentation, not compiled constructions.

Strongest confirmed blocker: G0/G1 and the subsequent positive-coherence
proof for the later faithfulness target. Strongest suspected unconfirmed
blocker for this checkpoint: none identified. Most important unchecked item:
independent source/kernel audit. Recommendation does not depend on unavailable
review material. Final recommendation: **unknown** as independent certification;
the scoped algebra passes this author-side audit, with coherence open.
