# v6 Lean claim scope

The abstract and §6 accurately state a conditional Lean maximality theorem. Neither claims a completed formal proof of maximality for the equation-generated Došen–Petrić category.

Reviewed source: `Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex`, abstract and §6 (“Lean formalization”), together with the formalization reference. Code baseline: `1e967bcb913a74ae590dde940f246acaddce1fba`. The following manuscript-only commit, `0af6a0e83fdcbb5ec3d98103cbb36b8f2b30dec6`, has identical Lean sources; the comparison changes only the v5 TeX, PDF and checksums.

| Manuscript anchor | Source evidence | Finding |
|---|---|---|
| Abstract: “relative to explicit coherence and structural inputs” | `DosenPetric/Substitution.lean`, `relative_maximality` | Accurate conditional scope. The declaration takes the structural, occurrence, normalization, signed-label, substitution, double-negation and congruence-closure inputs explicitly. |
| §6 paragraph 1: indexed arrow syntax and `Derives` quotient | `PresentationSyntax.Term`; `PresentationCategory.termSetoid`, `Hom`, `category` | Accurate. The syntax is indexed by source and target formulas; the quotient uses generated equational derivability. |
| §6 paragraph 1: substitution, normalization and tagged occurrence interpretation | `Presentation.substitution`, `Presentation.normalization`, `Presentation.occurrenceMap` | Accurate construction claims. No faithfulness claim is made here. |
| §6 paragraph 2: explicit arguments of `relative_maximality` | `Substitution.lean`, lines 103–109; `Structure.OccurrenceInterpretation.faithful` | Matches the declaration. Faithfulness is an input field, not a proved fact for the source quotient. |
| §6 symmetric map and collapse argument | `Structure.fold`; `OccurrenceInterpretation.fold_swap`; `ContextualCollapse.total` | Accurate mathematical description of the existing symmetric-fold proof. The code need not use a declaration named `mix`: its displayed distributor composite is the codiagonal of mix. |
| §6 final paragraph: source faithfulness and actual-presentation instantiation remain incomplete | `Reduced.Faithful`; `normal_faithful_of_reduced`; `global_faithful_of_reduced`; `faithful_of_positive_coherence`; current statement map | Accurate and necessary qualification. The source does not supply `PositiveCoherence`, and the full source category has not been connected to every input of `relative_maximality`. |

The manuscript’s q/e isomorphism proof and the formalization’s symmetric-fold proof are different proofs of the same contextual-collapse implication. Section 6 identifies the formal route explicitly, so the revision does not imply that q/e has already been formalized.

No scope correction is required. In particular, the manuscript does not claim complete Gentzen Reducibility, cut elimination, Boolean Coherence, an unconditional actual-presentation maximality endpoint, independent-kernel replay, or Palomar registration. This was a declaration-and-source comparison, not a new Lean build or independent kernel replay.
