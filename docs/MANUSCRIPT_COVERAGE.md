# Coverage and next proof obligations

The current development contains preliminary source for zero identities,
tagged substitution, and relation calculations. Its exact build status is in
`docs/VALIDATION.md` and the commit-specific CI logs. None of milestones I–III
below is complete.

| Milestone | Required endpoint | Current status |
| --- | --- | --- |
| I | Contextual collapse, relation calculations, and an explicit structural/faithful-interpretation interface admitting the intended nonthin model | Relation and zero-identity preliminaries written; complete interface and collapse proof open |
| II | Maximality conditional on explicit coherence, normalization, presentation, and substitution inputs | Open |
| III | Maximality for the actual Došen–Petrić presentation with all input bridges proved | Open |

## Next session

1. Run the strict build and axiom audit in the WSL2 checkout. Fix compilation
   failures without changing the intended statements.
2. Define products, coproducts, terminal/initial arrows, distributor, and a
   congruence with the compatibility needed by §5. State all endpoints and laws.
   Extend the interpretation to the existing relation operations. Avoid
   asserting the fold equations as opaque hypotheses: derive them from the
   existing relation lemmas and faithfulness.
3. Prove `j_A ∘ h_A ≡ j_A ∘ π₂` from K_A and the second-block calculation.
   Use the swap to obtain `j_A ∘ π₁ ≡ j_A ∘ π₂`, and precompose with
   `⟨1_A,0_A⟩`. Do not cancel j_A.
4. Prove terminality of A ∨ ⊤ in the quotient and the reversed injection
   equation for ⊤ ∨ A. Evaluate h at ⊤ and apply the first-injection law to
   obtain equal projections and then thinness.
5. Only after that endpoint, implement signed-literal isolation and
   substitution transport, retaining the actual free-presentation obligation.

## Verification boundaries

The source screening script is not a Lean parser. The Lean axiom audit checks
transitive axioms for all imported project definitions/theorems. It is not an
independent kernel replay or a semantic correspondence proof. The current
source has no Challenge/Solution pair and no Comparator acceptance claim.
No complete nonthin categorical model has yet been formalized.

The published normalization/coherence inputs have not been proved in Lean.
There is no custom axiom declaration for them and no theorem of maximality
whose conclusion is hidden in a structural field.
