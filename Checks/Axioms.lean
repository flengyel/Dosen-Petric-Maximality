module

import DosenPetric
import Lean

open Lean Elab Command

set_option autoImplicit false

run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (`DosenPetric).isPrefixOf (privateToUserName name) then
      -- Imported theorems can appear as axiomInfo in the module interface.
      -- collectAxioms uses the compiler's exported dependency data to distinguish
      -- those signatures from actual axioms; inspect every declaration kind.
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Quot.sound, `Classical.choice].contains a do
          throwError "Unpermitted axiom {a} in {name}"
      count := count + 1
  if count == 0 then
    throwError "No project declarations were audited"
  logInfo m!"PASS: transitive axiom checks for {count} project declarations"

#print axioms DosenPetric.ZeroIdentity.zeroOf_independent
#print axioms DosenPetric.ZeroIdentity.precompose
#print axioms DosenPetric.Formula.contract_expand
#print axioms DosenPetric.Formula.expand_contract
#print axioms DosenPetric.Relations.hRel_eq_fold
#print axioms DosenPetric.Relations.hRel_swap
#print axioms DosenPetric.Relations.second_block
#print axioms DosenPetric.Relations.first_injection
#print axioms DosenPetric.Relations.projections_distinct

#print axioms DosenPetric.OccurrenceInterpretation.fold_independent
#print axioms DosenPetric.OccurrenceInterpretation.fold_swap
#print axioms DosenPetric.OccurrenceInterpretation.first_injection
#print axioms DosenPetric.OccurrenceInterpretation.second_block
#print axioms DosenPetric.ContextualCollapse.total
#print axioms DosenPetric.GeneratedModel.interpretation
#print axioms DosenPetric.GeneratedModel.nonthin
#print axioms DosenPetric.GeneratedModel.empty_hom
#print axioms DosenPetric.Isolation.normalized_literal_context
#print axioms DosenPetric.ContextualCollapse.context_retract
#print axioms DosenPetric.ContextualCollapse.all_contexts
#print axioms DosenPetric.relative_maximality
