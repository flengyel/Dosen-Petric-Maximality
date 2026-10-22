module

import DosenPetric
import Lean

open Lean Elab Command

set_option autoImplicit false

run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants do
    if (`DosenPetric).isPrefixOf name then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        let axioms ← collectAxioms name
        for a in axioms do
          unless #[`propext, `Quot.sound, `Classical.choice].contains a do
            throwError "Unpermitted axiom {a} in {name}"
        count := count + 1
      | .axiomInfo _ => throwError "Project-owned axiom: {name}"
      | _ => pure ()
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
