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
#print axioms DosenPetric.Presentation.category
#print axioms DosenPetric.Presentation.operations
#print axioms DosenPetric.DiagonalData.diag_projections
#print axioms DosenPetric.Presentation.zeroConstruction_eq
#print axioms DosenPetric.Presentation.zeroIdentity
#print axioms DosenPetric.Presentation.Equation.subst
#print axioms DosenPetric.Presentation.Derives.subst
#print axioms DosenPetric.Presentation.substitution
#print axioms DosenPetric.Presentation.doubleNegation
#print axioms DosenPetric.Presentation.Equation.relation
#print axioms DosenPetric.Presentation.Derives.relation
#print axioms DosenPetric.Presentation.occurrenceMap
#print axioms DosenPetric.Presentation.occurrence_pair
#print axioms DosenPetric.Presentation.occurrence_zero
#print axioms DosenPetric.Presentation.nonthin
#print axioms DosenPetric.Presentation.empty_hom
#print axioms DosenPetric.Presentation.zeroConstruction_structural
#print axioms DosenPetric.Literal.flip_flip
#print axioms DosenPetric.Formula.signedLabel_letter
#print axioms DosenPetric.NormalForm.signedLabel_eq_literalAt
#print axioms DosenPetric.Presentation.NormalComparison.inverse_comp
#print axioms DosenPetric.Presentation.NormalComparison.trans
#print axioms DosenPetric.Presentation.NormalComparison.conj
#print axioms DosenPetric.Presentation.NormalComparison.deMorganConj
#print axioms DosenPetric.Presentation.NegationNormalization.comparison
#print axioms DosenPetric.Presentation.normalization
#print axioms DosenPetric.Presentation.NegationNormalization.forward_backward
#print axioms DosenPetric.Presentation.NegationNormalization.backward_forward
#print axioms DosenPetric.Presentation.NegationNormalization.forward_graph
#print axioms DosenPetric.Presentation.NegationNormalization.backward_graph
#print axioms DosenPetric.Presentation.NegationNormalization.literal_toOcc
#print axioms DosenPetric.Presentation.NegationNormalization.polarity_toOcc
#print axioms DosenPetric.Presentation.NegationNormalization.repeated_negative_tags
#print axioms DosenPetric.Presentation.NegationNormalization.transport_apply
#print axioms DosenPetric.Presentation.NegationNormalization.transport_recover
#print axioms DosenPetric.Presentation.NegationNormalization.transport_injective
#print axioms DosenPetric.Presentation.Term.relation_signedLabel
#print axioms DosenPetric.Presentation.occurrence_signedLabel
#print axioms DosenPetric.Presentation.occurrence_label
#print axioms DosenPetric.Presentation.occurrence_polarity
#print axioms DosenPetric.Presentation.no_edge_of_polarity_ne
#print axioms DosenPetric.Presentation.no_edge_opposite_literals
#print axioms DosenPetric.Presentation.no_edge_negative_positive_literals
#print axioms DosenPetric.Presentation.occurrence_literal
#print axioms DosenPetric.Presentation.occurrence_literal_letter
#print axioms DosenPetric.Presentation.occurrence_literal_polarity
#print axioms DosenPetric.Presentation.no_edge_of_literal_ne
#print axioms DosenPetric.Presentation.diag_copies
#print axioms DosenPetric.Presentation.codiag_merges
#print axioms DosenPetric.Presentation.NegationNormalization.transport_literal
#print axioms DosenPetric.Presentation.NegationNormalization.transport_literal_coordinates
#print axioms DosenPetric.Reduced.Equation.toFull
#print axioms DosenPetric.Reduced.Derives.toFull
#print axioms DosenPetric.Reduced.category
#print axioms DosenPetric.Reduced.inclusion
#print axioms DosenPetric.Reduced.inclusion_comp
#print axioms DosenPetric.Reduced.inclusion_tensor_conj
#print axioms DosenPetric.NormalForm.dual_dual
#print axioms DosenPetric.Presentation.NegationNormalization.form_true
#print axioms DosenPetric.Presentation.NegationNormalization.normal_formula
#print axioms DosenPetric.Presentation.NegationNormalization.normal_neg_formula
#print axioms DosenPetric.Presentation.fromTop_unique
#print axioms DosenPetric.Reduced.Term.mixedDisj
#print axioms DosenPetric.Reduced.Term.mixedConj
#print axioms DosenPetric.Reduced.Term.etaNF
#print axioms DosenPetric.Reduced.Term.epsilonNF
#print axioms DosenPetric.Presentation.NegationNormalization.forward_formula
#print axioms DosenPetric.Presentation.NegationNormalization.backward_formula
#print axioms DosenPetric.Presentation.NegationNormalization.transport_formula
#print axioms DosenPetric.Reduced.Compatibility.etaNF
#print axioms DosenPetric.Reduced.Compatibility.epsilonNF
#print axioms DosenPetric.Reduced.red
#print axioms DosenPetric.Reduced.red_sound
#print axioms DosenPetric.Reduced.representation
#print axioms DosenPetric.Reduced.Term.relation_toFull
#print axioms DosenPetric.Reduced.Derives.relation
#print axioms DosenPetric.Reduced.occurrence_inclusion
#print axioms DosenPetric.Reduced.Coordinates.red_apply
#print axioms DosenPetric.Reduced.Coordinates.red_coordinates
#print axioms DosenPetric.Reduced.normal_faithful_of_reduced
#print axioms DosenPetric.Reduced.global_faithful_of_reduced
#print axioms DosenPetric.Reduced.conjDiagonal
#print axioms DosenPetric.Reduced.disjDiagonal
#print axioms DosenPetric.Reduced.zero_top
#print axioms DosenPetric.Reduced.zero_bot
#print axioms DosenPetric.Reduced.fromTop_unique
#print axioms DosenPetric.Reduced.toBot_unique
#print axioms DosenPetric.Reduced.rightIn_tensor
#print axioms DosenPetric.Reduced.rightOut_tensor
#print axioms DosenPetric.Reduced.shuffle_unit_out
#print axioms DosenPetric.Reduced.shuffle_unit_in
#print axioms DosenPetric.Reduced.dist_top
#print axioms DosenPetric.Reduced.dist_bot
#print axioms DosenPetric.Reduced.distRight_top
#print axioms DosenPetric.Reduced.conj_shuffle_dist_bot
#print axioms DosenPetric.Reduced.Context.map_derives
#print axioms DosenPetric.Reduced.Context.mapTerm_id
#print axioms DosenPetric.Reduced.Context.mapTerm_comp
#print axioms DosenPetric.Reduced.Context.map_id
#print axioms DosenPetric.Reduced.Context.map_comp
#print axioms DosenPetric.Reduced.Context.gConj_nat
#print axioms DosenPetric.Reduced.Context.gDisj_nat
#print axioms DosenPetric.Reduced.Context.gConj_top
#print axioms DosenPetric.Reduced.Context.gDisj_bot
#print axioms DosenPetric.Reduced.Context.gEta
#print axioms DosenPetric.Reduced.Context.gEpsilon
#print axioms DosenPetric.Reduced.Context.gEta_comp
#print axioms DosenPetric.Reduced.Context.gEpsilon_comp
#print axioms DosenPetric.Reduced.Context.decode_encode
#print axioms DosenPetric.Reduced.Context.encode_decode
#print axioms DosenPetric.Reduced.Context.embeddings_disjoint
#print axioms DosenPetric.Reduced.Context.relation_mapTerm
#print axioms DosenPetric.Reduced.Context.occurrence_map
#print axioms DosenPetric.Reduced.Context.top_occ_fixed
#print axioms DosenPetric.Reduced.Context.bot_occ_fixed
#print axioms DosenPetric.Reduced.Context.gEta_comp_relation
#print axioms DosenPetric.Reduced.Context.gEpsilon_comp_relation
