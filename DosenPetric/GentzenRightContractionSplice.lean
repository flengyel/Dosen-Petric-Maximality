module

public import DosenPetric.GentzenReflectedSpliceNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSplice

theorem source_codiagonal (R C : NormalForm P) :
    comp (DistributiveEpi.sectionMap R C C) (codiag (.conj R C)) =
      tensor .conj (id R) (codiag C) := by
  have he : comp (DistributiveEpi.comparison R C C) (tensor .conj (id R) (codiag C)) =
      codiag (.conj R C) := by
    rw [DistributiveEpi.comparison,BlockedMix.copair_post]
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.inl_codiag,Laws.inr_codiag,Laws.tensor_id]
    have ht : copair (id (.conj R C)) (id (.conj R C)) = codiag (.conj R C) := by
      rw [copair,Laws.tensor_id,Laws.id_comp]
    exact ht
  rw [← he,← Laws.assoc,DistributiveEpi.section_comparison,Laws.id_comp]

theorem duplicate_input {R C Z : NormalForm P} (h : Hom (.conj R C) Z) :
    comp (tensor .conj (diag R) (id (.disj C C)))
      (comp (ofTerm (Rules.sourceConj R R C C))
        (comp (tensor .disj h h) (codiag Z))) =
      comp (tensor .conj (id R) (codiag C)) h := by
  rw [Laws.codiag_nat]
  rw [← Laws.assoc (tensor .conj (diag R) (id (.disj C C)))]
  change comp (DistributiveEpi.sectionMap R C C) (comp (codiag (.conj R C)) h) = _
  rw [← Laws.assoc,source_codiagonal]

theorem right_binary {R C V Y Z : NormalForm P} (h : Hom (.conj R C) Z)
    (g : Hom V (.disj (.disj Y C) C)) :
    PrincipalDisjunction.reflectedSplice h
      (comp g (comp (assocL .disj Y C C) (tensor .disj (id Y) (codiag C)))) =
      comp (tensor .conj (diag R) (id V))
        (comp (assocL .conj R R V)
          (comp (PrincipalDisjunction.reflectedSplice h
            (comp (PrincipalDisjunction.reflectedSplice h g) (assocR .disj Z Y C)))
            (comp (assocR .disj Z Z Y) (tensor .disj (codiag Z) (id Y))))) := by
  rw [← Laws.assoc g,PrincipalDisjunction.reflected_selected,← duplicate_input h]
  rw [PrincipalDisjunction.reflected_context,← Laws.assoc (ofTerm (Rules.sourceConj R R C C)),
    PrincipalDisjunction.reflected_output,
    PrincipalDisjunction.reflected_equation]
  simp only [Laws.assoc]

end ContractionSplice
end DosenPetric.Reduced.Gentzen
