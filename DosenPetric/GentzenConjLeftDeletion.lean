module

public import DosenPetric.GentzenConjLeftCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem distRight_inner (C R E : NormalForm P) :
    distRight C R E =
      comp (tensor .conj (swap .disj C R) (id E))
        (comp (innerDisj R C E) (swap .disj (.conj R E) C)) := by
  rw [innerDisj_distRight R C E]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (swap .disj C R) (id E)),Laws.tensor_comp,
    Laws.swap_swap,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  rw [Laws.swap_swap,Laws.comp_id]

/-- Expose one parametric output of the actual mixed conjunction comparison. -/
def selectedMixed (A C D B E : NormalForm P) :
    Hom (.conj (.disj A (.disj C D)) (.disj B E))
      (.disj C (.disj (.conj A B) (.disj D E))) :=
  comp (ofTerm (Term.mixedDisj A (.disj C D) B E))
    (comp (tensor .disj (id (.conj A B)) (assocL .disj C D E))
      ((sideM P .disj).cross C (.conj A B) (.disj D E)))

theorem selectedMixed_eq (A C D B E : NormalForm P) :
    selectedMixed A C D B E =
      comp (tensor .conj ((sideM P .disj).cross C A D) (id (.disj B E)))
        (comp (distRight C (.disj A D) (.disj B E))
          (tensor .disj (id C) (ofTerm (Term.mixedDisj A D B E)))) := by
  symm
  rw [distRight_inner]
  simp only [Laws.assoc]
  erw [Laws.swap_nat]
  rw [← Laws.assoc (innerDisj (.disj A D) C (.disj B E)),mixed_first_residual]
  simp only [Laws.assoc]
  have hi : comp (tensor .conj ((sideM P .disj).cross C A D) (id (.disj B E)))
      (comp (tensor .conj (swap .disj C (.disj A D)) (id (.disj B E)))
        (tensor .conj (assocL .disj A D C) (id (.disj B E)))) =
      tensor .conj (tensor .disj (id A) (swap .disj C D)) (id (.disj B E)) := by
    rw [Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,deletion_input]
  have hm := mixedDisj_nat (id A) (swap .disj C D) (id B) (id E)
  rw [Laws.tensor_id,Laws.tensor_id] at hm
  have he := congrArg (fun k => comp k
    (comp (ofTerm (Term.mixedDisj A (.disj D C) B E))
      (comp (residualOutput (.conj A B) D C E) (swap .disj (.disj (.conj A B) (.disj D E)) C)))) hi
  simp only [Laws.assoc] at he
  rw [he]
  rw [← Laws.assoc (tensor .conj (tensor .disj (id A) (swap .disj C D)) (id (.disj B E))),← hm]
  simp only [Laws.assoc]
  rw [deletion_output]
  rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
