module

public import DosenPetric.GentzenConjFirstResidual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjR_right_first_core {A D B E C R Y X W : NormalForm P}
    (f : Hom (.conj C Y) (.disj A D)) (g : Hom X (.disj B E)) (h : Hom W (.disj C R)) :
    splice h (comp (assocR .conj C Y X)
      (comp (tensor .conj f g) (ofTerm (Term.mixedDisj A D B E)))) =
      comp (exchangeCore .conj Y X W)
        (comp (tensor .conj (comp (splice h f) (assocL .disj A D R)) g)
          (comp (ofTerm (Term.mixedDisj A (.disj D R) B E))
            (residualOutput (.conj A B) D R E))) := by
  have hs : splice h (comp (assocR .conj C Y X)
      (comp (tensor .conj f g) (ofTerm (Term.mixedDisj A D B E)))) =
      comp (splice h (comp (assocR .conj C Y X) (tensor .conj f g)))
        (tensor .disj (ofTerm (Term.mixedDisj A D B E)) (id R)) := by
    simpa only [Laws.assoc] using Splice.output h
      (comp (assocR .conj C Y X) (tensor .conj f g)) (ofTerm (Term.mixedDisj A D B E))
  rw [hs,product_left_splice]
  simp only [Laws.assoc]
  rw [mixed_first_residual]
  rw [← Laws.assoc (tensor .conj (splice h f) g),Laws.tensor_comp,Laws.comp_id]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
