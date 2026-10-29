module

public import DosenPetric.GentzenMirrorSelectedDeletion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjR_left_first_core {A B C D E X Y T Z : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B E)) (h : Hom (.conj C T) Z) :
    splice (comp (tensor .conj f g) (selectedMixed A C D B E)) h =
      comp (assocR .conj T X Y)
        (comp (tensor .conj
          (comp (splice (comp f (coCross C A D)) h)
            (coCross A Z D)) g)
          (selectedMixed A Z D B E)) := by
  have hl : comp (tensor .conj f g) (selectedMixed A C D B E) =
      comp (comp (tensor .conj (comp f (coCross C A D)) g)
        (distRight C (.disj A D) (.disj B E)))
          (tensor .disj (id C) (mixedDisj A D B E)) := by
    rw [selectedMixed_eq]
    simp only [Laws.assoc]
    erw [← Laws.assoc (tensor .conj f g),Laws.tensor_comp,Laws.comp_id]
  rw [hl,Splice.residual,splice_distRight,selectedMixed_eq A Z D B E]
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj
    (comp (splice (comp f (coCross C A D)) h) (coCross A Z D)) g),
    Laws.tensor_comp,Laws.comp_id]
  rw [Laws.assoc,disj_cross_inverse,Laws.comp_id]

end BinaryLogical
end DosenPetric.Reduced.Gentzen.MirrorCalculus
