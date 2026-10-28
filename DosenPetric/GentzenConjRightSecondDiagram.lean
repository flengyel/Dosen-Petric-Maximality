module

public import DosenPetric.GentzenBinaryLogicalDiagram

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjR_right_second_core {A D B E C Z X Y W : NormalForm P}
    (f : Hom X (.disj A D)) (g : Hom (.conj C Y) (.disj B E)) (h : Hom W (.disj C Z)) :
    comp (splice h (comp ((sideM P .conj).cross C X Y)
      (comp (tensor .conj f g) (ofTerm (Term.mixedDisj A D B E)))))
      (comp (assocL .disj (.conj A B) (.disj D E) Z)
        (tensor .disj (id (.conj A B)) (assocL .disj D E Z))) =
      comp (assocL .conj X Y W)
        (comp (tensor .conj f (comp (splice h g) (assocL .disj B E Z)))
          (ofTerm (Term.mixedDisj A D B (.disj E Z)))) := by
  have hs : splice h (comp ((sideM P .conj).cross C X Y)
      (comp (tensor .conj f g) (ofTerm (Term.mixedDisj A D B E)))) =
      comp (splice h (comp ((sideM P .conj).cross C X Y) (tensor .conj f g)))
        (tensor .disj (ofTerm (Term.mixedDisj A D B E)) (id Z)) := by
    simpa only [Laws.assoc] using Splice.output h
      (comp ((sideM P .conj).cross C X Y) (tensor .conj f g))
      (ofTerm (Term.mixedDisj A D B E))
  rw [hs,product_right_splice,tensor_factor .conj f (splice h g) (assocL .disj B E Z)]
  have he := congrArg (fun k => comp (assocL .conj X Y W)
    (comp (tensor .conj f (splice h g)) k)) (mixed_residual A D B E Z)
  simpa only [Laws.assoc] using he

end BinaryLogical
end DosenPetric.Reduced.Gentzen
