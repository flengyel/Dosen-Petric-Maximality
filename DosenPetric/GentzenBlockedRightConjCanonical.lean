module

public import DosenPetric.GentzenDoubleConjParent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

def parent {A B C D E X Y : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E))) :
    Hom (.conj X Y) (.disj C (.disj (.conj A B) (.disj D E))) :=
  comp (tensor .conj f g)
    (comp (ofTerm (Term.mixedDisj A (.disj C D) B (.disj C E)))
      (DoubleConjSplice.mergeOutput C (.conj A B) D E))

theorem canonical_equation {A B C D E R X Y Z : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E)))
    (h : Hom (.conj C R) Z) :
    splice (parent f g) h =
      comp (BlockedMix.rightSharedInput R X Y)
        (comp (tensor .conj (DoubleConjSplice.child f h) (DoubleConjSplice.child g h))
          (comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj Z E)))
            (DoubleConjSplice.mergeOutput Z (.conj A B) D E))) := by
  have he := DoubleConjSplice.equation f g h
  rw [DoubleConjSplice.body_merged] at he
  exact he

end DosenPetric.Reduced.Gentzen.BlockedRightConj
