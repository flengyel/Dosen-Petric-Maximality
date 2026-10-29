module

public import DosenPetric.GentzenDoubleConjCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.DoubleConjSplice
universe u
variable {P : Type u}

def child {A C D R X Z : NormalForm P} (f : Hom X (.disj A (.disj C D)))
    (h : Hom (.conj C R) Z) : Hom (.conj R X) (.disj A (.disj Z D)) :=
  comp (splice (comp f ((sideM P .disj).cross C A D)) h) ((sideM P .disj).cross A Z D)

def body {A B C D E X Y : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E))) :
    Hom (.conj X Y) (.disj C (.disj C (.disj (.conj A B) (.disj D E)))) :=
  comp (tensor .conj f g)
    (comp (BinaryLogical.selectedMixed A C D B (.disj C E))
      (tensor .disj (id C) (secondOutput C (.conj A B) D E)))

theorem selected_between (A B C D E Z : NormalForm P) :
    comp (BinaryLogical.selectedMixed A Z D B (.disj C E))
      (comp (tensor .disj (id Z) (secondOutput C (.conj A B) D E))
        ((sideM P .disj).cross C Z (.disj (.conj A B) (.disj D E)))) =
      comp (BinaryLogical.selectedMixedSecond A (.disj Z D) B C E)
        (tensor .disj (id C) (firstOutput Z (.conj A B) D E)) := by
  have he := congrArg (fun k => comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj C E))) k)
    (between_square C Z (.conj A B) D E)
  simpa only [BinaryLogical.selectedMixed,BinaryLogical.selectedMixedSecond,
    firstOutput,secondOutput,Laws.assoc] using he

theorem first {A B C D E R X Y Z : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E)))
    (h : Hom (.conj C R) Z) :
    splice (body f g) h =
      comp (assocR .conj R X Y)
        (comp (tensor .conj (child f h) g)
          (comp (BinaryLogical.selectedMixed A Z D B (.disj C E))
            (tensor .disj (id Z) (secondOutput C (.conj A B) D E)))) := by
  rw [body,← Laws.assoc (tensor .conj f g),Splice.residual,BinaryLogical.conjR_left_first_core]
  simp only [child,Laws.assoc]

theorem second {A B C D E R X Y Z : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E)))
    (h : Hom (.conj C R) Z) :
    splice (comp (splice (body f g) h)
      ((sideM P .disj).cross C Z (.disj (.conj A B) (.disj D E)))) h =
      comp (tensor .conj (id R) (assocR .conj R X Y))
        (comp ((sideM P .conj).cross R (.conj R X) Y)
          (comp (tensor .conj (child f h) (child g h))
            (comp (BinaryLogical.selectedMixedSecond A (.disj Z D) B Z E)
              (tensor .disj (id Z) (firstOutput Z (.conj A B) D E))))) := by
  rw [first]
  simp only [Laws.assoc]
  rw [selected_between]
  rw [Splice.input]
  rw [← Laws.assoc (tensor .conj (child f h) g),Splice.residual,
    BinaryLogical.conjR_left_second_core]
  simp only [child,Laws.assoc]

end DosenPetric.Reduced.Gentzen.DoubleConjSplice
