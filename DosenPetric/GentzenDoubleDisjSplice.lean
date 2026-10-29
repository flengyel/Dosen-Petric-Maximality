module

public import DosenPetric.GentzenDoubleDisjSpliceCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.DoubleDisjSplice
universe u
variable {P : Type u}

def child {A C F D X R : NormalForm P}
    (h : Hom X (.disj C R)) (f : Hom (.conj A (.conj C F)) D) :
    Hom (.conj A (.conj F X)) (.disj D R) :=
  comp (assocR .conj A F X) (splice h (comp ((sideM P .conj).cross C A F) f))

def body {A B C F H D E : NormalForm P}
    (f : Hom (.conj A (.conj C F)) D) (g : Hom (.conj B (.conj C H)) E) :
    Hom (.conj C (.conj C (.conj (.disj A B) (.conj F H)))) (.disj D E) :=
  comp (twoHead C F H (.disj A B)) (DisjLogical.disjPair f g)

theorem first {A B C F H D E X R : NormalForm P}
    (f : Hom (.conj A (.conj C F)) D) (g : Hom (.conj B (.conj C H)) E)
    (h : Hom X (.disj C R)) :
    splice h (body f g) =
      comp (tensor .conj (DisjLogical.secondDisjInput C F H (.disj A B)) (id X))
        (comp (firstInput (.disj A B) F (.conj C H) X)
          (comp (DisjLogical.disjPair (child h f) g) (BinaryLogical.exchangeCore .disj D R E))) := by
  rw [body,twoHead,Laws.assoc,Splice.context,DisjLogical.disjL_right_first_core]
  simp only [firstInput,child,Laws.assoc]

theorem second {A B C F H D E X R : NormalForm P}
    (f : Hom (.conj A (.conj C F)) D) (g : Hom (.conj B (.conj C H)) E)
    (h : Hom X (.disj C R)) :
    splice h (comp (assocR .conj C (.conj (.disj A B) (.conj F H)) X) (splice h (body f g))) =
      comp (tensor .conj (firstInput (.disj A B) F H X) (id X))
        (comp (secondInput (.disj A B) (.conj F X) H X)
          (comp (DisjLogical.disjPair (child h f) (child h g))
            (comp (assocR .disj (.disj D R) E R)
              (tensor .disj (BinaryLogical.exchangeCore .disj D R E) (id R))))) := by
  rw [first]
  rw [← Laws.assoc (assocR .conj C (.conj (.disj A B) (.conj F H)) X),
    ← Laws.assoc (comp (assocR .conj C (.conj (.disj A B) (.conj F H)) X)
      (tensor .conj (DisjLogical.secondDisjInput C F H (.disj A B)) (id X))),
    Laws.assoc (assocR .conj C (.conj (.disj A B) (.conj F H)) X),between_square]
  simp only [Laws.assoc]
  rw [Splice.context]
  rw [← Laws.assoc (DisjLogical.secondDisjInput C (.conj F X) H (.disj A B)),
    Splice.output,DisjLogical.disjL_right_second_core]
  simp only [secondInput,child,Laws.assoc]

end DosenPetric.Reduced.Gentzen.DoubleDisjSplice
