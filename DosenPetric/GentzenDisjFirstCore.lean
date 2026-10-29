module

public import DosenPetric.GentzenDisjNativeCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

/-- The actual disjunction-left comparison before the context folds. -/
def disjPair {A B X Y U V : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B Y) V) :
    Hom (.conj (.disj A B) (.conj X Y)) (.disj U V) :=
  comp (swap .conj (.disj A B) (.conj X Y))
    (comp (ofTerm (Rules.sourceConj X Y A B))
      (tensor .disj (comp (swap .conj X A) f) (comp (swap .conj Y B) g)))

theorem reflected_first_child {A X C D T J : NormalForm P}
    (f : Hom (.conj A X) (.disj C D)) (h : Hom (.conj C T) J) :
    comp (assocL .conj T X A)
      (PrincipalDisjunction.reflectedSplice (comp (swap .conj T C) h)
        (comp (swap .conj X A) (comp f (swap .disj C D)))) =
      comp (swap .conj (.conj T X) A)
        (comp ((sideM P .conj).cross A T X) (splice f h)) := by
  have hi : comp (comp (swap .conj X A) (comp f (swap .disj C D))) (swap .disj D C) =
      comp (swap .conj X A) f := by
    simp only [Laws.assoc]
    rw [Laws.swap_swap,Laws.comp_id]
  have hh : comp (swap .conj C T) (comp (swap .conj T C) h) = h := by
    rw [← Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [PrincipalDisjunction.reflectedSplice,hi,hh,Splice.input]
  rw [← Laws.assoc,first_child_route,Laws.assoc]

theorem reflected_first_parent {A B X Y C D E T J : NormalForm P}
    (f : Hom (.conj A X) (.disj C D)) (g : Hom (.conj B Y) E) (h : Hom (.conj C T) J) :
    PrincipalDisjunction.reflectedSplice (comp (swap .conj T C) h)
      (comp (ofTerm (Rules.sourceConj X Y A B))
        (comp (tensor .disj
          (comp (swap .conj X A) (comp f (swap .disj C D))) (comp (swap .conj Y B) g))
          (BinaryLogical.exchangeCore .disj D C E))) =
      comp (tensor .conj (id T) (swap .conj (.conj X Y) (.disj A B)))
        (splice (comp (disjPair f g) (assocL .disj C D E)) h) := by
  have ht : tensor .disj
      (comp (swap .conj X A) (comp f (swap .disj C D))) (comp (swap .conj Y B) g) =
      comp (tensor .disj (comp (swap .conj X A) f) (comp (swap .conj Y B) g))
        (tensor .disj (swap .disj C D) (id E)) := by
    rw [Laws.tensor_comp,Laws.comp_id,Laws.assoc]
  have hi : comp (comp (ofTerm (Rules.sourceConj X Y A B))
      (comp (tensor .disj
        (comp (swap .conj X A) (comp f (swap .disj C D))) (comp (swap .conj Y B) g))
        (BinaryLogical.exchangeCore .disj D C E))) (swap .disj (.disj D E) C) =
      comp (swap .conj (.conj X Y) (.disj A B))
        (comp (disjPair f g) (assocL .disj C D E)) := by
    rw [ht]
    simp only [disjPair,Laws.assoc]
    rw [first_sum_route]
    rw [← Laws.assoc (swap .conj (.conj X Y) (.disj A B)),Laws.swap_swap,Laws.id_comp]
  have hh : comp (swap .conj C T) (comp (swap .conj T C) h) = h := by
    rw [← Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [PrincipalDisjunction.reflectedSplice,hi,hh,Splice.input]

def firstReflectedInverse (T X Y Q : NormalForm P) :
    Hom (.conj T (.conj Q (.conj X Y))) (.conj (.conj (.conj T X) Y) Q) :=
  comp (tensor .conj (id T) (swap .conj Q (.conj X Y)))
    (comp (assocR .conj T (.conj X Y) Q) (tensor .conj (assocR .conj T X Y) (id Q)))

theorem first_input_inverse (T X Y Q : NormalForm P) :
    comp (firstReflectedInverse T X Y Q) (firstReflectedInput T X Y Q) =
      id (.conj T (.conj Q (.conj X Y))) := by
  simp only [firstReflectedInverse,firstReflectedInput,Laws.assoc]
  rw [← Laws.assoc (tensor .conj (assocR .conj T X Y) (id Q)),Laws.tensor_comp,
    Laws.assocR_L,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  rw [← Laws.assoc (assocR .conj T (.conj X Y) Q),Laws.assocR_L,Laws.id_comp,
    Laws.tensor_comp,Laws.id_comp,Laws.swap_swap,Laws.tensor_id]

theorem disjL_left_first_core {A B X Y C D E T J : NormalForm P}
    (f : Hom (.conj A X) (.disj C D)) (g : Hom (.conj B Y) E) (h : Hom (.conj C T) J) :
    splice (comp (disjPair f g) (assocL .disj C D E)) h =
      comp (firstDisjInput T X Y (.disj A B))
        (comp (disjPair (comp ((sideM P .conj).cross A T X) (splice f h)) g)
          (assocL .disj J D E)) := by
  have he := reflected_core (comp (swap .conj Y B) g)
    (comp (swap .conj X A) (comp f (swap .disj C D))) (comp (swap .conj T C) h)
  rw [reflected_first_parent,reflected_first_child] at he
  have hr : comp (ofTerm (Rules.sourceConj (.conj T X) Y A B))
      (comp (tensor .disj
        (comp (swap .conj (.conj T X) A) (comp ((sideM P .conj).cross A T X) (splice f h)))
        (comp (swap .conj Y B) g)) (assocL .disj J D E)) =
      comp (swap .conj (.conj (.conj T X) Y) (.disj A B))
        (comp (disjPair (comp ((sideM P .conj).cross A T X) (splice f h)) g)
          (assocL .disj J D E)) := by
    simp only [disjPair,Laws.assoc]
    rw [← Laws.assoc (swap .conj (.conj (.conj T X) Y) (.disj A B)),Laws.swap_swap,Laws.id_comp]
  rw [hr] at he
  apply cancel_left _ _ (firstReflectedInput T X Y (.disj A B))
    (firstReflectedInverse T X Y (.disj A B)) (first_input_inverse T X Y (.disj A B))
  rw [← Laws.assoc (firstReflectedInput T X Y (.disj A B)),first_input_route]
  simpa only [firstReflectedInput,Laws.assoc] using he

end DisjLogical
end DosenPetric.Reduced.Gentzen
