module

public import DosenPetric.GentzenConjSecondCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem disj_cross_middle_nat {Q R : NormalForm P} (k : Hom Q R) (C E : NormalForm P) :
    comp (tensor .disj k (id (.disj C E))) ((sideM P .disj).cross C R E) =
      comp ((sideM P .disj).cross C Q E) (tensor .disj (id C) (tensor .disj k (id E))) := by
  have he := (sideM P .disj).cross_nat (id C) k (id E)
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he ⊢
  simpa only [Laws.tensor_id] using he

theorem second_deletion_nat {Q R : NormalForm P} (k : Hom Q R) (C D E : NormalForm P) :
    comp (tensor .disj k (swap .disj (.disj C E) D))
      (comp (tensor .disj (id R) ((sideM P .disj).cross C D E))
        ((sideM P .disj).cross C R (.disj D E))) =
      comp (tensor .disj (id Q) (assocL .disj C E D))
        (comp ((sideM P .disj).cross C Q (.disj E D))
          (tensor .disj (id C) (tensor .disj k (swap .disj E D)))) := by
  have ht : tensor .disj k (swap .disj (.disj C E) D) =
      comp (tensor .disj (id Q) (swap .disj (.disj C E) D))
        (tensor .disj k (id (.disj D (.disj C E)))) := by
    rw [Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj k (id (.disj D (.disj C E)))),Laws.tensor_comp,
    Laws.comp_id,Laws.id_comp]
  have ht' : tensor .disj k ((sideM P .disj).cross C D E) =
      comp (tensor .disj (id Q) ((sideM P .disj).cross C D E))
        (tensor .disj k (id (.disj C (.disj D E)))) := by
    rw [Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  rw [ht',Laws.assoc,disj_cross_middle_nat]
  rw [← Laws.assoc (tensor .disj (id Q) ((sideM P .disj).cross C D E)),
    ← Laws.assoc (tensor .disj (id Q) (swap .disj (.disj C E) D)),second_deletion]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,Laws.comp_id]

/-- Expose a parametric output in the second child of the mixed conjunction. -/
def selectedMixedSecond (A D B C E : NormalForm P) :
    Hom (.conj (.disj A D) (.disj B (.disj C E)))
      (.disj C (.disj (.conj A B) (.disj D E))) :=
  comp (ofTerm (Term.mixedDisj A D B (.disj C E)))
    (comp (tensor .disj (id (.conj A B)) ((sideM P .disj).cross C D E))
      ((sideM P .disj).cross C (.conj A B) (.disj D E)))

theorem selectedMixedSecond_swap (A D B C E : NormalForm P) :
    selectedMixedSecond A D B C E =
      comp (swap .conj (.disj A D) (.disj B (.disj C E)))
        (comp (selectedMixed B C E A D)
          (tensor .disj (id C) (tensor .disj (swap .conj B A) (swap .disj E D)))) := by
  unfold selectedMixedSecond
  rw [mixedDisj_swap]
  simp only [Laws.assoc]
  rw [second_deletion_nat]
  simp only [selectedMixed,Laws.assoc]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
