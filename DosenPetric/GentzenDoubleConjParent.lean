module

public import DosenPetric.GentzenDoubleConjEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.DoubleConjSplice
universe u
variable {P : Type u}

theorem cross_merge (C Y : NormalForm P) :
    comp ((sideM P .disj).cross C C Y)
      (comp (assocR .disj C C Y) (tensor .disj (codiag C) (id Y))) =
      comp (assocR .disj C C Y) (tensor .disj (codiag C) (id Y)) := by
  dsimp only [MonoidalData.cross,sideM,side,disjMonoidal,opposite,category]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocL .disj C C Y),Laws.assocL_R,Laws.id_comp,
    Laws.tensor_comp,Laws.codiag_swap,Laws.id_comp]

theorem parent_merge (C Q D E : NormalForm P) :
    comp (firstOutput C Q D (.disj C E))
      (comp (tensor .disj (id C) (secondOutput C Q D E))
        (comp (assocR .disj C C (.disj Q (.disj D E)))
          (tensor .disj (codiag C) (id (.disj Q (.disj D E)))))) = mergeOutput C Q D E := by
  have he := congrArg (fun k => comp k
    (comp (assocR .disj C C (.disj Q (.disj D E)))
      (tensor .disj (codiag C) (id (.disj Q (.disj D E)))))) (between_square C C Q D E)
  simp only [Laws.assoc] at he
  erw [cross_merge] at he
  exact he.trans (output_square C Q D E)

theorem body_merged {A B C D E X Y : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E))) :
    comp (body f g)
      (comp (assocR .disj C C (.disj (.conj A B) (.disj D E)))
        (tensor .disj (codiag C) (id (.disj (.conj A B) (.disj D E))))) =
      comp (tensor .conj f g)
        (comp (ofTerm (Term.mixedDisj A (.disj C D) B (.disj C E))) (mergeOutput C (.conj A B) D E)) := by
  have he := congrArg (fun k => comp (tensor .conj f g)
    (comp (ofTerm (Term.mixedDisj A (.disj C D) B (.disj C E))) k)) (parent_merge C (.conj A B) D E)
  simpa only [body,BinaryLogical.selectedMixed,firstOutput,Laws.assoc] using he

end DosenPetric.Reduced.Gentzen.DoubleConjSplice
