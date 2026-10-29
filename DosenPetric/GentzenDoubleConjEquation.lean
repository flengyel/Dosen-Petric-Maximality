module

public import DosenPetric.GentzenDoubleConjOutput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.DoubleConjSplice
universe u
variable {P : Type u}

theorem input_square (R X Y : NormalForm P) :
    comp (tensor .conj (diag R) (id (.conj X Y)))
      (comp (assocL .conj R R (.conj X Y))
        (comp (tensor .conj (id R) (assocR .conj R X Y))
          ((sideM P .conj).cross R (.conj R X) Y))) = BlockedMix.rightSharedInput R X Y := by
  simp only [BlockedMix.rightSharedInput,MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.diag_fst,Laws.diag_snd,
    Laws.comp_id,Laws.assoc]

theorem selected_merge (A B D E Z : NormalForm P) :
    comp (BinaryLogical.selectedMixedSecond A (.disj Z D) B Z E)
      (comp (tensor .disj (id Z) (firstOutput Z (.conj A B) D E))
        (comp (assocR .disj Z Z (.disj (.conj A B) (.disj D E)))
          (tensor .disj (codiag Z) (id (.disj (.conj A B) (.disj D E)))))) =
      comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj Z E))) (mergeOutput Z (.conj A B) D E) := by
  have he := congrArg (fun k => comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj Z E))) k)
    (output_square Z (.conj A B) D E)
  simpa only [BinaryLogical.selectedMixedSecond,firstOutput,secondOutput,Laws.assoc] using he

theorem equation {A B C D E R X Y Z : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E)))
    (h : Hom (.conj C R) Z) :
    splice (comp (body f g)
      (comp (assocR .disj C C (.disj (.conj A B) (.disj D E)))
        (tensor .disj (codiag C) (id (.disj (.conj A B) (.disj D E)))))) h =
      comp (BlockedMix.rightSharedInput R X Y)
        (comp (tensor .conj (child f h) (child g h))
          (comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj Z E)))
            (mergeOutput Z (.conj A B) D E))) := by
  rw [ContractionSplice.head_right_binary,second]
  simp only [Laws.assoc]
  erw [selected_merge]
  have hi := congrArg (fun k => comp k
    (comp (tensor .conj (child f h) (child g h))
      (comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj Z E))) (mergeOutput Z (.conj A B) D E))))
    (input_square R X Y)
  simpa only [Laws.assoc] using hi

end DosenPetric.Reduced.Gentzen.DoubleConjSplice
