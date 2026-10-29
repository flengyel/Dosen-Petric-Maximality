module

public import DosenPetric.GentzenDoubleDisjOutput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.DoubleDisjSplice
universe u
variable {P : Type u}

def parallelInput (Q F H X : NormalForm P) :
    Hom (.conj (.conj Q (.conj F H)) X) (.conj Q (.conj (.conj F X) (.conj H X))) :=
  comp (assocL .conj Q (.conj F H) X)
    (tensor .conj (id Q) (BlockedMix.sharedInput (snd F H) (fst F H)))

theorem input_square (Q F H X : NormalForm P) :
    comp (tensor .conj (id (.conj Q (.conj F H))) (diag X))
      (comp (assocR .conj (.conj Q (.conj F H)) X X)
        (comp (tensor .conj (firstInput Q F H X) (id X))
          (secondInput Q (.conj F X) H X))) = parallelInput Q F H X := by
  simp only [parallelInput,firstInput,secondInput,BinaryLogical.exchangeCore,BlockedMix.sharedInput,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,
    Laws.assoc,Laws.diag_fst,Laws.diag_snd,Laws.comp_id]

/-- The contracted disjunction parent equals the two original child splices. -/
theorem equation {A B C F H D E X R : NormalForm P}
    (f : Hom (.conj A (.conj C F)) D) (g : Hom (.conj B (.conj C H)) E)
    (h : Hom X (.disj C R)) :
    splice h (comp (tensor .conj (diag C) (id (.conj (.disj A B) (.conj F H))))
      (comp (assocL .conj C C (.conj (.disj A B) (.conj F H))) (body f g))) =
      comp (parallelInput (.disj A B) F H X)
        (comp (DisjLogical.disjPair (child h f) (child h g)) (BlockedMix.sharedOutput D E R)) := by
  rw [ContractionSplice.binary,second]
  simp only [Laws.assoc]
  rw [output_square]
  have he := congrArg (fun v => comp v
    (comp (DisjLogical.disjPair (child h f) (child h g)) (BlockedMix.sharedOutput D E R)))
    (input_square (.disj A B) F H X)
  simpa only [Laws.assoc] using he

end DosenPetric.Reduced.Gentzen.DoubleDisjSplice
