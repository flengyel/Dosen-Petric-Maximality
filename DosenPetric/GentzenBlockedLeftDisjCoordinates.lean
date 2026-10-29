module

public import DosenPetric.GentzenSourceMixedProjections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem selected_coordinates (C F H Q : NormalForm P) :
    comp (assocR .conj C (.conj F H) Q)
      (comp (tensor .conj
        (pair (tensor .conj (id C) (fst F H)) (tensor .conj (id C) (snd F H))) (id Q))
        (comp (fst (.conj (.conj C F) (.conj C H)) Q)
          (tensor .conj (fst C F) (fst C H)))) =
      comp (fst C (.conj (.conj F H) Q)) (diag C) := by
  apply Reduced.conj_ext
  all_goals simp only [ProductCalculation.assocR_pair,ProductCalculation.tensor_pair,
    ProductCalculation.pair_pre,ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,
    Laws.assoc,Laws.diag_fst,Laws.diag_snd,Laws.comp_id]

theorem parent_selected (C F H A B : NormalForm P) :
    comp (parent C F H A B) (tensor .disj (fst C (.conj F A)) (fst C (.conj H B))) =
      comp (fst C (.conj (.conj F H) (.disj A B))) (comp (diag C) (mix C C)) := by
  have hf (V Q : NormalForm P) :
      comp (assocL .conj C V Q) (fst C (.conj V Q)) =
        comp (fst (.conj C V) Q) (fst C V) := by
    rw [ProductCalculation.assocL_pair,ProductCalculation.pair_fst]
  have ht : tensor .disj
      (comp (fst (.conj C F) A) (fst C F))
      (comp (fst (.conj C H) B) (fst C H)) =
      comp (tensor .disj (fst (.conj C F) A) (fst (.conj C H) B))
        (tensor .disj (fst C F) (fst C H)) := by rw [Laws.tensor_comp]
  unfold parent
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,hf,hf,ht]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj (.conj C F) (.conj C H) A B)),sourceConj_fst]
  simp only [Laws.assoc]
  rw [Laws.mix_nat]
  simp only [← Laws.assoc]
  simpa only [← Laws.assoc] using congrArg (fun v => comp v (mix C C))
    (selected_coordinates C F H (.disj A B))

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
