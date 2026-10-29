module

public import DosenPetric.GentzenBlockedLeftDisjCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem diagonal_shared (C R : NormalForm P) :
    comp (diag (.disj C R))
      (comp (mix (.disj C R) (.disj C R)) (BlockedMix.sharedOutput C C R)) =
      tensor .disj (comp (diag C) (mix C C)) (id R) := by
  have he : comp (diag C) (mix C C) = union (inl C C) (inr C C) := by
    rw [MixCalculation.mix_union,union_pre]
    simp only [← Laws.assoc,Laws.diag_fst,Laws.diag_snd,Laws.id_comp]
  change comp (diag (.disj C R)) (comp (mix (.disj C R) (.disj C R))
    (copair (tensor .disj (inl C C) (id R)) (tensor .disj (inr C C) (id R)))) = _
  rw [copair,← union_source,← MixCalculation.disj_union_left,← he]

theorem cross_selected (F X A : NormalForm P) :
    comp (terminalCross F X A) (snd (.conj F A) X) =
      comp (fst (.conj F X) A) (snd F X) := by
  rw [terminalCross,ProductCalculation.pair_snd]

theorem input_selected (F H Q X : NormalForm P) :
    comp (input F H Q X)
      (comp (fst (.conj (.conj F X) (.conj H X)) Q)
        (tensor .conj (snd F X) (snd H X))) =
      comp (snd (.conj (.conj F H) Q) X) (diag X) := by
  apply Reduced.conj_ext
  all_goals simp only [input,terminalCross,BlockedMix.sharedInput,
    ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,
    Laws.assoc,Laws.diag_fst,Laws.diag_snd,Laws.comp_id]

theorem parent_selected_cut (C F H A B R : NormalForm P) :
    comp (comp (kernel (.conj (.conj F H) (.disj A B)) C R)
      (tensor .disj (parent C F H A B) (id R)))
      (tensor .disj (tensor .disj (fst C (.conj F A)) (fst C (.conj H B))) (id R)) =
      comp (snd (.conj (.conj F H) (.disj A B)) (.disj C R))
        (tensor .disj (comp (diag C) (mix C C)) (id R)) := by
  rw [Laws.assoc,Laws.tensor_comp,parent_selected,Laws.id_comp]
  have ht : tensor .disj
      (comp (fst C (.conj (.conj F H) (.disj A B))) (comp (diag C) (mix C C))) (id R) =
      comp (tensor .disj (fst C (.conj (.conj F H) (.disj A B))) (id R))
        (tensor .disj (comp (diag C) (mix C C)) (id R)) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  rw [ht,← Laws.assoc,kernel_selected]

theorem reconstruction_selected (C F H A B R : NormalForm P) :
    comp (reconstruction C F H A B R)
      (tensor .disj (tensor .disj (fst C (.conj F A)) (fst C (.conj H B))) (id R)) =
      comp (snd (.conj (.conj F H) (.disj A B)) (.disj C R))
        (tensor .disj (comp (diag C) (mix C C)) (id R)) := by
  unfold reconstruction
  simp only [Laws.assoc]
  rw [sharedOutput_natural]
  rw [← Laws.assoc (tensor .disj
      (comp (terminalCross F (.disj C R) A) (kernel (.conj F A) C R))
      (comp (terminalCross H (.disj C R) B) (kernel (.conj H B) C R))),Laws.tensor_comp]
  simp only [Laws.assoc]
  rw [kernel_selected,kernel_selected,cross_selected,cross_selected]
  have ht : tensor .disj
      (comp (fst (.conj F (.disj C R)) A) (snd F (.disj C R)))
      (comp (fst (.conj H (.disj C R)) B) (snd H (.disj C R))) =
      comp (tensor .disj (fst (.conj F (.disj C R)) A) (fst (.conj H (.disj C R)) B))
        (tensor .disj (snd F (.disj C R)) (snd H (.disj C R))) := by rw [Laws.tensor_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj (.conj F (.disj C R)) (.conj H (.disj C R)) A B)),
    sourceConj_fst]
  simp only [Laws.assoc]
  rw [← Laws.assoc (mix (.conj F (.disj C R)) (.conj H (.disj C R))),Laws.mix_nat]
  have he := input_selected F H (.disj A B) (.disj C R)
  have he' := congrArg (fun v => comp v
    (comp (mix (.disj C R) (.disj C R)) (BlockedMix.sharedOutput C C R))) he
  simpa only [Laws.assoc,diagonal_shared] using he'

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
