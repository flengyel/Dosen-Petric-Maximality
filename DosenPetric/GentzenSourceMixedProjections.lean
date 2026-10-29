module

public import DosenPetric.GentzenSplitPairs
public import DosenPetric.GentzenBlockedLeftDisjCore
public import DosenPetric.GentzenDisjSymmetry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Retain the first fixed factor and the second terminal formula. -/
theorem source_left_fixed (X Y A B : NormalForm P) :
    comp (ofTerm (Rules.sourceConj X Y A B))
      (tensor .disj (fst X A) (snd Y B)) =
      comp (tensor .conj (fst X Y) (id (.disj A B)))
        (comp (dist X A B) (tensor .disj (fst X A) (id B))) := by
  have ht : tensor .disj (fst X A) (snd Y B) =
      comp (tensor .disj (id (.conj X A)) (snd Y B)) (tensor .disj (fst X A) (id B)) := by
    rw [Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  have hd : comp (dist X A (.conj Y B))
      (tensor .disj (id (.conj X A)) (snd Y B)) =
      comp (tensor .conj (id X) (tensor .disj (id A) (snd Y B))) (dist X A B) := by
    simpa only [Laws.tensor_id] using Laws.dist_nat (id X) (id A) (snd Y B)
  have hp : comp (assocL .conj X Y (.disj B A))
      (tensor .conj (id X) (snd Y (.disj B A))) =
      tensor .conj (fst X Y) (id (.disj B A)) := by
    simp only [ProductCalculation.assocL_pair,ProductCalculation.tensor_pair,
      ProductCalculation.pair_pre,
      ProductCalculation.pair_snd_comp,ProductCalculation.pair_fst,ProductCalculation.pair_snd,Laws.comp_id]
  rw [ht]
  simp only [Rules.sourceConj,ofTerm_comp,ofTerm_tensor,ofTerm_id,
    term_dist,term_assocL,term_swap,Laws.assoc]
  rw [← Laws.assoc (dist X A (.conj Y B)),hd]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id X) (swap .disj (.conj Y B) A)),
    Laws.tensor_comp,Laws.id_comp,Laws.swap_nat,tensor_factor]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id X) (dist Y B A)),
    Laws.tensor_comp,Laws.id_comp,← Laws.dist_snd]
  rw [← Laws.assoc (assocL .conj X Y (.disj B A)),hp]
  rw [← Laws.assoc (tensor .conj (id (.conj X Y)) (swap .disj A B)),
    ← Laws.assoc (comp (tensor .conj (id (.conj X Y)) (swap .disj A B))
      (tensor .conj (fst X Y) (id (.disj B A)))),
    Laws.tensor_comp,Laws.id_comp,Laws.comp_id,Laws.tensor_comp,Laws.comp_id,Laws.swap_swap]

/-- Retain the first terminal formula and the second fixed factor. -/
theorem source_right_fixed (X Y A B : NormalForm P) :
    comp (ofTerm (Rules.sourceConj X Y A B))
      (tensor .disj (snd X A) (fst Y B)) =
      comp (tensor .conj (snd X Y) (swap .disj A B))
        (comp (dist Y B A)
          (comp (tensor .disj (fst Y B) (id A)) (swap .disj Y A))) := by
  rw [DisjLogical.sourceConj_swap]
  simp only [Laws.assoc]
  rw [Laws.swap_nat .disj (fst Y B) (snd X A)]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj Y X B A)),source_left_fixed]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (swap .conj X Y) (swap .disj A B)),Laws.tensor_comp,
    ← Laws.snd_swap,Laws.comp_id]

end DosenPetric.Reduced.Gentzen
