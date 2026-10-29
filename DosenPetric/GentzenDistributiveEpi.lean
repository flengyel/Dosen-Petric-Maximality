module

public import DosenPetric.GentzenBlockedGammaDisj

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DistributiveEpi

/-- Discard both fixed factors of the source mixed comparison. -/
theorem source_snd (X Y A B : NormalForm P) :
    comp (ofTerm (Rules.sourceConj X Y A B))
      (tensor .disj (snd X A) (snd Y B)) = snd (.conj X Y) (.disj A B) := by
  simp only [Rules.sourceConj,ofTerm_comp,ofTerm_tensor,ofTerm_id,
    term_dist,term_assocL,term_swap,Laws.assoc]
  rw [tensor_separate .disj (snd X A) (snd Y B)]
  rw [← Laws.assoc (dist X A (.conj Y B)),← Laws.dist_snd]
  rw [← Laws.assoc (tensor .conj (id X) (swap .disj (.conj Y B) A)),
    ← Laws.snd_nat,Laws.assoc]
  rw [Laws.swap_nat]
  rw [← Laws.assoc (tensor .conj (id X) (dist Y B A)),← Laws.snd_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (dist Y B A),← Laws.dist_snd]
  simp only [ProductCalculation.assocL_pair,ProductCalculation.pair_snd_comp]
  rw [← Laws.assoc (tensor .conj (id (.conj X Y)) (swap .disj A B)),
    ← Laws.snd_nat,Laws.assoc,Laws.swap_swap,Laws.comp_id]

def sectionMap (X A B : NormalForm P) :
    Hom (.conj X (.disj A B)) (.disj (.conj X A) (.conj X B)) :=
  comp (tensor .conj (diag X) (id (.disj A B))) (ofTerm (Rules.sourceConj X X A B))

def comparison (X A B : NormalForm P) :
    Hom (.disj (.conj X A) (.conj X B)) (.conj X (.disj A B)) :=
  copair (tensor .conj (id X) (inl A B)) (tensor .conj (id X) (inr A B))

theorem comparison_fst (X A B : NormalForm P) :
    comp (comparison X A B) (fst X (.disj A B)) = copair (fst X A) (fst X B) := by
  rw [comparison,BlockedMix.copair_post]
  simp only [← Laws.fst_nat,Laws.comp_id]

theorem comparison_snd (X A B : NormalForm P) :
    comp (comparison X A B) (snd X (.disj A B)) = tensor .disj (snd X A) (snd X B) := by
  rw [comparison,BlockedMix.copair_post]
  simp only [← Laws.snd_nat]
  rw [← BlockedMix.tensor_copair]
  have he : copair (inl A B) (inr A B) = id (.disj A B) := by
    have h := (disjDiagonal P).pair_eta (id (.disj A B))
    change copair (comp (inl A B) (id (.disj A B)))
      (comp (inr A B) (id (.disj A B))) = id (.disj A B) at h
    simpa only [Laws.comp_id] using h
  rw [he,Laws.comp_id]

/-- The canonical comparison onto a product with a coproduct has an explicit section. -/
theorem section_comparison (X A B : NormalForm P) :
    comp (sectionMap X A B) (comparison X A B) = id (.conj X (.disj A B)) := by
  apply Reduced.conj_ext
  · rw [Laws.assoc,comparison_fst]
    change comp (comp (tensor .conj (diag X) (id (.disj A B)))
      (ofTerm (Rules.sourceConj X X A B)))
      (comp (tensor .disj (fst X A) (fst X B)) (codiag X)) = _
    simp only [Laws.assoc]
    rw [← Laws.assoc (ofTerm (Rules.sourceConj X X A B)),sourceConj_fst]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (diag X) (id (.disj A B))),← Laws.fst_nat]
    simp only [Laws.assoc]
    rw [Laws.diag_mix_codiag,Laws.comp_id,Laws.id_comp]
  · rw [Laws.assoc,comparison_snd]
    unfold sectionMap
    rw [Laws.assoc,source_snd,← Laws.snd_nat,Laws.id_comp,Laws.comp_id]

theorem ext {X A B Z : NormalForm P} (f g : Hom (.conj X (.disj A B)) Z)
    (ha : comp (tensor .conj (id X) (inl A B)) f = comp (tensor .conj (id X) (inl A B)) g)
    (hb : comp (tensor .conj (id X) (inr A B)) f = comp (tensor .conj (id X) (inr A B)) g) : f = g := by
  apply cancel_left f g (comparison X A B) (sectionMap X A B) (section_comparison X A B)
  rw [comparison,BlockedMix.copair_post,BlockedMix.copair_post,ha,hb]

end DistributiveEpi
end DosenPetric.Reduced.Gentzen
