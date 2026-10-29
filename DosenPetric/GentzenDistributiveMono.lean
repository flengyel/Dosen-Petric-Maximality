module

public import DosenPetric.GentzenDistributiveEpi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DistributiveMono

theorem mixed_inl (A D B E : NormalForm P) :
    comp (tensor .conj (inl A D) (inl B E)) (ofTerm (Term.mixedDisj A D B E)) =
      inl (.conj A B) (.disj D E) := by
  rw [mixedDisj_eq,tensor_separate .conj (inl A D) (inl B E)]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (.disj A D)) (inl B E)),← Laws.dist_inl]
  rw [← Laws.assoc (inl (.conj (.disj A D) B) E),Laws.inl_nat]
  unfold innerDisj
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (inl A D) (id B)),← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id B) (inl A D)),← Laws.dist_inl]
  rw [← Laws.assoc (inl (.conj B A) D),Laws.inl_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .conj A B),Laws.swap_swap,Laws.id_comp]
  have he := (disjDiagonal P).assocR_fst (rightIn_assocL .disj) (.conj A B) D E
  change comp (inl (.disj (.conj A B) D) E) (assocL .disj (.conj A B) D E) =
    tensor .disj (id (.conj A B)) (inl D E) at he
  rw [he,Laws.inl_nat,Laws.id_comp]

def comparison (A B R : NormalForm P) :
    Hom (.disj (.conj A B) R) (.conj (.disj A R) (.disj B R)) :=
  pair (tensor .disj (fst A B) (id R)) (tensor .disj (snd A B) (id R))

def retraction (A B R : NormalForm P) :
    Hom (.conj (.disj A R) (.disj B R)) (.disj (.conj A B) R) :=
  comp (ofTerm (Term.mixedDisj A R B R)) (tensor .disj (id (.conj A B)) (codiag R))

theorem comparison_inl (A B R : NormalForm P) :
    comp (inl (.conj A B) R) (comparison A B R) =
      tensor .conj (inl A R) (inl B R) := by
  rw [comparison,ProductCalculation.pair_pre,Laws.inl_nat,Laws.inl_nat]
  exact (ProductCalculation.tensor_pair (inl A R) (inl B R)).symm

theorem comparison_inr (A B R : NormalForm P) :
    comp (inr (.conj A B) R) (comparison A B R) =
      comp (diag R) (tensor .conj (inr A R) (inr B R)) := by
  rw [comparison,ProductCalculation.pair_pre,Laws.inr_nat,Laws.inr_nat]
  simp only [Laws.id_comp]
  rfl

theorem comparison_retraction (A B R : NormalForm P) :
    comp (comparison A B R) (retraction A B R) = id (.disj (.conj A B) R) := by
  apply Reduced.disj_ext
  · rw [← Laws.assoc,comparison_inl,retraction,← Laws.assoc,mixed_inl,
      Laws.inl_nat,Laws.id_comp,Laws.comp_id]
  · rw [← Laws.assoc,comparison_inr,retraction]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (inr A R) (inr B R)),mixedDisj_inr]
    simp only [Laws.assoc]
    rw [Laws.inr_nat]
    rw [← Laws.assoc (diag R),← Laws.assoc (comp (diag R) (mix R R)),
      Laws.assoc (diag R),Laws.diag_mix_codiag,Laws.id_comp,Laws.comp_id]

theorem ext {S A B R : NormalForm P} (f g : Hom S (.disj (.conj A B) R))
    (ha : comp f (tensor .disj (fst A B) (id R)) = comp g (tensor .disj (fst A B) (id R)))
    (hb : comp f (tensor .disj (snd A B) (id R)) = comp g (tensor .disj (snd A B) (id R))) : f = g := by
  apply cancel_right f g (comparison A B R) (retraction A B R) (comparison_retraction A B R)
  rw [comparison,ProductCalculation.pair_pre,ProductCalculation.pair_pre,ha,hb]

end DistributiveMono
end DosenPetric.Reduced.Gentzen
