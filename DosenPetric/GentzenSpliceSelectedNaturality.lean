module

public import DosenPetric.GentzenDistributiveMono
public import DosenPetric.GentzenPrincipalConjunctionRule

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Splice

/-- Change the selected formula by an actual arrow on both sides of the splice. -/
theorem selected {C C' X Y R Z : NormalForm P} (k : Hom C C')
    (h : Hom X (.disj C R)) (g : Hom (.conj C' Y) Z) :
    splice h (comp (tensor .conj k (id Y)) g) =
      splice (comp h (tensor .disj k (id R))) g := by
  have hd : comp (tensor .conj (id Y) (tensor .disj k (id R))) (dist Y C' R) =
      comp (dist Y C R) (tensor .disj (tensor .conj (id Y) k) (id R)) := by
    simpa only [Laws.tensor_id] using (Laws.dist_nat (id Y) k (id R)).symm
  unfold splice
  rw [tensor_factor]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id Y) (tensor .disj k (id R))),hd]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,Laws.id_comp]
  rw [← Laws.assoc (tensor .conj (id Y) k),← Laws.swap_nat]
  simp only [Laws.assoc]

end Splice
namespace ContractionSplice

/-- The two copies of a selected output share just one residual output. -/
theorem mixed_diagonal (C R : NormalForm P) :
    comp (diag (.disj C R))
      (comp (ofTerm (Term.mixedDisj C R C R))
        (tensor .disj (id (.conj C C)) (codiag R))) =
      tensor .disj (diag C) (id R) := by
  apply Reduced.disj_ext
  · rw [← Laws.assoc,← Laws.diag_nat]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (inl C R) (inl C R)),DistributiveMono.mixed_inl]
    rw [Laws.inl_nat,Laws.inl_nat,Laws.id_comp]
  · rw [← Laws.assoc,← Laws.diag_nat]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (inr C R) (inr C R)),mixedDisj_inr]
    simp only [Laws.assoc]
    rw [Laws.inr_nat]
    rw [← Laws.assoc (diag R),← Laws.assoc (comp (diag R) (mix R R)),
      Laws.assoc (diag R),Laws.diag_mix_codiag,Laws.id_comp,Laws.inr_nat,Laws.id_comp]

theorem duplicate_output {X C R : NormalForm P} (h : Hom X (.disj C R)) :
    comp (pair h h) (comp (ofTerm (Term.mixedDisj C R C R))
      (tensor .disj (id (.conj C C)) (codiag R))) =
      comp h (tensor .disj (diag C) (id R)) := by
  rw [pair,Laws.diag_nat,Laws.assoc,mixed_diagonal]

end ContractionSplice
end DosenPetric.Reduced.Gentzen
