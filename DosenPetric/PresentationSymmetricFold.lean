module

public import DosenPetric.ManuscriptStructuralDiagrams

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

theorem tensor_prodMap {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    tensor .conj f g = (operations P).prodMap f g := by
  apply coherence
  have hm : occurrenceMap ((operations P).prodMap f g) =
      Relations.sumMap (occurrenceMap f) (occurrenceMap g) := (interpretation P).map_prodMap f g
  rw [occurrence_tensor_conj,hm]

/-- The formal fold in the retained route is exactly the manuscript's mix;codiag. -/
theorem fold_source_mix (A B : Formula P) :
    (operations P).fold A B = comp (mix A A) (codiag A) := by
  change comp (comp ((operations P).prodMap (id A) (inr B A))
    (dist A B A)) (copair (fst A B) (id A)) = _
  rw [Laws.assoc,← tensor_prodMap,copair,Laws.dist_mix A B A]
  simp only [Laws.assoc]

theorem codiag_copair_id (A : Formula P) : codiag A = copair (id A) (id A) := by
  rw [copair,Laws.tensor_id,Laws.id_comp]

/-- The displayed h_A uses the copair of two identities, at these exact types. -/
theorem fold_manuscript (A B : Formula P) :
    (operations P).fold A B = comp (mix A A) (copair (id A) (id A)) := by
  rw [fold_source_mix,← codiag_copair_id]

theorem mix_parameter_independent (A C B D : Formula P) :
    comp (tensor .conj (id A) (inr B C))
      (comp (dist A B C) (tensor .disj (fst A B) (id C))) =
    comp (tensor .conj (id A) (inr D C))
      (comp (dist A D C) (tensor .disj (fst A D) (id C))) :=
  (Laws.dist_mix A B C).symm.trans (Laws.dist_mix A D C)

theorem fold_parameter_independent (A B D : Formula P) :
    (operations P).fold A B = (operations P).fold A D := by
  rw [fold_source_mix,fold_source_mix]

/-- The exact pair-of-projections symmetry stated in manuscript §6. -/
theorem fold_symmetric (A : Formula P) :
    comp (pair (snd A A) (fst A A)) (comp (mix A A) (codiag A)) =
      comp (mix A A) (codiag A) := by
  have hh := (interpretation P).fold_swap A .bot
  change comp (pair (snd A A) (fst A A)) ((operations P).fold A .bot) =
    (operations P).fold A .bot at hh
  rw [fold_source_mix] at hh
  exact hh

end DosenPetric.Presentation
