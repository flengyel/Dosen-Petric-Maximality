module

public import DosenPetric.PresentationNegationCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

theorem reduceHom_coordinates {A B : Formula P} (f : Presentation.Hom A B) (x : A.Occ) (y : B.Occ) :
    occurrenceMap (reduceHom f) (Presentation.NegationNormalization.toOcc A x)
      (Presentation.NegationNormalization.toOcc B y) ↔ Presentation.occurrenceMap f x y := by
  rw [reduceHom_occurrence]
  exact Presentation.NegationNormalization.transport_coordinates f x y

end DosenPetric.Reduced
namespace DosenPetric.Presentation
universe u
variable {P : Type u}
open NegationNormalization (normal form_true toOcc toOcc_neg)

/-- Derived source negation takes the converse relation at the original tags. -/
theorem occurrence_negate {A B : Formula P} (f : Hom A B) (x : A.Occ) (y : B.Occ) :
    occurrenceMap (negate f) y x ↔ occurrenceMap f x y := by
  have hn := Reduced.reduceHom_coordinates (negate f) y x
  rw [Reduced.reduce_negate] at hn
  have hc := Reduced.occurrence_castHom (form_true B).symm (form_true A).symm
    (Reduced.dualHom (Reduced.reduceHom f))
    (NormalForm.toDual (normal B) (toOcc B y)) (NormalForm.toDual (normal A) (toOcc A x))
  rw [← toOcc_neg B,← toOcc_neg A,NormalForm.castOcc_trans,NormalForm.castOcc_trans] at hc
  rw [toOcc_neg B,toOcc_neg A] at hc
  exact hn.symm.trans (hc.trans ((Reduced.dualHom_relation (Reduced.reduceHom f)
    (toOcc A x) (toOcc B y)).trans (Reduced.reduceHom_coordinates f x y)))

end DosenPetric.Presentation
