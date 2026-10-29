module

public import DosenPetric.PresentationSubstitutionOperations
public import DosenPetric.PresentationSymmetricFold

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- Uniqueness does not assert the existence of an arrow from top. -/
instance top_hom_subsingleton (A : Formula P) : Subsingleton (Hom .top A) :=
  ⟨fromTop_unique⟩

theorem literal_identity_ne_zero (l : Literal P) : id l.formula ≠ zeroConstruction l.formula := by
  intro h
  have he : occurrenceMap (id l.formula) l.point l.point := rfl
  rw [h] at he
  have hz : occurrenceMap (zeroConstruction l.formula) = Relations.empty := (interpretation P).map_zero l.formula
  rw [hz] at he
  exact he

theorem identity_ne_zero (p : P) : id (.var p) ≠ zeroConstruction (.var p) :=
  literal_identity_ne_zero (.pos p)

theorem identity_ne_primitive_zero (p : P) : id (.var p) ≠ zero (.var p) := by
  intro h
  exact identity_ne_zero p (h.trans (zeroConstruction_eq (.var p)).symm)

end DosenPetric.Presentation
