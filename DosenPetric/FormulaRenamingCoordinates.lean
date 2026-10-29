module

public import DosenPetric.FormulaRenaming

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Formula
universe u v
variable {P : Type u} {Q : Type v}

theorem rename_index_value (ρ : P → Q) (A : Formula P) (x : A.Occ) :
    ((A.rename ρ).occurrenceIndex (A.renameOcc ρ x)).val = (A.occurrenceIndex x).val := by
  induction A with
  | var p => rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ih ih' | disj A B ih ih' =>
    cases x with
    | inl x => exact ih x
    | inr x =>
      change (A.rename ρ).occurrenceCount + ((B.rename ρ).occurrenceIndex (B.renameOcc ρ x)).val =
        A.occurrenceCount + (B.occurrenceIndex x).val
      rw [rename_count,ih']
  | neg A ih => exact ih x

theorem profile_renaming (ρ : P → Q) (A : Formula P) (i : Fin (A.rename ρ).occurrenceCount) :
    (A.rename ρ).profile i = ρ (A.profile (Fin.cast (A.rename_count ρ) i)) := by
  let j := Fin.cast (A.rename_count ρ) i
  have he : (A.rename ρ).occurrenceIndex (A.renameOcc ρ (A.occurrenceAt j)) = i := by
    apply Fin.ext
    rw [rename_index_value,occurrenceIndex_at]
    rfl
  have hp := congrArg (A.rename ρ).occurrenceAt he
  rw [occurrenceAt_index] at hp
  change (A.rename ρ).label ((A.rename ρ).occurrenceAt i) = ρ (A.label (A.occurrenceAt j))
  rw [← hp,rename_label]

end DosenPetric.Formula
