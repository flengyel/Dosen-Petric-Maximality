module

public import DosenPetric.PatternSubstitutionProfiles
public import DosenPetric.FormulaSubstitutionOrdinals
public import DosenPetric.FormulaSkeletonProfiles

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PatternProfiles
open FiniteBlocks
variable {k : Nat} {l : Fin k → Nat}
  (M : Formula (Fin k)) (N : ∀ i, Formula (Fin (l i)))

theorem insertion_blockSizes : M.blockSizes (insertion N) = fun r => (N (M.profile r)).occurrenceCount := by
  funext r
  exact (N (M.profile r)).rename_count (tag (M.profile r))

theorem composite_count : (M.subst (insertion N)).occurrenceCount = total (fun r => (data M N).n ((data M N).outer r)) := by
  rw [Formula.substitution_count,insertion_blockSizes]
  rfl

/-- The abstract source-block encoding is exactly the actual left-to-right
occurrence index, not merely an arbitrary bijection of finite sets. -/
theorem chiInverse_index (z : (data M N).Domain) :
    ((M.subst (insertion N)).occurrenceIndex (chiInverse M N z)).val =
      (encode (fun r => (data M N).n ((data M N).outer r)) z).val := by
  rw [chiInverse,Formula.substitution_index]
  change prefixSum (M.blockSizes (insertion N)) (M.occurrenceIndex (M.occurrenceAt z.1)) +
    (((N (M.profile z.1)).rename (tag (M.profile z.1))).occurrenceIndex
      ((N (M.profile z.1)).renameOcc (tag (M.profile z.1)) ((N (M.profile z.1)).occurrenceAt z.2))).val = _
  rw [Formula.occurrenceIndex_at,insertion_blockSizes,Formula.rename_index_value,Formula.occurrenceIndex_at,encode_value]
  rfl

theorem chiInverse_encoding (z : (data M N).Domain) :
    Fin.cast (composite_count M N) ((M.subst (insertion N)).occurrenceIndex (chiInverse M N z)) =
      encode (fun r => (data M N).n ((data M N).outer r)) z := by
  apply Fin.ext
  exact chiInverse_index M N z

/-- All four sides of the actual occurrence/profile/ordinal diagram commute. -/
theorem actual_ordinal_square (x : (M.subst (insertion N)).Occ) :
    (data M N).delta (Fin.cast (composite_count M N) ((M.subst (insertion N)).occurrenceIndex x)) =
      encode (data M N).l ((M.subst (insertion N)).label x) := by
  rw [← chiInverse_chi M N x,chiInverse_encoding,ProfileComposition.Data.ordinal_square,chiInverse_label]

theorem composite_profile (i : Fin (M.subst (insertion N)).occurrenceCount) :
    encode (data M N).l ((M.subst (insertion N)).profile i) =
      (data M N).delta (Fin.cast (composite_count M N) i) := by
  have he := actual_ordinal_square M N ((M.subst (insertion N)).occurrenceAt i)
  rw [Formula.occurrenceIndex_at] at he
  exact he.symm

/-- Flatten the tagged target placeholder blocks to the book's finite ordinal. -/
def flattened : Formula (Fin (total (data M N).l)) :=
  (M.subst (insertion N)).rename (encode (data M N).l)

theorem generalized_composite_skeleton : (flattened M N).skeleton = (M.subst (insertion N)).skeleton :=
  (M.subst (insertion N)).skeleton_rename (encode (data M N).l)

theorem flattened_count : (flattened M N).occurrenceCount = total (fun r => (data M N).n ((data M N).outer r)) :=
  ((M.subst (insertion N)).rename_count (encode (data M N).l)).trans (composite_count M N)

theorem flattened_profile (i : Fin (flattened M N).occurrenceCount) :
    (flattened M N).profile i = (data M N).delta (Fin.cast (flattened_count M N) i) := by
  change ((M.subst (insertion N)).rename (encode (data M N).l)).profile i = _
  rw [Formula.profile_renaming,composite_profile]
  congr 1

theorem flattened_skeleton_count : (flattened M N).skeleton.occurrenceCount =
    total (fun r => (data M N).n ((data M N).outer r)) :=
  ((flattened M N).rename_count (fun _ => ())).trans (flattened_count M N)

/-- The substituted skeleton together with delta reconstructs the generalized
composite, exactly as in the book's skeleton/profile notation. -/
theorem generalized_composite_reconstruction :
    Formula.fromSkeletonProfile (flattened M N).skeleton
      (fun i => (data M N).delta (Fin.cast (flattened_skeleton_count M N) i)) = flattened M N := by
  have he : (fun i => (data M N).delta (Fin.cast (flattened_skeleton_count M N) i)) =
      (flattened M N).skeletonProfile := by
    funext i
    unfold Formula.skeletonProfile
    rw [flattened_profile]
    congr 1
  rw [he,Formula.skeleton_profile_reconstruction]

end DosenPetric.PatternProfiles
