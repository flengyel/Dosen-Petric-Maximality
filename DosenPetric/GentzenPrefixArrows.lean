module

public import DosenPetric.GentzenSelectedOppositeStructural

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Lift an arbitrary side arrow through a fixed context prefix. -/
def prefixSide (o : Op) : (K : List (NormalForm P)) →
    {U V : List (NormalForm P)} → (side P o).Hom (fold o U) (fold o V) →
    (side P o).Hom (fold o (K ++ U)) (fold o (K ++ V))
  | [], _, _, r => r
  | A :: K, _, _, r => (sideM P o).tensor ((side P o).id A) (prefixSide o K r)

/-- Naturality of the actual append comparison under a fixed prefix. -/
theorem prefixSide_join (o : Op) (K : List (NormalForm P))
    {U V : List (NormalForm P)} (r : (side P o).Hom (fold o U) (fold o V)) :
    (side P o).comp (join o K U) (prefixSide o K r) =
      (side P o).comp ((sideM P o).tensor ((side P o).id (fold o K)) r) (join o K V) := by
  let C := side P o
  let M := sideM P o
  induction K with
  | nil => rw [join_nil,join_nil]; exact M.leftOut_nat r
  | cons A K ih =>
    rw [join_cons,join_cons]
    change C.comp (C.comp (M.assocL A (fold o K) (fold o U))
      (M.tensor (C.id A) (join o K U))) (M.tensor (C.id A) (prefixSide o K r)) =
      C.comp (M.tensor (C.id (o.formula A (fold o K))) r)
        (C.comp (M.assocL A (fold o K) (fold o V)) (M.tensor (C.id A) (join o K V)))
    rw [C.assoc,M.tensor_comp,C.id_comp,ih]
    have ht : M.tensor (C.id A) (C.comp (M.tensor (C.id (fold o K)) r) (join o K V)) =
        C.comp (M.tensor (C.id A) (M.tensor (C.id (fold o K)) r))
          (M.tensor (C.id A) (join o K V)) := by rw [M.tensor_comp,C.id_comp]
    rw [ht,← C.assoc,M.assocL_nat,M.tensor_id,C.assoc]

/-- The corresponding split square, with both actual comparison inverses. -/
theorem prefixSide_split (o : Op) (K : List (NormalForm P))
    {U V : List (NormalForm P)} (r : (side P o).Hom (fold o U) (fold o V)) :
    (side P o).comp (prefixSide o K r) (split o K V) =
      (side P o).comp (split o K U) ((sideM P o).tensor ((side P o).id (fold o K)) r) := by
  let C := side P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o K U) (split o K U) (split_join o K U)
  rw [← C.assoc,prefixSide_join,C.assoc,join_split,C.comp_id,
    ← C.assoc,join_split,C.id_comp]

end DosenPetric.Reduced.Gentzen
