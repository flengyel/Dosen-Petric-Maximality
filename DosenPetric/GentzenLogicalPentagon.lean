module

public import DosenPetric.GentzenCutOppositeConjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)

include D in
/-- The associativity comparison follows from the already proved product coordinates. -/
theorem assocL_pentagon
    (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
      M.tensor (C.id A) (M.rightOut B)) (A B U V : O) :
    C.comp (M.assocL (M.obj A B) U V) (M.assocL A B (M.obj U V)) =
      C.comp (M.tensor (M.assocL A B U) (C.id V))
        (C.comp (M.assocL A (M.obj B U) V) (M.tensor (C.id A) (M.assocL B U V))) := by
  simp only [D.assocL_pair hu, D.tensor_pair, D.pair_pre,
    D.pair_fst, D.pair_snd, D.pair_fst_comp, D.pair_snd_comp, C.comp_id, C.assoc]

end DiagonalData
end DosenPetric
