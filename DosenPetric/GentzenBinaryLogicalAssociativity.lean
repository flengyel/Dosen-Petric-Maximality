module

public import DosenPetric.GentzenBinaryMixRightStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)

include D in
theorem assocR_pentagon
    (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
      M.tensor (C.id A) (M.rightOut B)) (A B U V : O) :
    C.comp (M.assocR A B (M.obj U V)) (M.assocR (M.obj A B) U V) =
      C.comp (M.tensor (C.id A) (M.assocR B U V))
        (C.comp (M.assocR A (M.obj B U) V) (M.tensor (M.assocR A B U) (C.id V))) := by
  simp only [D.assocR_pair hu,D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,
    D.pair_fst_comp,D.pair_snd_comp,C.comp_id,C.assoc]

end DiagonalData
namespace Reduced.Gentzen
variable {P : Type u}
namespace BinaryLogical

theorem disj_assocL_pentagon (A B D E : NormalForm P) :
    comp (tensor .disj (assocL .disj A B D) (id E))
      (comp (assocL .disj A (.disj B D) E) (tensor .disj (id A) (assocL .disj B D E))) =
      comp (assocL .disj (.disj A B) D E) (assocL .disj A B (.disj D E)) := by
  have he := (disjDiagonal P).assocR_pentagon (rightIn_assocL .disj) A B D E
  dsimp only [disjMonoidal,opposite,category] at he
  simpa only [Laws.assoc] using he.symm

end BinaryLogical
end Reduced.Gentzen
end DosenPetric
