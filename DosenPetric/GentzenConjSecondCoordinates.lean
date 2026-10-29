module

public import DosenPetric.GentzenConjLeftSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)
variable (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
  M.tensor (C.id A) (M.rightOut B))
variable (hs : ∀ A B, C.comp (M.swap A B) (D.snd B A) = D.fst A B)

include hu hs in
theorem second_deletion (Q A B E : O) :
    C.comp (M.cross A Q (M.obj B E))
      (C.comp (M.tensor (C.id Q) (M.cross A B E))
        (M.tensor (C.id Q) (M.swap B (M.obj A E)))) =
      C.comp (M.tensor (C.id A) (M.tensor (C.id Q) (M.swap B E)))
        (C.comp (M.cross A Q (M.obj E B))
          (M.tensor (C.id Q) (M.assocR A E B))) := by
  simp only [MonoidalData.cross,D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,
    D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id,C.assoc]

end DiagonalData
namespace Reduced.Gentzen
variable {P : Type u}
namespace BinaryLogical

theorem second_deletion (Q C D E : NormalForm P) :
    comp (tensor .disj (id Q) (swap .disj (.disj C E) D))
      (comp (tensor .disj (id Q) ((sideM P .disj).cross C D E))
        ((sideM P .disj).cross C Q (.disj D E))) =
      comp (tensor .disj (id Q) (assocL .disj C E D))
        (comp ((sideM P .disj).cross C Q (.disj E D))
          (tensor .disj (id C) (tensor .disj (id Q) (swap .disj E D)))) := by
  have he := (disjDiagonal P).second_deletion (rightIn_assocL .disj) (side_swap_snd .disj) Q C D E
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he ⊢
  simpa only [Laws.assoc] using he

end BinaryLogical
end Reduced.Gentzen
end DosenPetric
