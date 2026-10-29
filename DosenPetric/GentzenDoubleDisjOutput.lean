module

public import DosenPetric.GentzenDoubleDisjSplice
public import DosenPetric.GentzenBlockedMixCore

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
theorem double_cut_output (A B R : O) :
    C.comp (M.tensor (C.id (M.obj A B)) (D.diag R))
      (C.comp (M.assocR (M.obj A B) R R)
        (C.comp (M.tensor
          (C.comp (M.assocL A B R)
            (C.comp (M.tensor (C.id A) (M.swap B R)) (M.assocR A R B))) (C.id R))
          (M.assocL (M.obj A R) B R))) =
      D.pair (M.tensor (D.fst A B) (C.id R)) (M.tensor (D.snd A B) (C.id R)) := by
  simp only [D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,D.tensor_pair,D.pair_pre,
    D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,
    C.assoc,D.diag_fst,D.diag_snd,C.comp_id]

end DiagonalData
namespace Reduced.Gentzen.DoubleDisjSplice
variable {P : Type u}

theorem output_square (D E R : NormalForm P) :
    comp (assocR .disj (.disj D R) E R)
      (comp (tensor .disj (BinaryLogical.exchangeCore .disj D R E) (id R))
        (comp (assocL .disj (.disj D E) R R)
          (tensor .disj (id (.disj D E)) (codiag R)))) = BlockedMix.sharedOutput D E R := by
  have he := (disjDiagonal P).double_cut_output (rightIn_assocL .disj) (side_swap_snd .disj) D E R
  dsimp only [disjMonoidal,disjDiagonal,opposite,category,DiagonalData.pair] at he
  simpa only [BinaryLogical.exchangeCore,BlockedMix.sharedOutput,copair,Laws.assoc] using he

end Reduced.Gentzen.DoubleDisjSplice
end DosenPetric
