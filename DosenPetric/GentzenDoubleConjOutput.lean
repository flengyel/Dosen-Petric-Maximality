module

public import DosenPetric.GentzenDoubleConjSplice

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
theorem double_principal_merge (Z Q E F : O) :
    C.comp (M.tensor (D.diag Z) (C.id (M.obj Q (M.obj E F))))
      (C.comp (M.assocL Z Z (M.obj Q (M.obj E F)))
        (C.comp (M.tensor (C.id Z) (M.firstExtract Z Q E F))
          (M.secondExtract Z Q (M.obj Z E) F))) =
      C.comp (M.cross Z Q (M.obj E F))
        (M.tensor (C.id Q)
          (D.pair (M.tensor (C.id Z) (D.fst E F)) (M.tensor (C.id Z) (D.snd E F)))) := by
  simp only [MonoidalData.firstExtract,MonoidalData.secondExtract,MonoidalData.cross,
    D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,D.tensor_pair,D.pair_pre,
    D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,D.diag_fst,D.diag_snd,C.comp_id,C.assoc]

end DiagonalData
namespace Reduced.Gentzen.DoubleConjSplice
variable {P : Type u}

def mergeOutput (Z Q D E : NormalForm P) :
    Hom (.disj Q (.disj (.disj Z D) (.disj Z E))) (.disj Z (.disj Q (.disj D E))) :=
  comp (tensor .disj (id Q) (copair (tensor .disj (id Z) (inl D E)) (tensor .disj (id Z) (inr D E))))
    ((sideM P .disj).cross Z Q (.disj D E))

theorem output_square (Z Q D E : NormalForm P) :
    comp (secondOutput Z Q (.disj Z D) E)
      (comp (tensor .disj (id Z) (firstOutput Z Q D E))
        (comp (assocR .disj Z Z (.disj Q (.disj D E)))
          (tensor .disj (codiag Z) (id (.disj Q (.disj D E)))))) = mergeOutput Z Q D E := by
  have he := (disjDiagonal P).double_principal_merge (rightIn_assocL .disj) (side_swap_snd .disj) Z Q D E
  dsimp only [MonoidalData.firstExtract,MonoidalData.secondExtract,disjMonoidal,
    disjDiagonal,opposite,category,DiagonalData.pair] at he
  simpa only [firstOutput,secondOutput,mergeOutput,copair,MonoidalData.cross,
    sideM,side,disjMonoidal,opposite,category,Laws.assoc] using he

end Reduced.Gentzen.DoubleConjSplice
end DosenPetric
