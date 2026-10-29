module

public import DosenPetric.GentzenConjLeftStrength

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
theorem deletion_input (A T R : O) :
    C.comp (M.assocR A R T)
      (C.comp (M.swap (M.obj A R) T) (M.cross T A R)) =
      M.tensor (C.id A) (M.swap R T) := by
  simp only [MonoidalData.cross,D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,
    D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id]

include hu hs in
theorem deletion_output (Q T R E : O) :
    C.comp (M.swap T (M.obj Q (M.obj R E)))
      (C.comp (M.assocL Q (M.obj R E) T)
        (C.comp (M.tensor (C.id Q)
          (C.comp (M.assocL R E T)
            (C.comp (M.tensor (C.id R) (M.swap E T)) (M.assocR R T E))))
          (M.tensor (C.id Q) (M.tensor (M.swap R T) (C.id E))))) =
      C.comp (M.cross T Q (M.obj R E)) (M.tensor (C.id Q) (M.assocR T R E)) := by
  simp only [MonoidalData.cross,D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,
    D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id,C.assoc]

include hu hs in
theorem cross_inverse (A B E : O) :
    C.comp (M.cross A B E) (M.cross B A E) = C.id (M.obj A (M.obj B E)) := by
  simp only [MonoidalData.cross,D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,
    D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id]
  rw [D.pair_eta]
  simpa only [C.id_comp] using D.pair_eta (C.id (M.obj A (M.obj B E)))

end DiagonalData
namespace Reduced.Gentzen
variable {P : Type u}
namespace BinaryLogical

theorem deletion_input (A C D : NormalForm P) :
    comp ((sideM P .disj).cross C A D)
      (comp (swap .disj C (.disj A D)) (assocL .disj A D C)) =
      tensor .disj (id A) (swap .disj C D) := by
  have he := (disjDiagonal P).deletion_input (rightIn_assocL .disj) (side_swap_snd .disj) A C D
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he ⊢
  simpa only [Laws.assoc] using he

theorem deletion_output (Q C D E : NormalForm P) :
    comp (tensor .disj (id Q) (tensor .disj (swap .disj C D) (id E)))
      (comp (residualOutput Q D C E) (swap .disj (.disj Q (.disj D E)) C)) =
      comp (tensor .disj (id Q) (assocL .disj C D E))
        ((sideM P .disj).cross C Q (.disj D E)) := by
  have he := (disjDiagonal P).deletion_output (rightIn_assocL .disj) (side_swap_snd .disj) Q C D E
  dsimp only [residualOutput,exchangeCore,sideM,side,disjMonoidal,opposite,category] at he ⊢
  simpa only [Laws.assoc] using he

theorem disj_cross_inverse (A B E : NormalForm P) :
    comp ((sideM P .disj).cross B A E) ((sideM P .disj).cross A B E) =
      id (.disj A (.disj B E)) :=
  (disjDiagonal P).cross_inverse (rightIn_assocL .disj) (side_swap_snd .disj) A B E

end BinaryLogical
end Reduced.Gentzen
end DosenPetric
