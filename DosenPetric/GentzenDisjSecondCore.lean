module

public import DosenPetric.GentzenDisjSymmetry

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
theorem second_sum_route (A B E : O) :
    C.comp (M.cross A E B) (M.swap E (M.obj A B)) =
      C.comp (M.tensor (C.id A) (M.swap E B)) (M.assocR A B E) := by
  simp only [MonoidalData.cross,D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,
    D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id]

end DiagonalData
namespace Reduced.Gentzen.DisjLogical
variable {P : Type u}

theorem second_sum_route (C D E : NormalForm P) :
    comp (swap .disj (.disj C D) E) ((sideM P .disj).cross C E D) =
      comp (assocL .disj C D E) (tensor .disj (id C) (swap .disj D E)) := by
  have he := (disjDiagonal P).second_sum_route (rightIn_assocL .disj) (side_swap_snd .disj) C D E
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he ⊢
  exact he

def secondDisjInput (T X Y Q : NormalForm P) :
    Hom (.conj T (.conj Q (.conj X Y))) (.conj Q (.conj X (.conj T Y))) :=
  comp ((sideM P .conj).cross T Q (.conj X Y))
    (tensor .conj (id Q) ((sideM P .conj).cross T X Y))

theorem second_input_route {Q R : NormalForm P} (k : Hom Q R) (T X Y : NormalForm P) :
    comp (tensor .conj (id T) (tensor .conj k (swap .conj X Y))) (firstDisjInput T Y X R) =
      comp (secondDisjInput T X Y Q) (tensor .conj k (swap .conj X (.conj T Y))) := by
  simp only [firstDisjInput,secondDisjInput,MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

theorem disjL_left_second_core {A B X Y C D E T J : NormalForm P}
    (f : Hom (.conj A X) E) (g : Hom (.conj B Y) (.disj C D)) (h : Hom (.conj C T) J) :
    splice (comp (disjPair f g) ((sideM P .disj).cross C E D)) h =
      comp (secondDisjInput T X Y (.disj A B))
        (comp (disjPair f (comp ((sideM P .conj).cross B T Y) (splice g h)))
          ((sideM P .disj).cross J E D)) := by
  have hp : comp (disjPair f g) ((sideM P .disj).cross C E D) =
      comp (tensor .conj (swap .disj A B) (swap .conj X Y))
        (comp (comp (disjPair g f) (assocL .disj C D E)) (tensor .disj (id C) (swap .disj D E))) := by
    rw [disjPair_swap]
    simp only [Laws.assoc]
    rw [second_sum_route]
  rw [hp,Splice.input,Splice.residual,disjL_left_first_core]
  conv =>
    rhs
    rw [disjPair_swap]
  simp only [Laws.assoc]
  erw [second_sum_route]
  rw [← Laws.assoc (tensor .conj (id T) (tensor .conj (swap .disj A B) (swap .conj X Y))),second_input_route]
  simp only [Laws.assoc]

end Reduced.Gentzen.DisjLogical
end DosenPetric
