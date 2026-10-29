module

public import DosenPetric.GentzenDisjRightSecondSelected

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
theorem first_right_output (U V R : O) :
    C.comp (M.assocL U V R)
      (C.comp (M.tensor (C.id U) (M.swap V R))
        (C.comp (M.assocR U R V) (M.swap (M.obj U R) V))) =
      C.comp (M.tensor (M.swap U V) (C.id R)) (M.assocL V U R) := by
  simp only [D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,D.tensor_pair,D.pair_pre,
    D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id]

end DiagonalData
namespace Reduced.Gentzen.DisjLogical
variable {P : Type u}

theorem first_right_output (U V R : NormalForm P) :
    comp (swap .disj V (.disj U R)) (BinaryLogical.exchangeCore .disj U R V) =
      comp (assocR .disj V U R) (tensor .disj (swap .disj V U) (id R)) := by
  have he := (disjDiagonal P).first_right_output (rightIn_assocL .disj) (side_swap_snd .disj) U V R
  dsimp only [disjMonoidal,opposite,category,BinaryLogical.exchangeCore] at he ⊢
  simpa only [Laws.assoc] using he

theorem first_right_head_route {Q R : NormalForm P} (k : Hom Q R) (C X Y : NormalForm P) :
    comp (firstDisjInput C X Y Q) (tensor .conj k (swap .conj (.conj C X) Y)) =
      comp (tensor .conj (id C) (tensor .conj k (swap .conj X Y))) (secondDisjInput C Y X R) := by
  simp only [firstDisjInput,secondDisjInput,MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

theorem first_right_input_route {Q R : NormalForm P} (k : Hom Q R) (X Y W : NormalForm P) :
    comp (tensor .conj (tensor .conj k (swap .conj X Y)) (id W))
      (comp (assocL .conj R (.conj Y X) W) (tensor .conj (id R) (assocL .conj Y X W))) =
      comp (assocL .conj Q (.conj X Y) W)
        (comp (tensor .conj (id Q) (BinaryLogical.exchangeCore .conj X Y W))
          (tensor .conj k (swap .conj (.conj X W) Y))) := by
  simp only [BinaryLogical.exchangeCore,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

theorem disjL_right_first_core {A B X Y C R U V W : NormalForm P}
    (f : Hom (.conj A (.conj C X)) U) (g : Hom (.conj B Y) V) (h : Hom W (.disj C R)) :
    splice h (comp (firstDisjInput C X Y (.disj A B)) (disjPair f g)) =
      comp (assocL .conj (.disj A B) (.conj X Y) W)
        (comp (tensor .conj (id (.disj A B)) (BinaryLogical.exchangeCore .conj X Y W))
          (comp (disjPair
            (comp (assocR .conj A X W) (splice h (comp ((sideM P .conj).cross C A X) f))) g)
            (BinaryLogical.exchangeCore .disj U R V))) := by
  have hg : comp (firstDisjInput C X Y (.disj A B)) (disjPair f g) =
      comp (comp (tensor .conj (id C) (tensor .conj (swap .disj A B) (swap .conj X Y)))
        (comp (secondDisjInput C Y X (.disj B A)) (disjPair g f))) (swap .disj V U) := by
    rw [disjPair_swap]
    simp only [Laws.assoc]
    rw [← Laws.assoc (firstDisjInput C X Y (.disj A B)),first_right_head_route]
    simp only [Laws.assoc]
  rw [hg,Splice.output,Splice.context,disjL_right_second_core]
  conv =>
    rhs
    rw [disjPair_swap]
  simp only [Laws.assoc]
  rw [first_right_output]
  have he := congrArg (fun p => comp p
    (comp (disjPair g (comp (assocR .conj A X W) (splice h (comp ((sideM P .conj).cross C A X) f))))
      (comp (assocR .disj V U R) (tensor .disj (swap .disj V U) (id R)))))
      (first_right_input_route (swap .disj A B) X Y W)
  simpa only [Laws.assoc] using he

end Reduced.Gentzen.DisjLogical
end DosenPetric
