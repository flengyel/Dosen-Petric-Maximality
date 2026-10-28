module

public import DosenPetric.GentzenMixedDisjSymmetry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

/-- Exchange the last two factors of a left-associated triple. -/
def exchangeCore (o : Op) (X Y Z : NormalForm P) :
    Hom (o.formula (o.formula X Y) Z) (o.formula (o.formula X Z) Y) :=
  comp (assocL o X Y Z)
    (comp (tensor o (id X) (swap o Y Z)) (assocR o X Z Y))

theorem first_product_route (C Y X : NormalForm P) :
    assocR .conj C Y X =
      comp (tensor .conj (id C) (swap .conj Y X))
        (comp ((sideM P .conj).cross C X Y) (swap .conj X (.conj C Y))) := by
  change _ = comp (tensor .conj (id C) (swap .conj Y X))
    (comp (comp (assocR .conj C X Y)
      (comp (tensor .conj (swap .conj C X) (id Y)) (assocL .conj X C Y)))
      (swap .conj X (.conj C Y)))
  simp only [ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem first_splice_route (Y X W : NormalForm P) :
    comp (exchangeCore .conj Y X W) (swap .conj (.conj Y W) X) =
      comp (tensor .conj (swap .conj Y X) (id W)) (assocL .conj X Y W) := by
  simp only [exchangeCore,ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

/-- Cut through the first product factor, retaining the second factor. -/
theorem product_left_splice {W C R Y Z X E : NormalForm P}
    (h : Hom W (.disj C R)) (f : Hom (.conj C Y) Z) (g : Hom X E) :
    splice h (comp (assocR .conj C Y X) (tensor .conj f g)) =
      comp (exchangeCore .conj Y X W)
        (comp (tensor .conj (splice h f) g) (innerDisj Z R E)) := by
  have hf : comp (assocR .conj C Y X) (tensor .conj f g) =
      comp (tensor .conj (id C) (swap .conj Y X))
        (comp ((sideM P .conj).cross C X Y)
          (comp (tensor .conj g f) (swap .conj E Z))) := by
    rw [first_product_route]
    simp only [Laws.assoc]
    rw [Laws.swap_nat]
  have hs : splice h (comp ((sideM P .conj).cross C X Y)
      (comp (tensor .conj g f) (swap .conj E Z))) =
      comp (splice h (comp ((sideM P .conj).cross C X Y) (tensor .conj g f)))
        (tensor .disj (swap .conj E Z) (id R)) := by
    simpa only [Laws.assoc] using Splice.output h
      (comp ((sideM P .conj).cross C X Y) (tensor .conj g f)) (swap .conj E Z)
  rw [hf,Splice.context,hs,product_right_splice]
  unfold innerDisj
  have hn := Laws.swap_nat .conj (splice h f) g
  have he := congrArg (fun k => comp (exchangeCore .conj Y X W)
    (comp k (comp (dist E Z R) (tensor .disj (swap .conj E Z) (id R))))) hn
  simp only [Laws.assoc] at he ⊢
  rw [← Laws.assoc (exchangeCore .conj Y X W),first_splice_route] at he
  simpa only [Laws.assoc] using he

end BinaryLogical
end DosenPetric.Reduced.Gentzen
