module

public import DosenPetric.GentzenConjSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
universe u
variable {P : Type u}
namespace BinaryLogical

def cross (o : Op) (A B E : NormalForm P) :
    Hom (o.formula A (o.formula B E)) (o.formula B (o.formula A E)) :=
  comp (assocR o A B E)
    (comp (tensor o (swap o A B) (id E)) (assocL o B A E))

def coCross (A B E : NormalForm P) : Hom (.disj B (.disj A E)) (.disj A (.disj B E)) :=
  cross .disj B A E

def innerDisj (A D B : NormalForm P) := CutDistribution.step A D B

theorem mixedDisj_eq (A D B E : NormalForm P) :
    mixedDisj A D B E =
      comp (dist (.disj A D) B E)
        (comp (tensor .disj (innerDisj A D B) (id E)) (assocL .disj (.conj A B) D E)) := rfl

theorem product_outer_route (Y C T : NormalForm P) :
    comp (assocL .conj Y T C) (tensor .conj (id Y) (swap .conj T C)) =
      comp (swap .conj (.conj Y T) C) (cross .conj C Y T) := by
  simp only [cross,ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem disj_assocL_pentagon (A B D E : NormalForm P) :
    comp (tensor .disj (assocL .disj A B D) (id E))
      (comp (assocL .disj A (.disj B D) E) (tensor .disj (id A) (assocL .disj B D E))) =
      comp (assocL .disj (.disj A B) D E) (assocL .disj A B (.disj D E)) := by
  dsimp only [comp,tensor,assocL,id,mirror]
  simp only [Gentzen.ProductCalculation.assocL_pair,Gentzen.ProductCalculation.tensor_pair,
    Gentzen.ProductCalculation.pair_pre,Gentzen.ProductCalculation.pair_fst,
    Gentzen.ProductCalculation.pair_snd,Gentzen.ProductCalculation.pair_fst_comp,
    Gentzen.ProductCalculation.pair_snd_comp,Reduced.Laws.comp_id,Reduced.Laws.assoc]

end BinaryLogical
end DosenPetric.Reduced.Gentzen.MirrorCalculus
