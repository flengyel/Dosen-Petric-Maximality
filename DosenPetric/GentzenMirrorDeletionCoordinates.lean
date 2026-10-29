module

public import DosenPetric.GentzenMirrorBinaryResidual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
variable {P : Type u}
namespace BinaryLogical

theorem deletion_input (A C D : NormalForm P) :
    comp (coCross C A D)
      (comp (swap .disj C (.disj A D)) (assocL .disj A D C)) =
      tensor .disj (id A) (swap .disj C D) := by
  dsimp only [residualOutput,exchangeCore,coCross,cross,comp,tensor,assocL,assocR,swap,id,mirror]
  simp only [Gentzen.ProductCalculation.assocR_pair,Gentzen.ProductCalculation.assocL_pair,
    Gentzen.ProductCalculation.swap_pair,Gentzen.ProductCalculation.tensor_pair,
    Gentzen.ProductCalculation.pair_pre,Gentzen.ProductCalculation.pair_fst,
    Gentzen.ProductCalculation.pair_snd,Gentzen.ProductCalculation.pair_fst_comp,
    Gentzen.ProductCalculation.pair_snd_comp,Reduced.Laws.comp_id]

theorem deletion_output (Q C D E : NormalForm P) :
    comp (tensor .disj (id Q) (tensor .disj (swap .disj C D) (id E)))
      (comp (residualOutput Q D C E) (swap .disj (.disj Q (.disj D E)) C)) =
      comp (tensor .disj (id Q) (assocL .disj C D E))
        (coCross C Q (.disj D E)) := by
  dsimp only [residualOutput,exchangeCore,coCross,cross,comp,tensor,assocL,assocR,swap,id,mirror]
  simp only [Gentzen.ProductCalculation.assocR_pair,Gentzen.ProductCalculation.assocL_pair,
    Gentzen.ProductCalculation.swap_pair,Gentzen.ProductCalculation.tensor_pair,
    Gentzen.ProductCalculation.pair_pre,Gentzen.ProductCalculation.pair_fst,
    Gentzen.ProductCalculation.pair_snd,Gentzen.ProductCalculation.pair_fst_comp,
    Gentzen.ProductCalculation.pair_snd_comp,Reduced.Laws.comp_id,Reduced.Laws.assoc]

theorem disj_cross_inverse (A B E : NormalForm P) :
    comp (coCross B A E) (coCross A B E) = id (.disj A (.disj B E)) := by
  dsimp only [coCross,cross,comp,tensor,assocL,assocR,swap,id,mirror]
  simp only [Gentzen.ProductCalculation.assocR_pair,Gentzen.ProductCalculation.assocL_pair,
    Gentzen.ProductCalculation.swap_pair,Gentzen.ProductCalculation.tensor_pair,
    Gentzen.ProductCalculation.pair_pre,Gentzen.ProductCalculation.pair_fst,
    Gentzen.ProductCalculation.pair_snd,Gentzen.ProductCalculation.pair_fst_comp,
    Gentzen.ProductCalculation.pair_snd_comp,Reduced.Laws.comp_id]
  have eta {V A B : NormalForm P} (f : Reduced.Hom V (.conj A B)) :
      Reduced.pair (Reduced.comp f (Reduced.fst A B)) (Reduced.comp f (Reduced.snd A B)) = f :=
    (conjDiagonal P).pair_eta f
  rw [eta (Reduced.fst (.conj (mirror E) (mirror B)) (mirror A))]
  simpa only [Reduced.Laws.id_comp] using
    eta (Reduced.id (.conj (.conj (mirror E) (mirror B)) (mirror A)))

end BinaryLogical
end DosenPetric.Reduced.Gentzen.MirrorCalculus
