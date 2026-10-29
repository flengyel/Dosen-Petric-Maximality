module

public import DosenPetric.GentzenDisjRightReflection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

def selectedBranch (Y B C : NormalForm P) : Hom (.conj (.conj Y C) B) (.conj B (.conj C Y)) :=
  comp (swap .conj (.conj Y C) B) (tensor .conj (id B) (swap .conj Y C))

def selectedHeadInput (C X Y Q : NormalForm P) :
    Hom (.conj (.conj (.conj X Y) Q) C) (.conj C (.conj Q (.conj X Y))) :=
  comp (swap .conj (.conj (.conj X Y) Q) C) (tensor .conj (id C) (swap .conj (.conj X Y) Q))

theorem selected_source_input (X Y Q C : NormalForm P) :
    comp (BinaryLogical.exchangeCore .conj (.conj X Y) Q C)
      (comp (tensor .conj (assocL .conj X Y C) (id Q))
        (comp (swap .conj (.conj X (.conj Y C)) Q)
          (tensor .conj (id Q) (tensor .conj (id X) (swap .conj Y C))))) =
      comp (selectedHeadInput C X Y Q) (secondDisjInput C X Y Q) := by
  simp only [BinaryLogical.exchangeCore,selectedHeadInput,secondDisjInput,
    MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

theorem selected_child_head (Y B C : NormalForm P) :
    comp (swap .conj C (.conj Y B))
      (comp (BinaryLogical.exchangeCore .conj Y B C) (selectedBranch Y B C)) =
      comp (tensor .conj (id C) (swap .conj Y B)) ((sideM P .conj).cross C B Y) := by
  simp only [BinaryLogical.exchangeCore,selectedBranch,
    MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem selected_child_result (Y B W : NormalForm P) :
    comp (BinaryLogical.exchangeCore .conj Y W B) (tensor .conj (swap .conj Y B) (id W)) =
      comp (selectedBranch Y B W)
        (comp (tensor .conj (id B) (swap .conj W Y)) (assocR .conj B Y W)) := by
  simp only [BinaryLogical.exchangeCore,selectedBranch,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem selected_parent_result (X Y Q W : NormalForm P) :
    comp (selectedHeadInput W X Y Q)
      (comp (secondDisjInput W X Y Q)
        (tensor .conj (id Q) (tensor .conj (id X) (swap .conj W Y)))) =
      comp (tensor .conj (swap .conj (.conj X Y) Q) (id W))
        (comp (assocL .conj Q (.conj X Y) W) (tensor .conj (id Q) (assocL .conj X Y W))) := by
  simp only [selectedHeadInput,secondDisjInput,
    MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

end DisjLogical
end DosenPetric.Reduced.Gentzen
