module

public import DosenPetric.GentzenDoubleDisjInput
public import DosenPetric.GentzenBlockedLeftDisjFixedEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

def frontChild (C F A : NormalForm P) : Hom (.conj A (.conj C F)) (.conj C (.conj F A)) :=
  comp ((sideM P .conj).cross A C F) (tensor .conj (id C) (swap .conj A F))

theorem frontChild_square (C F A : NormalForm P) :
    comp (swap .conj (.conj C F) A) (frontChild C F A) = assocL .conj C F A := by
  simp only [frontChild,MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem frontChild_head (C F A : NormalForm P) :
    comp ((sideM P .conj).cross C A F) (frontChild C F A) =
      tensor .conj (id C) (swap .conj A F) := by
  simp only [frontChild,MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem child_terminal_input (A F X : NormalForm P) :
    comp (swap .conj (.conj F X) A)
      (comp (assocR .conj A F X) (tensor .conj (swap .conj A F) (id X))) =
      terminalCross F X A := by
  simp only [terminalCross,ProductCalculation.assocR_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem parent_input_square (C F H Q : NormalForm P) :
    comp (tensor .conj (diag C) (id (.conj Q (.conj F H))))
      (comp (assocL .conj C C (.conj Q (.conj F H)))
        (comp (DoubleDisjSplice.twoHead C F H Q)
          (swap .conj Q (.conj (.conj C F) (.conj C H))))) =
      comp (tensor .conj (id C) (swap .conj Q (.conj F H)))
        (comp (assocR .conj C (.conj F H) Q)
          (tensor .conj
            (pair (tensor .conj (id C) (fst F H)) (tensor .conj (id C) (snd F H))) (id Q))) := by
  simp only [DoubleDisjSplice.twoHead,DisjLogical.firstDisjInput,DisjLogical.secondDisjInput,
    MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,
    Laws.assoc,Laws.diag_fst,Laws.diag_snd,Laws.comp_id]

theorem parallel_input_square (F H Q X : NormalForm P) :
    comp (tensor .conj (swap .conj (.conj F H) Q) (id X))
      (comp (DoubleDisjSplice.parallelInput Q F H X)
        (swap .conj Q (.conj (.conj F X) (.conj H X)))) = input F H Q X := by
  simp only [DoubleDisjSplice.parallelInput,input,terminalCross,BlockedMix.sharedInput,
    ProductCalculation.assocL_pair,ProductCalculation.swap_pair,ProductCalculation.tensor_pair,
    ProductCalculation.pair_pre,ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
