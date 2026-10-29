module

public import DosenPetric.GentzenBlockedLeftDisjSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

def fixedMap {C F D : NormalForm P} (A : NormalForm P) (k : Hom (.conj C F) D) :
    Hom (.conj C (.conj F A)) D := comp (tensor .conj (id C) (fst F A)) k

theorem assocL_drop (C F A : NormalForm P) :
    comp (assocL .conj C F A) (tensor .conj (id C) (fst F A)) = fst (.conj C F) A := by
  apply Reduced.conj_ext
  all_goals simp only [ProductCalculation.assocL_pair,ProductCalculation.tensor_pair,
    ProductCalculation.pair_pre,ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem cross_drop (F X A : NormalForm P) :
    comp (terminalCross F X A) (tensor .conj (fst F A) (id X)) = fst (.conj F X) A := by
  apply Reduced.conj_ext
  all_goals simp only [terminalCross,ProductCalculation.tensor_pair,
    ProductCalculation.pair_pre,ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,Laws.comp_id]

theorem input_drop (F H Q X : NormalForm P) :
    comp (input F H Q X) (fst (.conj (.conj F X) (.conj H X)) Q) =
      comp (tensor .conj (fst (.conj F H) Q) (id X))
        (BlockedMix.sharedInput (snd F H) (fst F H)) := by
  apply Reduced.conj_ext
  all_goals simp only [input,terminalCross,BlockedMix.sharedInput,
    ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,Laws.comp_id]

theorem fixed_kernel {C F D : NormalForm P} (A R : NormalForm P) (k : Hom (.conj C F) D) :
    comp (kernel (.conj F A) C R) (tensor .disj (fixedMap A k) (id R)) =
      comp (tensor .conj (fst F A) (id (.disj C R))) (splice (id (.disj C R)) k) := by
  rw [kernel,← Splice.output,Laws.id_comp,fixedMap,Splice.context]

theorem child_fixed {C F D : NormalForm P} (A R : NormalForm P) (k : Hom (.conj C F) D) :
    comp (terminalCross F (.disj C R) A)
      (comp (kernel (.conj F A) C R) (tensor .disj (fixedMap A k) (id R))) =
      comp (fst (.conj F (.disj C R)) A) (splice (id (.disj C R)) k) := by
  rw [fixed_kernel,← Laws.assoc,cross_drop]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
