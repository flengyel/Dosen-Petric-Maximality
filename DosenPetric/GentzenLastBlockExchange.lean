module

public import DosenPetric.GentzenConjFirstCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

def tailExchange (F U V : List (NormalForm P)) :
    ExchangeScript P (F ++ (V ++ U)) (F ++ (U ++ V)) :=
  (ExchangeScript.exchange F U V []).reindex
    (by simp only [List.append_nil,List.append_assoc])
    (by simp only [List.append_nil,List.append_assoc])

theorem tailExchange_arrow (o : Op) (F U V : List (NormalForm P)) :
    (tailExchange F U V).arrow o = prefixSide o F ((BinaryMix.swapWhole U V).arrow o) := by
  induction F with
  | nil =>
    apply side_ext o
    intro E a
    rw [ExchangeScript.component]
    change component o _ = (side P o).comp ((BinaryMix.swapWhole U V).arrow o) (component o a)
    rw [ExchangeScript.component]
    apply congrArg (component o)
    apply At.index_injective
    simp only [tailExchange,BinaryMix.swapWhole,BinaryMix.swapBlocks,ExchangeScript.get,
      ExchangeScript.rewire,Rewire.get,At.index_cast,swapBlocks_index]
  | cons A F ih =>
    have he : (tailExchange (A :: F) U V).arrow o =
        (sideM P o).tensor ((side P o).id A) ((tailExchange F U V).arrow o) := by
      apply side_ext o
      intro E a
      rw [ExchangeScript.component]
      cases a with
      | here =>
        rw [component_here]
        erw [← (sideD P o).fst_nat,(side P o).comp_id]
        rw [← component_here]
        apply congrArg (component o)
        apply At.index_injective
        simp only [tailExchange,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
          At.index_cast,swapBlocks_index,List.length_cons,At.index,exchangeIndex]
        simp only [Nat.zero_lt_succ,ite_true]
      | there a =>
        rw [component_there,← (side P o).assoc,← (sideD P o).snd_nat,
          (side P o).assoc,ExchangeScript.component]
        rw [← component_there]
        apply congrArg (component o)
        apply At.index_injective
        simp only [tailExchange,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
          At.index_cast,swapBlocks_index,List.length_cons,At.index]
        unfold exchangeIndex
        split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
    rw [he,ih]
    rfl

theorem tailExchange_split (o : Op) (F U V : List (NormalForm P)) :
    (side P o).comp ((tailExchange F U V).arrow o)
      ((side P o).comp (split o F (U ++ V))
        ((sideM P o).tensor ((side P o).id (fold o F)) (split o U V))) =
      (side P o).comp (split o F (V ++ U))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o F)) (split o V U))
          ((sideM P o).tensor ((side P o).id (fold o F))
            ((sideM P o).swap (fold o V) (fold o U)))) := by
  let C := side P o
  let M := sideM P o
  rw [tailExchange_arrow,← C.assoc,prefixSide_split,C.assoc,M.tensor_comp,C.id_comp,
    BinaryMix.swapWhole_split]
  rw [M.tensor_comp,C.id_comp]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
