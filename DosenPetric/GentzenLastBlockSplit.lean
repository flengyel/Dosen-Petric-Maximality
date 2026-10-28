module

public import DosenPetric.GentzenLastBlockExchange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

def lastExchange (F U V : List (NormalForm P)) :
    ExchangeScript P ((F ++ V) ++ U) ((F ++ U) ++ V) :=
  (ExchangeScript.exchange F U V []).reindex
    (by rw [List.append_nil]) (by rw [List.append_nil])

theorem lastExchange_decompose (o : Op) (F U V : List (NormalForm P)) :
    (lastExchange F U V).arrow o =
      ((ExchangeScript.appendAssoc F V U).inverse.seq
        ((tailExchange F U V).seq (ExchangeScript.appendAssoc F U V))).arrow o := by
  apply side_ext o
  intro E a
  rw [ExchangeScript.component,ExchangeScript.component]
  apply congrArg (component o)
  apply At.index_injective
  simp only [lastExchange,tailExchange,ExchangeScript.appendAssoc,ExchangeScript.inverse,
    ExchangeScript.get,ExchangeScript.rewire,Rewire.get,At.index_cast,swapBlocks_index]

theorem lastExchange_split (o : Op) (F U V : List (NormalForm P)) :
    (side P o).comp ((lastExchange F U V).arrow o)
      ((side P o).comp (split o (F ++ U) V)
        ((sideM P o).tensor (split o F U) ((side P o).id (fold o V)))) =
      (side P o).comp (split o (F ++ V) U)
        ((side P o).comp ((sideM P o).tensor (split o F V) ((side P o).id (fold o U)))
          ((side P o).comp ((sideM P o).assocL (fold o F) (fold o V) (fold o U))
            ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o F))
              ((sideM P o).swap (fold o V) (fold o U)))
              ((sideM P o).assocR (fold o F) (fold o U) (fold o V))))) := by
  let C := side P o
  let M := sideM P o
  rw [lastExchange_decompose]
  change C.comp (C.comp ((ExchangeScript.appendAssoc F V U).inverse.arrow o)
    (C.comp ((tailExchange F U V).arrow o) ((ExchangeScript.appendAssoc F U V).arrow o))) _ = _
  rw [C.assoc,C.assoc,split_assoc]
  have ht := congrArg (fun k => C.comp k (M.assocR (fold o F) (fold o U) (fold o V)))
    (tailExchange_split o F U V)
  dsimp only [C,M] at ht
  simp only [(side P o).assoc] at ht
  erw [ht]
  have he := congrArg (fun k => C.comp k
    (C.comp (M.tensor (C.id (fold o F)) (M.swap (fold o V) (fold o U)))
      (M.assocR (fold o F) (fold o U) (fold o V)))) (split_assoc_inverse o F V U)
  dsimp only [C,M] at he ⊢
  simpa only [(side P o).assoc] using he

end BinaryLogical
end DosenPetric.Reduced.Gentzen
