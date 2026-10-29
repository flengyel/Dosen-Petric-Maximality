module

public import DosenPetric.GentzenDisjRightFirstCore
public import DosenPetric.GentzenBinaryContractionSplice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.DoubleDisjSplice
universe u
variable {P : Type u}

def firstInput (Q F H X : NormalForm P) :
    Hom (.conj (.conj Q (.conj F H)) X) (.conj Q (.conj (.conj F X) H)) :=
  comp (assocL .conj Q (.conj F H) X)
    (tensor .conj (id Q) (BinaryLogical.exchangeCore .conj F H X))

def secondInput (Q F H X : NormalForm P) :
    Hom (.conj (.conj Q (.conj F H)) X) (.conj Q (.conj F (.conj H X))) :=
  comp (assocL .conj Q (.conj F H) X)
    (tensor .conj (id Q) (assocL .conj F H X))

def twoHead (C F H Q : NormalForm P) :
    Hom (.conj C (.conj C (.conj Q (.conj F H))))
      (.conj Q (.conj (.conj C F) (.conj C H))) :=
  comp (tensor .conj (id C) (DisjLogical.secondDisjInput C F H Q))
    (DisjLogical.firstDisjInput C F (.conj C H) Q)

/-- The second selected copy remains in the untouched second branch after the
    first cut is commuted into the first branch. -/
theorem between_square (C F H Q X : NormalForm P) :
    comp (assocR .conj C (.conj Q (.conj F H)) X)
      (comp (tensor .conj (DisjLogical.secondDisjInput C F H Q) (id X))
        (firstInput Q F (.conj C H) X)) =
      comp (tensor .conj (id C) (firstInput Q F H X))
        (DisjLogical.secondDisjInput C (.conj F X) H Q) := by
  simp only [firstInput,DisjLogical.secondDisjInput,BinaryLogical.exchangeCore,
    MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]

end DosenPetric.Reduced.Gentzen.DoubleDisjSplice
