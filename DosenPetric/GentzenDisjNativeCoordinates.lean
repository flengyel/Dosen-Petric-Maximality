module

public import DosenPetric.GentzenDisjReflectedCore

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
theorem first_sum_route (A B E : O) :
    C.comp (M.swap A (M.obj B E))
      (C.comp (M.assocL B E A)
        (C.comp (M.tensor (C.id B) (M.swap E A))
          (C.comp (M.assocR B A E) (M.tensor (M.swap B A) (C.id E))))) =
      M.assocR A B E := by
  simp only [D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,
    D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id]

end DiagonalData
namespace Reduced.Gentzen.DisjLogical
variable {P : Type u}

theorem first_sum_route (C D E : NormalForm P) :
    comp (tensor .disj (swap .disj C D) (id E))
      (comp (BinaryLogical.exchangeCore .disj D C E) (swap .disj (.disj D E) C)) =
      assocL .disj C D E := by
  have he := (disjDiagonal P).first_sum_route (rightIn_assocL .disj) (side_swap_snd .disj) C D E
  dsimp only [disjMonoidal,opposite,category,BinaryLogical.exchangeCore] at he ⊢
  simpa only [Laws.assoc] using he

theorem first_child_route (T X A : NormalForm P) :
    comp (assocL .conj T X A) (tensor .conj (id T) (swap .conj X A)) =
      comp (swap .conj (.conj T X) A) ((sideM P .conj).cross A T X) := by
  simp only [MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

def firstReflectedInput (T X Y Q : NormalForm P) :
    Hom (.conj (.conj (.conj T X) Y) Q) (.conj T (.conj Q (.conj X Y))) :=
  comp (tensor .conj (assocL .conj T X Y) (id Q))
    (comp (assocL .conj T (.conj X Y) Q) (tensor .conj (id T) (swap .conj (.conj X Y) Q)))

def firstDisjInput (T X Y Q : NormalForm P) :
    Hom (.conj T (.conj Q (.conj X Y))) (.conj Q (.conj (.conj T X) Y)) :=
  comp ((sideM P .conj).cross T Q (.conj X Y)) (tensor .conj (id Q) (assocR .conj T X Y))

theorem first_input_route (T X Y Q : NormalForm P) :
    comp (firstReflectedInput T X Y Q) (firstDisjInput T X Y Q) =
      swap .conj (.conj (.conj T X) Y) Q := by
  simp only [firstReflectedInput,firstDisjInput,MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id,Laws.assoc]
  simp only [← Laws.assoc]
  have eta {V A B : NormalForm P} (f : Hom V (.conj A B)) :
      pair (comp f (fst A B)) (comp f (snd A B)) = f := (conjDiagonal P).pair_eta f
  rw [eta (comp (fst (.conj (.conj T X) Y) Q) (fst (.conj T X) Y)),
    eta (fst (.conj (.conj T X) Y) Q)]


end Reduced.Gentzen.DisjLogical
end DosenPetric
