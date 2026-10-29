module

public import DosenPetric.GentzenConjSecondDeletion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem second_input_route (T X Y : NormalForm P) :
    comp ((sideM P .conj).cross T X Y) (swap .conj X (.conj T Y)) =
      comp (tensor .conj (id T) (swap .conj X Y)) (assocR .conj T Y X) := by
  simp only [MonoidalData.cross,sideM,side,conjMonoidal,category,
    ProductCalculation.assocR_pair,ProductCalculation.assocL_pair,
    ProductCalculation.swap_pair,ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]

theorem conjR_left_second_core {A D B C E X Y T Z : NormalForm P}
    (f : Hom X (.disj A D)) (g : Hom Y (.disj B (.disj C E))) (h : Hom (.conj C T) Z) :
    splice (comp (tensor .conj f g) (selectedMixedSecond A D B C E)) h =
      comp ((sideM P .conj).cross T X Y)
        (comp (tensor .conj f
          (comp (splice (comp g ((sideM P .disj).cross C B E)) h)
            ((sideM P .disj).cross B Z E)))
          (selectedMixedSecond A D B Z E)) := by
  have hf : comp (tensor .conj f g) (selectedMixedSecond A D B C E) =
      comp (swap .conj X Y)
        (comp (comp (tensor .conj g f) (selectedMixed B C E A D))
          (tensor .disj (id C) (tensor .disj (swap .conj B A) (swap .disj E D)))) := by
    rw [selectedMixedSecond_swap]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj f g),← Laws.swap_nat]
    simp only [Laws.assoc]
  rw [hf,Splice.input,Splice.residual,conjR_left_first_core,selectedMixedSecond_swap]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj f
    (comp (splice (comp g ((sideM P .disj).cross C B E)) h) ((sideM P .disj).cross B Z E))),
    ← Laws.swap_nat]
  simp only [Laws.assoc]
  erw [← Laws.assoc ((sideM P .conj).cross T X Y),second_input_route]
  simp only [Laws.assoc]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
