module

public import DosenPetric.GentzenFirstBlockExchange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

def conjLeftSecondNative {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (T ++ Θ) (J ++ (B :: E))) :
    G P (T ++ (Γ ++ Θ)) (J ++ (.conj A B :: (Δ ++ E))) :=
  (HeadRouting.front J (Δ ++ E) (.conj A B)).inverse.right
    (((BinaryMix.swapBlocks Δ J E).consFixed (.conj A B)).right
      ((BinaryMix.swapBlocks Γ T Θ).left
        (G.conjR f ((HeadRouting.front J E B).right k))))

def leftSecondInput (T Γ Θ : List (NormalForm P)) :
    Hom (ante (T ++ (Γ ++ Θ))) (.conj (ante Γ) (.conj (ante T) (ante Θ))) :=
  comp (ofTerm (append .conj T (Γ ++ Θ)).invTerm)
    (comp (tensor .conj (id (ante T)) (ofTerm (append .conj Γ Θ).invTerm))
      ((sideM P .conj).cross (ante T) (ante Γ) (ante Θ)))

theorem left_second_input (T Γ Θ : List (NormalForm P)) :
    comp ((BinaryMix.swapBlocks Γ T Θ).arrow .conj)
      (comp (ofTerm (append .conj Γ (T ++ Θ)).invTerm)
        (tensor .conj (id (ante Γ)) (ofTerm (append .conj T Θ).invTerm))) =
      leftSecondInput T Γ Θ := by
  have he := BinaryMix.swapBlocks_split .conj Γ T Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at he
  exact he

theorem left_second_output (Q : NormalForm P) (J D E : List (NormalForm P)) :
    comp (tensor .disj (id Q) (tensor .disj (id (succ D)) (ofTerm (append .disj J E).toTerm)))
      (comp (tensor .disj (id Q) (ofTerm (append .disj D (J ++ E)).toTerm))
        (comp (((BinaryMix.swapBlocks D J E).consFixed Q).arrow .disj)
          ((HeadRouting.front J (D ++ E) Q).inverse.arrow .disj))) =
      comp (tensor .disj (id Q) ((sideM P .disj).cross (succ J) (succ D) (succ E)))
        (comp ((sideM P .disj).cross (succ J) Q (.disj (succ D) (succ E)))
          (leftFirstOutput Q J D E)) := by
  rw [ExchangeScript.consFixed_arrow]
  dsimp only [sideM,side,disjMonoidal,opposite,category]
  have hs := BinaryMix.swapBlocks_split .disj D J E
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs
  have ht : comp (tensor .disj (id (succ D)) (ofTerm (append .disj J E).toTerm))
      (comp (ofTerm (append .disj D (J ++ E)).toTerm) ((BinaryMix.swapBlocks D J E).arrow .disj)) =
      comp ((sideM P .disj).cross (succ J) (succ D) (succ E))
        (comp (tensor .disj (id (succ J)) (ofTerm (append .disj D E).toTerm))
          (ofTerm (append .disj J (D ++ E)).toTerm)) := by
    dsimp only [sideM,side,disjMonoidal,opposite,category]
    simpa only [Laws.assoc] using hs
  rw [← Laws.assoc (tensor .disj (id Q) (ofTerm (append .disj D (J ++ E)).toTerm)),
    Laws.tensor_comp,Laws.id_comp]
  rw [← Laws.assoc (tensor .disj (id Q) (tensor .disj (id (succ D)) (ofTerm (append .disj J E).toTerm))),
    Laws.tensor_comp,Laws.id_comp,ht]
  rw [tensor_factor .disj (id Q),tensor_factor .disj (id Q)]
  simp only [Laws.assoc]
  rw [front_inverse_split]
  erw [← Laws.assoc (tensor .disj (id Q) (tensor .disj (id (succ J)) (ofTerm (append .disj D E).toTerm))),
    disj_cross_nat]
  simp only [leftFirstOutput,Laws.assoc]
  rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
