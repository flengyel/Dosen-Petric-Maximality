module

public import DosenPetric.GentzenDisjSecondCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

def disjSecondNative {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (k : G P (T ++ (B :: Θ)) (J ++ E)) :
    G P (T ++ (.disj A B :: (Γ ++ Θ))) (J ++ (Δ ++ E)) :=
  (BinaryMix.swapBlocks Δ J E).right
    ((HeadRouting.front T (Γ ++ Θ) (.disj A B)).inverse.left
      (((BinaryMix.swapBlocks Γ T Θ).consFixed (.disj A B)).left
        (G.disjL f ((HeadRouting.front T Θ B).left k))))

def disjSecondInput (Q : NormalForm P) (T Γ Θ : List (NormalForm P)) :
    Hom (ante (T ++ (Q :: (Γ ++ Θ)))) (.conj Q (.conj (ante Γ) (.conj (ante T) (ante Θ)))) :=
  comp (ofTerm (append .conj T (Q :: (Γ ++ Θ))).invTerm)
    (comp (tensor .conj (id (ante T)) (tensor .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm)))
      (secondDisjInput (ante T) (ante Γ) (ante Θ) Q))

theorem disj_second_input (Q : NormalForm P) (T Γ Θ : List (NormalForm P)) :
    comp ((HeadRouting.front T (Γ ++ Θ) Q).inverse.arrow .conj)
      (comp (((BinaryMix.swapBlocks Γ T Θ).consFixed Q).arrow .conj)
        (comp (tensor .conj (id Q) (ofTerm (append .conj Γ (T ++ Θ)).invTerm))
          (tensor .conj (id Q) (tensor .conj (id (ante Γ)) (ofTerm (append .conj T Θ).invTerm))))) =
      disjSecondInput Q T Γ Θ := by
  have hs := BinaryMix.swapBlocks_split .conj Γ T Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at hs
  rw [ExchangeScript.consFixed_arrow]
  dsimp only [side,sideM,conjMonoidal,category]
  rw [Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,hs]
  rw [tensor_factor .conj (id Q),tensor_factor .conj (id Q)]
  rw [← Laws.assoc ((HeadRouting.front T (Γ ++ Θ) Q).inverse.arrow .conj),conj_front_inverse_split]
  have hn := (sideM P .conj).cross_nat (id (ante T)) (id Q) (ofTerm (append .conj Γ Θ).invTerm)
  dsimp only [side,sideM,conjMonoidal,category] at hn
  simp only [Laws.assoc]
  erw [← Laws.assoc ((sideM P .conj).cross (ante T) Q (ante (Γ ++ Θ))),hn]
  simp only [disjSecondInput,secondDisjInput,Laws.assoc]
  rfl

theorem disj_second_output (J D E : List (NormalForm P)) :
    comp (tensor .disj (id (succ D)) (ofTerm (append .disj J E).toTerm))
      (comp (ofTerm (append .disj D (J ++ E)).toTerm) ((BinaryMix.swapBlocks D J E).arrow .disj)) =
      comp ((sideM P .disj).cross (succ J) (succ D) (succ E)) (disjFirstOutput J D E) := by
  have he := BinaryMix.swapBlocks_split .disj D J E
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at he ⊢
  simpa only [disjFirstOutput,Laws.assoc] using he

end DisjLogical
end DosenPetric.Reduced.Gentzen
