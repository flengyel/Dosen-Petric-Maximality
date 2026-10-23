module

public import DosenPetric.GentzenHeadThinningLaws

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Rules
universe u
variable {P : Type u}

theorem conjRight_congr {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    {f f' : Term P (ante Γ) (succ (A :: Δ))} {g g' : Term P (ante Θ) (succ (B :: Λ))}
    (hf : ofTerm f = ofTerm f') (hg : ofTerm g = ofTerm g') :
    ofTerm (conjRight f g) = ofTerm (conjRight f' g') := by
  simp only [conjRight, ofTerm_comp, ofTerm_tensor]
  rw [hf, hg]

theorem disjLeft_congr {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    {f f' : Term P (ante (A :: Γ)) (succ Δ)} {g g' : Term P (ante (B :: Θ)) (succ Λ)}
    (hf : ofTerm f = ofTerm f') (hg : ofTerm g = ofTerm g') :
    ofTerm (disjLeft f g) = ofTerm (disjLeft f' g') := by
  simp only [disjLeft, ofTerm_comp, ofTerm_tensor]
  rw [hf, hg]

theorem mix_congr {Γ Θ Δ Λ : List (NormalForm P)}
    {f f' : Term P (ante Γ) (succ Δ)} {g g' : Term P (ante Θ) (succ Λ)}
    (hf : ofTerm f = ofTerm f') (hg : ofTerm g = ofTerm g') :
    ofTerm (mix f g) = ofTerm (mix f' g') := by
  simp only [mix, ofTerm_comp, ofTerm_tensor]
  rw [hf, hg]

theorem cut_congr {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    {f f' : Term P (ante Γ) (succ (C :: Δ))} {g g' : Term P (ante (C :: Θ)) (succ Λ)}
    (hf : ofTerm f = ofTerm f') (hg : ofTerm g = ofTerm g') :
    ofTerm (cut f g) = ofTerm (cut f' g') := by
  simp only [cut, ofTerm_comp, ofTerm_tensor]
  rw [hf, hg]

end DosenPetric.Reduced.Gentzen.Rules
