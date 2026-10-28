module

public import DosenPetric.GentzenBinaryMixDiagram

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

def swapBlocks (F U K : List (NormalForm P)) :
    ExchangeScript P (U ++ (F ++ K)) (F ++ (U ++ K)) :=
  (ExchangeScript.exchange [] F U K).reindex
    (by simp only [List.nil_append,List.append_assoc])
    (by simp only [List.nil_append,List.append_assoc])

/-- Rebuild the first native mix child, then exchange the two fixed context blocks. -/
def leftFirst {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    G P (T ++ (Θ ++ Γ)) (J ++ (At.shift Λ a).erase) :=
  ((swapBlocks Λ J a.erase).right
    ((swapBlocks Θ T Γ).left (G.mix k g))).reindex rfl
      (congrArg (fun xs => J ++ xs) (At.erase_shift_at Λ a)).symm

theorem leftFirst_count {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    (leftFirst a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [leftFirst,G.count_reindex,ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem leftFirst_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    (leftFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [leftFirst,G.atomized_reindex,ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem leftFirst_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k k' : G P (T ++ Γ) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (leftFirst a g k).denote = ofTerm (leftFirst a g k').denote := by
  unfold leftFirst
  apply G.reindex_congr
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.mix k.denote g.denote))) _ = _
  rw [Rules.mix_congr hk rfl]
  rfl

end BinaryMix
end DosenPetric.Reduced.Gentzen
