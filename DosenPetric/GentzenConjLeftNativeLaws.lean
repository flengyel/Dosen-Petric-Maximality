module

public import DosenPetric.GentzenConjLeftRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjLeftFirstNative_count {Γ Θ D Λ T J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (T ++ Γ) (J ++ (A :: D))) (g : G P Θ (B :: Λ)) :
    (conjLeftFirstNative k g).cutCount = k.cutCount + g.cutCount := by
  simp only [conjLeftFirstNative,ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem conjLeftFirstNative_atomized {Γ Θ D Λ T J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (T ++ Γ) (J ++ (A :: D))) (g : G P Θ (B :: Λ)) :
    (conjLeftFirstNative k g).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [conjLeftFirstNative,ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem conjLeftFirstNative_congr {Γ Θ D Λ T J : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P (T ++ Γ) (J ++ (A :: D))) (g : G P Θ (B :: Λ))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjLeftFirstNative k g).denote = ofTerm (conjLeftFirstNative k' g).denote := by
  have ha : ofTerm ((HeadRouting.front J D A).right k).denote =
      ofTerm ((HeadRouting.front J D A).right k').denote := by
    rw [ExchangeScript.right_denote,ExchangeScript.right_denote,hk]
  unfold conjLeftFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp (comp _ (ofTerm (Rules.conjRight _ g.denote))) _) _ = _
  rw [Rules.conjRight_congr ha rfl]
  rfl

theorem leftFirstChild_factor {Γ Δ I J : List (NormalForm P)} {A C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut f a.there h z).denote =
      ofTerm (G.cut ((HeadRouting.front [A] a.erase C).right ((a.toHead.consFixed A).right f))
        (z.toHead.left h)).denote := by
  apply Rules.cut_congr _ rfl
  rw [ExchangeScript.right_denote,toHead_there_arrow,ExchangeScript.right_denote,ExchangeScript.right_denote]
  simp only [ExchangeScript.arrow,ExchangeScript.rewire,Rewire.arrow]
  exact (Laws.assoc ..).symm

theorem headBefore_residual_conjR {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Δ C) (g : G P Θ (B :: Λ)) :
    ofTerm (((LogicalDeletion.headBefore a Λ).consFixed (.conj A B)).right (G.conjR f g)).denote =
      ofTerm (G.conjR ((a.toHead.consFixed A).right f) g).denote := by
  rw [ExchangeScript.right_denote,ExchangeScript.consFixed_arrow,BinaryMix.headBefore_structural]
  have he := residual_first_conjR a.toHead.structural f g
  rw [StructuralProgram.right_denote,structural_consFixed_arrow] at he
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he
  change comp (ofTerm (G.conjR f g).denote)
    (tensor .disj (id (.conj A B)) ((a.toHead.structural.suffixFixed Λ).arrow .disj)) = _
  rw [he]
  have ha : ofTerm ((a.toHead.structural.consFixed A).right f).denote =
      ofTerm ((a.toHead.consFixed A).right f).denote := by
    rw [StructuralProgram.right_denote,ExchangeScript.right_denote,structural_consFixed_arrow,
      ExchangeScript.consFixed_arrow,ExchangeScript.structural_arrow]
  exact Rules.conjRight_congr ha rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
