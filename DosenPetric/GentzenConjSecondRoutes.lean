module

public import DosenPetric.GentzenConjSecondEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem residual_second_conjR {F U Γ Θ Δ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ (A :: Δ)) (g : G P Θ (B :: U)) :
    ofTerm (((p.prefixFixed Δ).consFixed (.conj A B)).right (G.conjR f g)).denote =
      ofTerm (G.conjR f ((p.consFixed B).right g)).denote := by
  rw [StructuralProgram.right_denote,G.denote_conjR,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [StructuralProgram.right_denote]
  have hq := structural_consFixed_arrow (p.prefixFixed Δ) (.conj A B) .disj
  have hp := structural_consFixed_arrow p B .disj
  rw [hq,hp]
  have hs := p.prefixFixed_split .disj Δ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs ⊢
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,Laws.id_comp,hs]
  rw [tensor_factor .disj (id (.conj A B))]
  have hm := mixedDisj_nat (id A) (id (succ Δ)) (id B) (p.arrow .disj)
  rw [Laws.tensor_id,Laws.tensor_id] at hm
  erw [← Laws.assoc (ofTerm (Term.mixedDisj A (succ Δ) B (succ U))),hm]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm f.denote) (ofTerm g.denote)),Laws.tensor_comp,Laws.comp_id]

theorem headShift_residual_conjR {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) :
    ofTerm ((LogicalDeletion.headShift (.conj A B :: Δ) a).right (G.conjR f g)).denote =
      ofTerm ((HeadRouting.front (.conj A B :: Δ) a.erase C).right
        (G.conjR (Δ := Δ) (Λ := C :: a.erase) f ((a.toHead.consFixed B).right g))).denote := by
  rw [ExchangeScript.right_denote,BinaryMix.headShift_structural]
  have he := residual_second_conjR a.toHead.structural f g
  rw [StructuralProgram.right_denote] at he
  change comp (ofTerm (G.conjR (Δ := Δ) (Λ := Λ) f g).denote)
    (comp ((a.toHead.structural.prefixFixed (.conj A B :: Δ)).arrow .disj)
      ((HeadRouting.front (.conj A B :: Δ) a.erase C).arrow .disj)) = _
  erw [← Laws.assoc,he,ExchangeScript.right_denote]
  have ha : ofTerm ((a.toHead.structural.consFixed B).right g).denote =
      ofTerm ((a.toHead.consFixed B).right g).denote := by
    rw [StructuralProgram.right_denote,ExchangeScript.right_denote,structural_consFixed_arrow,
      ExchangeScript.consFixed_arrow,ExchangeScript.structural_arrow]
  have hh := Rules.conjRight_congr (f := f.denote) (f' := f.denote) rfl ha
  change comp (ofTerm (Rules.conjRight f.denote (a.toHead.structural.consFixed B |>.right g).denote)) _ = _
  rw [hh]
  rfl

theorem conjLeftSecondNative_count {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (T ++ Θ) (J ++ (B :: E))) :
    (conjLeftSecondNative f k).cutCount = f.cutCount + k.cutCount := by
  simp only [conjLeftSecondNative,ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem conjLeftSecondNative_atomized {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (T ++ Θ) (J ++ (B :: E))) :
    (conjLeftSecondNative f k).Atomized ↔ f.Atomized ∧ k.Atomized := by
  simp only [conjLeftSecondNative,ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem conjLeftSecondNative_congr {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k k' : G P (T ++ Θ) (J ++ (B :: E)))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjLeftSecondNative f k).denote = ofTerm (conjLeftSecondNative f k').denote := by
  have ha : ofTerm ((HeadRouting.front J E B).right k).denote =
      ofTerm ((HeadRouting.front J E B).right k').denote := by
    rw [ExchangeScript.right_denote,ExchangeScript.right_denote,hk]
  unfold conjLeftSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp (comp _ (ofTerm (Rules.conjRight f.denote _))) _) _ = _
  rw [Rules.conjRight_congr rfl ha]
  rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
