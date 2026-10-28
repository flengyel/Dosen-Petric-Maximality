module

public import DosenPetric.GentzenPrincipalLogicalTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalConjunction
variable {Γ Θ Δ Λ F U V : List (NormalForm P)} {A B : NormalForm P}

/-- The principal reduction with the right selected formula at its original gap. -/
def selectedReduction (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (F ++ A :: B :: U) V) :
    G P ((At.shift F (.here (.conj A B) U)).erase ++ (Γ ++ Θ)) (V ++ (Δ ++ Λ)) :=
  reduction f g ((LogicalHeadRouting.components F U A B (.conj A B)).left h)

theorem selected_equation (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (F ++ A :: B :: U) V) :
    ofTerm (PositionalCut.cut (G.conjR f g) (.here (.conj A B) (Δ ++ Λ))
      (G.conjL F U V A B h) (At.shift F (.here (.conj A B) U))).denote =
      ofTerm (selectedReduction f g h).denote := by
  exact (Rules.cut_congr rfl (G.conjL_toHead F U V A B h)).trans
    (rule_equation f g ((LogicalHeadRouting.components F U A B (.conj A B)).left h))

theorem selectedReduction_count (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (F ++ A :: B :: U) V) :
    (selectedReduction f g h).cutCount = f.cutCount + g.cutCount + h.cutCount + 2 := by
  simp only [selectedReduction, reduction, ExchangeScript.right_count,
    ExchangeScript.left_count, G.cutCount]
  omega

theorem selectedReduction_atomized (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (F ++ A :: B :: U) V) :
    (selectedReduction f g h).Atomized ↔ f.Atomized ∧ g.Atomized ∧ h.Atomized := by
  simp only [selectedReduction, reduction, ExchangeScript.right_atomized,
    ExchangeScript.left_atomized, G.Atomized]
  constructor
  · rintro ⟨hg,hf,hh⟩
    exact ⟨hf,hg,hh⟩
  · rintro ⟨hf,hg,hh⟩
    exact ⟨hg,hf,hh⟩

/-- The two selected subformulas strictly lower the degree, with no rank premise. -/
theorem component_degrees (A B : NormalForm P) :
    cutDegree A < cutDegree (.conj A B) ∧ cutDegree B < cutDegree (.conj A B) :=
  ⟨cutDegree_conj_left A B, cutDegree_conj_right A B⟩

end PrincipalConjunction
end DosenPetric.Reduced.Gentzen
