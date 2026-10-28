module

public import DosenPetric.GentzenPrincipalDisjunctionRule
public import DosenPetric.GentzenPrincipalLogicalTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalDisjunction
variable {Γ Θ Ξ F U Λ Ω : List (NormalForm P)} {A B : NormalForm P}

/-- The native two-component reduction at the original selected disjunction gap. -/
def selectedReduction (f : G P Γ (F ++ A :: B :: U))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    G P ((Θ ++ Ξ) ++ Γ) ((Λ ++ Ω) ++ (At.shift F (.here (.disj A B) U)).erase) :=
  reduction ((LogicalHeadRouting.components F U A B (.disj A B)).right f) g h

theorem selected_equation (f : G P Γ (F ++ A :: B :: U))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    ofTerm (PositionalCut.cut (G.disjR Γ F U A B f) (At.shift F (.here (.disj A B) U))
      (G.disjL g h) (.here (.disj A B) (Θ ++ Ξ))).denote =
      ofTerm (selectedReduction f g h).denote := by
  exact (Rules.cut_congr (G.disjR_toHead Γ F U A B f) rfl).trans
    (rule_equation ((LogicalHeadRouting.components F U A B (.disj A B)).right f) g h)

theorem selectedReduction_count (f : G P Γ (F ++ A :: B :: U))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    (selectedReduction f g h).cutCount = f.cutCount + g.cutCount + h.cutCount + 2 := by
  simp only [selectedReduction, reduction, ExchangeScript.right_count,
    ExchangeScript.left_count, G.cutCount]
  omega

theorem selectedReduction_atomized (f : G P Γ (F ++ A :: B :: U))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    (selectedReduction f g h).Atomized ↔ f.Atomized ∧ g.Atomized ∧ h.Atomized := by
  simp only [selectedReduction, reduction, ExchangeScript.right_atomized,
    ExchangeScript.left_atomized, G.Atomized]
  constructor
  · rintro ⟨⟨hf,hh⟩,hg⟩
    exact ⟨hf,hg,hh⟩
  · rintro ⟨hf,hg,hh⟩
    exact ⟨⟨hf,hh⟩,hg⟩

/-- Both component formulas strictly lower the original disjunction degree. -/
theorem component_degrees (A B : NormalForm P) :
    cutDegree A < cutDegree (.disj A B) ∧ cutDegree B < cutDegree (.disj A B) :=
  ⟨cutDegree_disj_left A B, cutDegree_disj_right A B⟩

end PrincipalDisjunction
end DosenPetric.Reduced.Gentzen
