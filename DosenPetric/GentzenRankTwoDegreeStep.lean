module

public import DosenPetric.GentzenPrincipalDegreeSteps
public import DosenPetric.GentzenRankTwoClassification

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Exhaustive selected rank-two elimination under only the strict outer degree hypothesis. -/
theorem rank_two_degree_step {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (ih : DegreeBelow P (cutDegree C))
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) (af : f.Atomized) (ag : g.Atomized)
    (hr : rank f x g y = 2) : Eliminated f x g y := by
  cases rank_two_classification f x g y hf hg af ag hr with
  | inl h => exact h.2
  | inr h => cases h with
    | conj f g h =>
      have hfg : f.cutCount + g.cutCount = 0 := hf
      have hhh : h.CutFree := hg
      exact PrincipalConjunction.degree_step ih f g h
        (Nat.add_eq_zero_iff.mp hfg).1 (Nat.add_eq_zero_iff.mp hfg).2 hhh
    | disj f g h =>
      have hgh : g.cutCount + h.cutCount = 0 := hg
      have hff : f.CutFree := hf
      exact PrincipalDisjunction.degree_step ih f g h hff
        (Nat.add_eq_zero_iff.mp hgh).1 (Nat.add_eq_zero_iff.mp hgh).2

end PositionalCut
end DosenPetric.Reduced.Gentzen
