module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {Γ Θ Ξ Δ Λ Ω : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: B :: Δ)) (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    ofTerm (G.cut (G.disjR Γ [] Δ A B f) (G.disjL g h)).denote =
      ofTerm (PrincipalDisjunction.reduction f g h).denote :=
  PrincipalDisjunction.rule_equation f g h

example {P : Type u} {Γ Θ Ξ F U Λ Ω : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    ofTerm (PositionalCut.cut (G.disjR Γ F U A B f) (At.shift F (.here (.disj A B) U))
      (G.disjL g h) (.here (.disj A B) (Θ ++ Ξ))).denote =
      ofTerm (PrincipalDisjunction.selectedReduction f g h).denote :=
  PrincipalDisjunction.selected_equation f g h

example {P : Type u} {Γ Θ Ξ F U Λ Ω : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    (PrincipalDisjunction.selectedReduction f g h).cutCount =
      f.cutCount + g.cutCount + h.cutCount + 2 ∧
    ((PrincipalDisjunction.selectedReduction f g h).Atomized ↔
      f.Atomized ∧ g.Atomized ∧ h.Atomized) :=
  ⟨PrincipalDisjunction.selectedReduction_count f g h,
    PrincipalDisjunction.selectedReduction_atomized f g h⟩

example {P : Type u} {Γ Θ Ξ F U Λ Ω : List (NormalForm P)} {A B : NormalForm P}
    (ih : DegreeBelow P (cutDegree (.disj A B)))
    (f : G P Γ (F ++ A :: B :: U)) (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω)
    (hf : f.CutFree) (hg : g.CutFree) (hh : h.CutFree) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (At.shift F (.here (.disj A B) U))
      (G.disjL g h) (.here (.disj A B) (Θ ++ Ξ)) :=
  PrincipalDisjunction.degree_step ih f g h hf hg hh

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (ih : DegreeBelow P (cutDegree C))
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) (af : f.Atomized) (ag : g.Atomized)
    (hr : PositionalCut.rank f x g y = 2) : PositionalCut.Eliminated f x g y :=
  PositionalCut.rank_two_degree_step ih f x g y hf hg af ag hr

example {P : Type u} (o : Op) (F U : List (NormalForm P)) (A : NormalForm P) :
    (HeadRouting.front F U A).arrow o =
      (side P o).comp ((sideM P o).tensor ((side P o).id A) (split o F U))
        ((side P o).comp ((sideM P o).cross A (fold o F) (fold o U)) (join o F (A :: U))) :=
  HeadRouting.front_arrow o F U A

example {P : Type u} (A : NormalForm P) (U : List (NormalForm P)) :
    ((HeadRouting.front [A] U A).get (.here A (A :: U))).index = 1 ∧
    ((HeadRouting.front [A] U A).get (.there (.here A U))).index = 0 := by
  constructor
  · have h := HeadRouting.front_before U A (At.here A [])
    exact congrArg At.index h
  · have h := HeadRouting.front_head [A] U A
    exact congrArg At.index h

example : cutDegree (.top : NormalForm Empty) = 1 ∧ cutDegree (.bot : NormalForm Empty) = 1 := ⟨rfl,rfl⟩
example : mirror (.conj .top .bot : NormalForm Empty) = .disj .top .bot := rfl

#check PrincipalConjunction.degree_step
#check PrincipalDisjunction.equation
#check PrincipalDisjunction.component_degrees
#print axioms PrincipalDisjunction.rule_equation
#print axioms PrincipalDisjunction.selected_equation
#print axioms PrincipalConjunction.degree_step
#print axioms PrincipalDisjunction.degree_step
#print axioms PositionalCut.rank_two_degree_step
