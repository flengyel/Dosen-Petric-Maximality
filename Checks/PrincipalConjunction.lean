module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {Γ Θ Δ Λ Ξ Ω : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P (A :: B :: Ξ) Ω) :
    ofTerm (G.cut (G.conjR f g) (G.conjL [] Ξ Ω A B h)).denote =
      ofTerm (PrincipalConjunction.reduction f g h).denote :=
  PrincipalConjunction.rule_equation f g h

example {P : Type u} {Γ Θ Δ Λ F U V : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P (F ++ A :: B :: U) V) :
    ofTerm (PositionalCut.cut (G.conjR f g) (.here (.conj A B) (Δ ++ Λ))
      (G.conjL F U V A B h) (At.shift F (.here (.conj A B) U))).denote =
      ofTerm (PrincipalConjunction.selectedReduction f g h).denote :=
  PrincipalConjunction.selected_equation f g h

example {P : Type u} {Γ Θ Δ Λ F U V : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P (F ++ A :: B :: U) V) :
    (PrincipalConjunction.selectedReduction f g h).cutCount =
      f.cutCount + g.cutCount + h.cutCount + 2 ∧
    ((PrincipalConjunction.selectedReduction f g h).Atomized ↔
      f.Atomized ∧ g.Atomized ∧ h.Atomized) :=
  ⟨PrincipalConjunction.selectedReduction_count f g h,
    PrincipalConjunction.selectedReduction_atomized f g h⟩

example {P : Type u} (o : Op) (F U : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp ((At.shift F (.here (o.formula A B) U)).toHead.arrow o)
      (logicalSide o F U A B) =
    (side P o).comp (logicalSide o [] (At.shift F (.here (o.formula A B) U)).erase A B)
      ((LogicalHeadRouting.components F U A B (o.formula A B)).arrow o) :=
  LogicalHeadRouting.square o F U A B

example {P : Type u} (F U : List (NormalForm P)) (A : NormalForm P) :
    ((LogicalHeadRouting.components F U A A (.conj A A)).get
      (At.shift F (.here A (A :: U)))).index = 0 ∧
    ((LogicalHeadRouting.components F U A A (.conj A A)).get
      (At.shift F (.there (.here A U)))).index = 1 := by
  rw [LogicalHeadRouting.first, LogicalHeadRouting.second]
  exact ⟨rfl,rfl⟩

#check cutDegree_conj_left
#check cutDegree_conj_right
#check PrincipalConjunction.equation
#check G.conjL_toHead
#check G.disjR_toHead
#check split_assoc
#print axioms PrincipalConjunction.rule_equation
#print axioms PrincipalConjunction.selected_equation
#print axioms LogicalHeadRouting.square
