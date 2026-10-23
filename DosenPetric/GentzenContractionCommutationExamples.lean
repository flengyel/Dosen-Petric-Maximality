module

public import DosenPetric.GentzenContractionCommutationRank
public import DosenPetric.GentzenExchangeCommutationExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.Contraction
universe u
variable {P : Type u}

/-- Independent arities 2 and 3, with an actual cut retained in the premise. -/
def twoThreePremise (l : Literal P) : G P [.lit l,.lit l] [.lit l,.lit l,.lit l] :=
  G.thinR _ [] [.lit l,.lit l] (.lit l)
    (G.thinR _ [] [.lit l] (.lit l) (W1.cutPremiseL l))

def twoThreeL (l : Literal P) :=
  outerL (.lit l) (.lit l) [[],[]] [[],[],[]] [] []
    (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) (twoThreePremise l)

def twoThreeR (l : Literal P) :=
  outerR (.lit l) (.lit l) [[],[]] [[],[],[]] [] []
    (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) (twoThreePremise l)

theorem two_three_effects (l : Literal P) :
    ofTerm (twoThreeR l).denote = ofTerm (twoThreeL l).denote ∧
    (twoThreeL l).rho .left (.here (.lit l) []) =
      (twoThreeR l).rho .left (.here (.lit l) []) + 1 ∧
    (twoThreeR l).rho .right (.here (.lit l) []) =
      (twoThreeL l).rho .right (.here (.lit l) []) + 2 ∧
    endpointSum (.lit l) (.lit l) [[],[]] [[],[],[]] [] [] (twoThreeR l) =
      endpointSum (.lit l) (.lit l) [[],[]] [[],[],[]] [] [] (twoThreeL l) + 1 ∧
    (twoThreeR l).cutCount = 1 := by
  refine ⟨denote ..,?_,?_,?_,rfl⟩
  · have h := left_directed_balance (.lit l) (.lit l) [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) (twoThreePremise l)
    change (twoThreeL l).rho .left (.here (.lit l) []) + 1 =
      (twoThreeR l).rho .left (.here (.lit l) []) + 2 at h
    omega
  · have h := right_directed_balance (.lit l) (.lit l) [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) (twoThreePremise l)
    change (twoThreeR l).rho .right (.here (.lit l) []) + 1 =
      (twoThreeL l).rho .right (.here (.lit l) []) + 3 at h
    omega
  · have h := endpointSum_balance (.lit l) (.lit l) [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) (twoThreePremise l)
    change endpointSum (.lit l) (.lit l) [[],[]] [[],[],[]] [] [] (twoThreeL l) + 3 =
      endpointSum (.lit l) (.lit l) [[],[]] [[],[],[]] [] [] (twoThreeR l) + 2 at h
    omega

/-- Three selected copies plus a fixed equal formula, on both sides. -/
def repeatedPremise (l : Literal P) :
    G P [.lit l,.lit l,.lit l,.lit l] [.lit l,.lit l,.lit l,.lit l] :=
  G.thinR _ [] [.lit l,.lit l,.lit l] (.lit l) (W1.Exchange.repeatedPremiseL l)

def repeatedL (l : Literal P) :=
  outerL (.lit l) (.lit l) [[],[.lit l],[]] [[],[.lit l],[]] [] []
    (by change 2 ≤ 3; omega) (by change 2 ≤ 3; omega) (repeatedPremise l)

def repeatedR (l : Literal P) :=
  outerR (.lit l) (.lit l) [[],[.lit l],[]] [[],[.lit l],[]] [] []
    (by change 2 ≤ 3; omega) (by change 2 ≤ 3; omega) (repeatedPremise l)

theorem repeated_sum_unchanged (l : Literal P) :
    endpointSum (.lit l) (.lit l) [[],[.lit l],[]] [[],[.lit l],[]] [] [] (repeatedL l) =
      endpointSum (.lit l) (.lit l) [[],[.lit l],[]] [[],[.lit l],[]] [] [] (repeatedR l) :=
  endpointSum_eq_of_lengths_eq _ _ _ _ _ _ _ _ _ rfl

theorem repeated_left_decreases_right_increases (l : Literal P) :
    (repeatedR l).rho .left (.there (.here (.lit l) [])) <
      (repeatedL l).rho .left (.there (.here (.lit l) [])) ∧
    (repeatedL l).rho .right (.there (.here (.lit l) [])) <
      (repeatedR l).rho .right (.there (.here (.lit l) [])) := by
  have hp : At.shift (gaps [[],[.lit l],[]]) (.here (.lit l) []) = .there (.here (.lit l) []) := by
    apply At.index_injective
    rfl
  have hL := left_directed_decrease (.lit l) (.lit l) [[],[.lit l],[]] [[],[.lit l],[]] [] []
    (by change 2 ≤ 3; omega) (by change 2 ≤ 3; omega) (repeatedPremise l)
  have hR := right_directed_decrease (.lit l) (.lit l) [[],[.lit l],[]] [[],[.lit l],[]] [] []
    (by change 2 ≤ 3; omega) (by change 2 ≤ 3; omega) (repeatedPremise l)
  rw [hp] at hL hR
  exact ⟨hL,hR⟩

theorem selected_indices (C : NormalForm P) :
    (selectedCopies C [[],[C],[]] []).map At.index = [0,2,3] := rfl

theorem fixed_equal_not_selected (C : NormalForm P) :
    (At.there (.here C [C,C])) ∉ selectedCopies C [[],[C],[]] [] := by
  intro h
  have hi := List.mem_map_of_mem (f := At.index) h
  change 1 ∈ [0,2,3] at hi
  simp at hi

def constantTop : G Empty [.top,.top] [.top,.top,.top] :=
  G.thinR _ [] [.top,.top] .top (G.thinR _ [] [.top] .top W1.constantPremiseL)

def constantBot : G Empty [.bot,.bot] [.bot,.bot,.bot] :=
  G.thinL [] [.bot] _ .bot (G.thinR _ [] [.bot,.bot] .bot W1.constantPremiseR)

theorem emptyP_top :
    ofTerm (outerR .top .top [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) constantTop).denote =
    ofTerm (outerL .top .top [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) constantTop).denote := denote ..

theorem emptyP_bot :
    (outerR .bot .bot [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) constantBot).rho .left (.here .bot []) <
    (outerL .bot .bot [[],[]] [[],[],[]] [] []
      (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) constantBot).rho .left (.here .bot []) :=
  left_directed_decrease ..

theorem both_signs_with_cut (p : P) :
    (twoThreeR (.pos p)).cutCount = 1 ∧ (repeatedR (.neg p)).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.Contraction
