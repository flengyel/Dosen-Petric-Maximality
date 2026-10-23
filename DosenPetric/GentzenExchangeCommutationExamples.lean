module

public import DosenPetric.GentzenExchangeCommutationRank
public import DosenPetric.GentzenThinningCommutationExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.Exchange
universe u
variable {P : Type u}

/-- Even two empty blocks leave the explicit exchange node in the cluster. -/
theorem empty_exchangeR_rank {Γ Δ : List (NormalForm P)} (f : G P Γ Δ)
    {C : NormalForm P} (x : At Γ C) :
    (G.exchangeR Γ [] [] [] Δ f).rho .left x = 1 + f.rho .left x :=
  G.rho_exchangeR_left Γ [] [] [] Δ f x

theorem empty_exchangeL_rank {Γ Δ : List (NormalForm P)} (f : G P Γ Δ)
    {C : NormalForm P} (x : At Δ C) :
    (G.exchangeL [] [] [] Γ Δ f).rho .right x = 1 + f.rho .right x :=
  G.rho_exchangeL_right [] [] [] Γ Δ f x

theorem one_empty_blockL (C : NormalForm P) (Y Λ : List (NormalForm P))
    (f : G P [C,C] (Y ++ Λ)) :
    ofTerm (newL C [[],[]] [] [] [] Y Λ (by change 2 ≤ 2; omega) f).denote =
      ofTerm (oldL C [[],[]] [] [] [] Y Λ (by change 2 ≤ 2; omega) f).denote := denoteL ..

theorem one_empty_blockR (C : NormalForm P) (X Θ : List (NormalForm P))
    (f : G P (X ++ [] ++ Θ) [C,C]) :
    ofTerm (newR C [[],[]] [] X [] Θ [] (by change 2 ≤ 2; omega) f).denote =
      ofTerm (oldR C [[],[]] [] X [] Θ [] (by change 2 ≤ 2; omega) f).denote := denoteR ..

/-- Actual inhabited constant types with empty variable type and empty blocks. -/
theorem emptyP_constantsL :
    ofTerm (newL .top [[],[]] [] [] [] [] [.top] (by change 2 ≤ 2; omega) W1.constantPremiseL).denote =
      ofTerm (oldL .top [[],[]] [] [] [] [] [.top] (by change 2 ≤ 2; omega) W1.constantPremiseL).denote ∧
    (newL .top [[],[]] [] [] [] [] [.top] (by change 2 ≤ 2; omega) W1.constantPremiseL).rho .left (.here .top []) <
      (oldL .top [[],[]] [] [] [] [] [.top] (by change 2 ≤ 2; omega) W1.constantPremiseL).rho .left (.here .top []) :=
  ⟨denoteL ..,endpoint_decreasesL ..⟩

theorem emptyP_constantsR :
    ofTerm (newR .bot [[],[]] [] [] [] [.bot] [] (by change 2 ≤ 2; omega) W1.constantPremiseR).denote =
      ofTerm (oldR .bot [[],[]] [] [] [] [.bot] [] (by change 2 ≤ 2; omega) W1.constantPremiseR).denote ∧
    (newR .bot [[],[]] [] [] [] [.bot] [] (by change 2 ≤ 2; omega) W1.constantPremiseR).rho .right (.here .bot []) <
      (oldR .bot [[],[]] [] [] [] [.bot] [] (by change 2 ≤ 2; omega) W1.constantPremiseR).rho .right (.here .bot []) :=
  ⟨denoteR ..,endpoint_decreasesR ..⟩

/-- Three selected copies and one fixed equal gap formula; the premise has a cut. -/
def repeatedPremiseL (l : Literal P) : G P [.lit l,.lit l,.lit l,.lit l] [.lit l,.lit l,.lit l] :=
  G.thinR _ [] [.lit l,.lit l] (.lit l)
    (G.thinR _ [] [.lit l] (.lit l)
      (G.thinL [] [.lit l,.lit l,.lit l] _ (.lit l)
        (G.thinL [] [.lit l,.lit l] _ (.lit l) (W1.cutPremiseL l))))

def repeatedPremiseR (l : Literal P) : G P [.lit l,.lit l,.lit l] [.lit l,.lit l,.lit l,.lit l] :=
  G.thinL [] [.lit l,.lit l] _ (.lit l)
    (G.thinL [] [.lit l] _ (.lit l)
      (G.thinR _ [] [.lit l,.lit l,.lit l] (.lit l)
        (G.thinR _ [] [.lit l,.lit l] (.lit l) (W1.cutPremiseR l))))

def repeatedOldL (l : Literal P) :=
  oldL (.lit l) [[],[.lit l],[]] [] [] [.lit l,.lit l] [.lit l] []
    (by change 2 ≤ 3; omega) (repeatedPremiseL l)

def repeatedNewL (l : Literal P) :=
  newL (.lit l) [[],[.lit l],[]] [] [] [.lit l,.lit l] [.lit l] []
    (by change 2 ≤ 3; omega) (repeatedPremiseL l)

def repeatedOldR (l : Literal P) :=
  oldR (.lit l) [[],[.lit l],[]] [] [.lit l,.lit l] [.lit l] [] []
    (by change 2 ≤ 3; omega) (repeatedPremiseR l)

def repeatedNewR (l : Literal P) :=
  newR (.lit l) [[],[.lit l],[]] [] [.lit l,.lit l] [.lit l] [] []
    (by change 2 ≤ 3; omega) (repeatedPremiseR l)

theorem repeated_with_cutL (l : Literal P) :
    ofTerm (repeatedNewL l).denote = ofTerm (repeatedOldL l).denote ∧
    (repeatedNewL l).cutCount = 1 ∧ (repeatedNewL l).Atomized ∧
    (repeatedOldL l).rho .left (.there (.here (.lit l) [])) =
      (repeatedNewL l).rho .left (.there (.here (.lit l) [])) + 2 := by
  refine ⟨denoteL ..,rfl,?_,?_⟩
  · change True ∧ True ∧ True ∧ True ∧ True ∧ (True ∧ True)
    exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩
  · have h := endpoint_lossL (.lit l) [[],[.lit l],[]] [] [] [.lit l,.lit l] [.lit l] []
      (by change 2 ≤ 3; omega) (repeatedPremiseL l)
    have hp : At.shift (gaps [[],[.lit l],[]]) (.here (.lit l) []) = .there (.here (.lit l) []) := by
      apply At.index_injective
      rfl
    rw [hp] at h
    change (repeatedOldL l).rho .left _ + 1 = (repeatedNewL l).rho .left _ + 3 at h
    omega

theorem repeated_with_cutR (l : Literal P) :
    ofTerm (repeatedNewR l).denote = ofTerm (repeatedOldR l).denote ∧
    (repeatedNewR l).cutCount = 1 ∧ (repeatedNewR l).Atomized ∧
    (repeatedOldR l).rho .right (.there (.here (.lit l) [])) =
      (repeatedNewR l).rho .right (.there (.here (.lit l) [])) + 2 := by
  refine ⟨denoteR ..,rfl,?_,?_⟩
  · change True ∧ True ∧ True ∧ True ∧ True ∧ (True ∧ True)
    exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩
  · have h := endpoint_lossR (.lit l) [[],[.lit l],[]] [] [.lit l,.lit l] [.lit l] [] []
      (by change 2 ≤ 3; omega) (repeatedPremiseR l)
    have hp : At.shift (gaps [[],[.lit l],[]]) (.here (.lit l) []) = .there (.here (.lit l) []) := by
      apply At.index_injective
      rfl
    rw [hp] at h
    change (repeatedOldR l).rho .right _ + 1 = (repeatedNewR l).rho .right _ + 3 at h
    omega

theorem both_signs (p : P) :
    (repeatedNewL (.pos p)).cutCount = 1 ∧ (repeatedNewR (.neg p)).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.Exchange
