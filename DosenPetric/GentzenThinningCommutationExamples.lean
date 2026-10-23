module

public import DosenPetric.GentzenThinningCommutationRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1
universe u
variable {P : Type u}

/-- Three selected copies; the equal formula in the middle gap is fixed. -/
theorem three_copy_lossL (C D : NormalForm P) (Δ Λ : List (NormalForm P))
    (f : G P [C,C,C,C] (Δ ++ Λ)) :
    G.contractionRankL C [[],[C],[]] [] (Δ ++ D :: Λ) (by change 2 ≤ 3; omega)
        (G.thinR _ Δ Λ D f) =
      G.contractionRankL C [[],[C],[]] [] (Δ ++ Λ) (by change 2 ≤ 3; omega) f + 3 :=
  contraction_lossL C D [[],[C],[]] [] Δ Λ (by change 2 ≤ 3; omega) f

theorem three_copy_lossR (C D : NormalForm P) (Γ Θ : List (NormalForm P))
    (f : G P (Γ ++ Θ) [C,C,C,C]) :
    G.contractionRankR (Γ ++ D :: Θ) C [[],[C],[]] [] (by change 2 ≤ 3; omega)
        (G.thinL Γ Θ _ D f) =
      G.contractionRankR (Γ ++ Θ) C [[],[C],[]] [] (by change 2 ≤ 3; omega) f + 3 :=
  contraction_lossR C D [[],[C],[]] Γ Θ [] (by change 2 ≤ 3; omega) f

theorem three_copy_endpoint_lossL (C D : NormalForm P) (Δ Λ : List (NormalForm P))
    (f : G P [C,C,C,C] (Δ ++ Λ)) :
    (oldL C D [[],[C],[]] [] Δ Λ (by change 2 ≤ 3; omega) f).rho .left (At.there (.here C [])) =
      (newL C D [[],[C],[]] [] Δ Λ (by change 2 ≤ 3; omega) f).rho .left (At.there (.here C [])) + 2 := by
  have h := endpoint_lossL C D [[],[C],[]] [] Δ Λ (by change 2 ≤ 3; omega) f
  have hp : At.shift (gaps [[],[C],[]]) (.here C []) = At.there (.here C []) := by
    apply At.index_injective
    rfl
  rw [hp] at h
  change _ + 1 = _ + 3 at h
  omega

theorem three_copy_endpoint_lossR (C D : NormalForm P) (Γ Θ : List (NormalForm P))
    (f : G P (Γ ++ Θ) [C,C,C,C]) :
    (oldR C D [[],[C],[]] Γ Θ [] (by change 2 ≤ 3; omega) f).rho .right (At.there (.here C [])) =
      (newR C D [[],[C],[]] Γ Θ [] (by change 2 ≤ 3; omega) f).rho .right (At.there (.here C [])) + 2 := by
  have h := endpoint_lossR C D [[],[C],[]] Γ Θ [] (by change 2 ≤ 3; omega) f
  have hp : At.shift (gaps [[],[C],[]]) (.here C []) = At.there (.here C []) := by
    apply At.index_injective
    rfl
  rw [hp] at h
  change _ + 1 = _ + 3 at h
  omega

/-- Empty P still supports genuine constant proof trees. -/
def constantPremiseL : G Empty [.top,.top] [.top] :=
  G.thinL [] [.top] [.top] .top (G.thinL [] [] [.top] .top G.topI)

def constantPremiseR : G Empty [.bot] [.bot,.bot] :=
  G.thinR [.bot] [] [.bot] .bot (G.thinR [.bot] [] [] .bot G.botE)

theorem emptyP_constantsL :
    ofTerm (newL .top .top [[],[]] [] [] [.top] (by change 2 ≤ 2; omega) constantPremiseL).denote =
      ofTerm (oldL .top .top [[],[]] [] [] [.top] (by change 2 ≤ 2; omega) constantPremiseL).denote ∧
    (newL .top .top [[],[]] [] [] [.top] (by change 2 ≤ 2; omega) constantPremiseL).rho .left (.here .top []) <
      (oldL .top .top [[],[]] [] [] [.top] (by change 2 ≤ 2; omega) constantPremiseL).rho .left (.here .top []) ∧
    (newL .top .top [[],[]] [] [] [.top] (by change 2 ≤ 2; omega) constantPremiseL).Atomized :=
  ⟨denoteL ..,endpoint_decreasesL ..,newL_atomized _ _ _ _ _ _ _ _ True.intro ⟨True.intro,⟨True.intro,True.intro⟩⟩⟩

theorem emptyP_constantsR :
    ofTerm (newR .bot .bot [[],[]] [.bot] [] [] (by change 2 ≤ 2; omega) constantPremiseR).denote =
      ofTerm (oldR .bot .bot [[],[]] [.bot] [] [] (by change 2 ≤ 2; omega) constantPremiseR).denote ∧
    (newR .bot .bot [[],[]] [.bot] [] [] (by change 2 ≤ 2; omega) constantPremiseR).rho .right (.here .bot []) <
      (oldR .bot .bot [[],[]] [.bot] [] [] (by change 2 ≤ 2; omega) constantPremiseR).rho .right (.here .bot []) ∧
    (newR .bot .bot [[],[]] [.bot] [] [] (by change 2 ≤ 2; omega) constantPremiseR).Atomized :=
  ⟨denoteR ..,endpoint_decreasesR ..,newR_atomized _ _ _ _ _ _ _ _ True.intro ⟨True.intro,⟨True.intro,True.intro⟩⟩⟩

/-- A real cut is retained, rather than hidden by a CutFree hypothesis. -/
def cutPremiseL (l : Literal P) : G P [.lit l,.lit l] [.lit l] :=
  G.thinL [] [.lit l] [.lit l] (.lit l) (G.cut (G.identity l) (G.identity l))

def cutPremiseR (l : Literal P) : G P [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [] [.lit l] (.lit l) (G.cut (G.identity l) (G.identity l))

theorem with_cutL (l : Literal P) :
    ofTerm (newL (.lit l) (.lit l) [[],[]] [] [] [.lit l] (by change 2 ≤ 2; omega) (cutPremiseL l)).denote =
      ofTerm (oldL (.lit l) (.lit l) [[],[]] [] [] [.lit l] (by change 2 ≤ 2; omega) (cutPremiseL l)).denote ∧
    (newL (.lit l) (.lit l) [[],[]] [] [] [.lit l] (by change 2 ≤ 2; omega) (cutPremiseL l)).rho .left (.here (.lit l) []) <
      (oldL (.lit l) (.lit l) [[],[]] [] [] [.lit l] (by change 2 ≤ 2; omega) (cutPremiseL l)).rho .left (.here (.lit l) []) ∧
    (newL (.lit l) (.lit l) [[],[]] [] [] [.lit l] (by change 2 ≤ 2; omega) (cutPremiseL l)).cutCount = 1 :=
  ⟨denoteL ..,endpoint_decreasesL ..,rfl⟩

theorem with_cutR (l : Literal P) :
    ofTerm (newR (.lit l) (.lit l) [[],[]] [.lit l] [] [] (by change 2 ≤ 2; omega) (cutPremiseR l)).denote =
      ofTerm (oldR (.lit l) (.lit l) [[],[]] [.lit l] [] [] (by change 2 ≤ 2; omega) (cutPremiseR l)).denote ∧
    (newR (.lit l) (.lit l) [[],[]] [.lit l] [] [] (by change 2 ≤ 2; omega) (cutPremiseR l)).rho .right (.here (.lit l) []) <
      (oldR (.lit l) (.lit l) [[],[]] [.lit l] [] [] (by change 2 ≤ 2; omega) (cutPremiseR l)).rho .right (.here (.lit l) []) ∧
    (newR (.lit l) (.lit l) [[],[]] [.lit l] [] [] (by change 2 ≤ 2; omega) (cutPremiseR l)).cutCount = 1 :=
  ⟨denoteR ..,endpoint_decreasesR ..,rfl⟩

theorem both_signs_with_cut (p : P) :
    (newL (.lit (.pos p)) (.lit (.pos p)) [[],[]] [] [] [.lit (.pos p)]
      (by change 2 ≤ 2; omega) (cutPremiseL (.pos p))).cutCount = 1 ∧
    (newR (.lit (.neg p)) (.lit (.neg p)) [[],[]] [.lit (.neg p)] [] []
      (by change 2 ≤ 2; omega) (cutPremiseR (.neg p))).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1
