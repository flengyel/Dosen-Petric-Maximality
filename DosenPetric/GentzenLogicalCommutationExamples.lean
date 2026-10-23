module

public import DosenPetric.GentzenLogicalCommutationRank
public import DosenPetric.GentzenContractionCommutationExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.Logical
universe u
variable {P : Type u}

/-- A fixed compound in the prefix is introduced logically, not by compound thinning. -/
def contextPremiseL (l : Literal P) :
    G P [.lit l,.lit l,.lit l,.lit l] [.disj (.lit l) (.lit l),.lit l,.lit l,.lit l] :=
  G.disjR _ [] [.lit l,.lit l,.lit l] (.lit l) (.lit l)
    (G.thinR _ [] [.lit l,.lit l,.lit l,.lit l] (.lit l)
      (G.thinR _ [] [.lit l,.lit l,.lit l] (.lit l) (W1.Exchange.repeatedPremiseL l)))

def contextPremiseR (l : Literal P) :
    G P [.conj (.lit l) (.lit l),.lit l,.lit l,.lit l] [.lit l,.lit l,.lit l,.lit l] :=
  G.conjL [] [.lit l,.lit l,.lit l] _ (.lit l) (.lit l)
    (G.thinL [] [.lit l,.lit l,.lit l,.lit l] _ (.lit l)
      (G.thinL [] [.lit l,.lit l,.lit l] _ (.lit l) (W1.Exchange.repeatedPremiseR l)))

def contextOldL (l : Literal P) :=
  oldL (.lit l) (.lit l) (.lit l) [[],[.lit l],[]] []
    [.disj (.lit l) (.lit l)] [.lit l] (by change 2 ≤ 3; omega) (contextPremiseL l)

def contextNewL (l : Literal P) :=
  newL (.lit l) (.lit l) (.lit l) [[],[.lit l],[]] []
    [.disj (.lit l) (.lit l)] [.lit l] (by change 2 ≤ 3; omega) (contextPremiseL l)

def contextOldR (l : Literal P) :=
  oldR (.lit l) (.lit l) (.lit l) [[],[.lit l],[]]
    [.conj (.lit l) (.lit l)] [.lit l] [] (by change 2 ≤ 3; omega) (contextPremiseR l)

def contextNewR (l : Literal P) :=
  newR (.lit l) (.lit l) (.lit l) [[],[.lit l],[]]
    [.conj (.lit l) (.lit l)] [.lit l] [] (by change 2 ≤ 3; omega) (contextPremiseR l)

theorem context_checkedL (l : Literal P) :
    ofTerm (contextNewL l).denote = ofTerm (contextOldL l).denote ∧
    (contextNewL l).cutCount = 1 ∧ (contextNewL l).Atomized ∧
    (contextOldL l).rho .right
      (At.shift [.disj (.lit l) (.lit l)] (.here (.disj (.lit l) (.lit l)) [.lit l])) = 2 ∧
    (contextNewL l).rho .right
      (At.shift [.disj (.lit l) (.lit l)] (.here (.disj (.lit l) (.lit l)) [.lit l])) = 1 := by
  refine ⟨denoteL ..,rfl,?_,oldL_principal_rank ..,newL_principal_rank ..⟩
  change True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ (True ∧ True)
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩

theorem context_checkedR (l : Literal P) :
    ofTerm (contextNewR l).denote = ofTerm (contextOldR l).denote ∧
    (contextNewR l).cutCount = 1 ∧ (contextNewR l).Atomized ∧
    (contextOldR l).rho .left
      (At.shift [.conj (.lit l) (.lit l)] (.here (.conj (.lit l) (.lit l)) [.lit l])) = 2 ∧
    (contextNewR l).rho .left
      (At.shift [.conj (.lit l) (.lit l)] (.here (.conj (.lit l) (.lit l)) [.lit l])) = 1 := by
  refine ⟨denoteR ..,rfl,?_,oldR_principal_rank ..,newR_principal_rank ..⟩
  change True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ (True ∧ True)
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩

theorem context_endpoint_lossL (l : Literal P) :
    (contextOldL l).rho .left (.there (.here (.lit l) [])) =
      (contextNewL l).rho .left (.there (.here (.lit l) [])) + 2 := by
  have h := endpoint_lossL (.lit l) (.lit l) (.lit l) [[],[.lit l],[]] []
    [.disj (.lit l) (.lit l)] [.lit l] (by change 2 ≤ 3; omega) (contextPremiseL l)
  have hp : At.shift (gaps [[],[.lit l],[]]) (.here (.lit l) []) = .there (.here (.lit l) []) := by
    apply At.index_injective
    rfl
  rw [hp] at h
  change (contextOldL l).rho .left _ + 1 = (contextNewL l).rho .left _ + 3 at h
  omega

theorem context_endpoint_lossR (l : Literal P) :
    (contextOldR l).rho .right (.there (.here (.lit l) [])) =
      (contextNewR l).rho .right (.there (.here (.lit l) [])) + 2 := by
  have h := endpoint_lossR (.lit l) (.lit l) (.lit l) [[],[.lit l],[]]
    [.conj (.lit l) (.lit l)] [.lit l] [] (by change 2 ≤ 3; omega) (contextPremiseR l)
  have hp : At.shift (gaps [[],[.lit l],[]]) (.here (.lit l) []) = .there (.here (.lit l) []) := by
    apply At.index_injective
    rfl
  rw [hp] at h
  change (contextOldR l).rho .right _ + 1 = (contextNewR l).rho .right _ + 3 at h
  omega

/-- A fixed equal whole formula is not the newly introduced principal position. -/
theorem fixed_compound_distinct (Z : NormalForm P) (Λ : List (NormalForm P)) :
    At.shift [Z] (.here Z Λ) ≠ (.here Z (Z :: Λ)) := by
  intro h
  have hi := congrArg At.index h
  have hs := At.index_shift [Z] (.here Z Λ)
  change (At.shift [Z] (.here Z Λ)).index = 0 at hi
  change (At.shift [Z] (.here Z Λ)).index = 1 + 0 at hs
  omega

theorem internal_literal_tags_distinct (l : Literal P)
    (x y : (.lit l : NormalForm P).formula.Occ) :
    (Sum.inl x : (.disj (.lit l) (.lit l) : NormalForm P).formula.Occ) ≠ Sum.inr y := by
  intro h
  cases h

def constantPremiseL : G Empty [.top,.top] [.top,.top] :=
  G.thinR _ [] [.top] .top W1.constantPremiseL

def constantPremiseR : G Empty [.bot,.bot] [.bot,.bot] :=
  G.thinL [] [.bot] _ .bot W1.constantPremiseR

theorem emptyP_top :
    ofTerm (newL .top .top .top [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseL).denote =
      ofTerm (oldL .top .top .top [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseL).denote ∧
    (oldL .top .top .top [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseL).rho .right
      (At.shift [] (.here (.disj .top .top) [])) = 2 ∧
    (newL .top .top .top [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseL).rho .right
      (At.shift [] (.here (.disj .top .top) [])) = 1 :=
  ⟨denoteL ..,oldL_principal_rank ..,newL_principal_rank ..⟩

theorem emptyP_bot :
    ofTerm (newR .bot .bot .bot [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseR).denote =
      ofTerm (oldR .bot .bot .bot [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseR).denote ∧
    (oldR .bot .bot .bot [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseR).rho .left
      (At.shift [] (.here (.conj .bot .bot) [])) = 2 ∧
    (newR .bot .bot .bot [[],[]] [] [] [] (by change 2 ≤ 2; omega) constantPremiseR).rho .left
      (At.shift [] (.here (.conj .bot .bot) [])) = 1 :=
  ⟨denoteR ..,oldR_principal_rank ..,newR_principal_rank ..⟩

theorem both_signs_with_cut (p : P) :
    (contextNewL (.pos p)).cutCount = 1 ∧ (contextNewR (.neg p)).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.Logical
