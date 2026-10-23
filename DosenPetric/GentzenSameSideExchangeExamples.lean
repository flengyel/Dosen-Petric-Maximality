module

public import DosenPetric.GentzenSameSideExchangeInstances
public import DosenPetric.GentzenExchangeCommutationExamples
public import DosenPetric.GentzenSameSideThinningExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideExchange
universe u
variable {P : Type u}

/-- Three selected copies and two equal fixed copies in one gap. -/
def repeatedData (l : Literal P) :=
  GapExchange.interior (.lit l) [[]] [[]] [] [.lit l] [.lit l] [] []

def repeatedPremiseL (l : Literal P) : G P [.lit l,.lit l,.lit l,.lit l,.lit l] [.lit l,.lit l,.lit l] :=
  G.thinL [] _ _ (.lit l) (W1.Exchange.repeatedPremiseL l)

def repeatedPremiseR (l : Literal P) : G P [.lit l,.lit l,.lit l] [.lit l,.lit l,.lit l,.lit l,.lit l] :=
  G.thinR _ [] _ (.lit l) (W1.Exchange.repeatedPremiseR l)

theorem repeated_left (l : Literal P) :
    LeftLaws (repeatedData l) (by change 2 ≤ 3; omega) _ (repeatedPremiseL l) := leftLaws ..

theorem repeated_right (l : Literal P) :
    RightLaws (repeatedData l) (by change 2 ≤ 3; omega) _ (repeatedPremiseR l) := rightLaws ..

theorem repeated_selected_indices (l : Literal P) :
    ((repeatedData l).selected0.map At.index) = [0,3,4] ∧
    ((repeatedData l).selected1.map At.index) = [0,3,4] := ⟨rfl,rfl⟩

/-- The context lists are equal, but the two fixed occurrences really transpose. -/
theorem equal_label_transposition (C : NormalForm P) :
    ((At.here C [C]).swapBlocks [] [C] [C] []).index = 1 ∧
    ((At.there (At.here C [])).swapBlocks [] [C] [C] []).index = 0 ∧
    (At.here C [C]).swapBlocks [] [C] [C] [] ≠ At.here C [C] := by
  refine ⟨rfl,rfl,?_⟩
  intro h
  have hi := congrArg At.index h
  change 1 = 0 at hi
  omega

theorem fixed_equal_positions_swap (l : Literal P) :
    ((repeatedData l).swapLower (At.here (.lit l) [.lit l,.lit l])).index = 1 ∧
    ((repeatedData l).swapLower (At.there (At.here (.lit l) [.lit l]))).index = 0 ∧
    (repeatedData l).keep1.index = 2 := ⟨rfl,rfl,rfl⟩

theorem repeated_fixed_rank (l : Literal P) :
    (newL (repeatedData l) (by change 2 ≤ 3; omega) _ (repeatedPremiseL l)).rho .left
      ((repeatedData l).swapLower (At.here (.lit l) [.lit l,.lit l])) =
    (oldL (repeatedData l) (by change 2 ≤ 3; omega) _ (repeatedPremiseL l)).rho .left
      ((repeatedData l).swapLower (At.here (.lit l) [.lit l,.lit l])) :=
  fixed_rankL _ _ _ _ _ (by change 0 ≠ 2; omega)

theorem repeated_endpoint_loss (l : Literal P) :
    (oldR (repeatedData l) (by change 2 ≤ 3; omega) _ (repeatedPremiseR l)).rho .right (repeatedData l).keep1 =
    (newR (repeatedData l) (by change 2 ≤ 3; omega) _ (repeatedPremiseR l)).rho .right (repeatedData l).keep1 + 2 := by
  have h := (repeated_right l).endpoint_loss
  change _ + 1 = _ + 3 at h
  omega

/-- Explicit exchange nodes remain in clusters even when both blocks are empty. -/
def emptyData (l : Literal P) := GapExchange.interior (.lit l) [[]] [] [] [] [] [] []

theorem both_empty_left (l : Literal P) :
    LeftLaws (emptyData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseL l) := leftLaws ..

theorem both_empty_right (l : Literal P) :
    RightLaws (emptyData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseR l) := rightLaws ..

theorem one_empty_left (l : Literal P) :
    LeftLaws (GapExchange.interior (.lit l) [[]] [] [] [] [.lit l] [] [])
      (by change 2 ≤ 2; omega) _ (W1.SameSideThinning.tailPremiseL l) := leftLaws ..

theorem one_empty_right (l : Literal P) :
    RightLaws (GapExchange.terminal (.lit l) [[],[]] [] [.lit l] [] [])
      (by change 2 ≤ 2; omega) _ (W1.SameSideThinning.tailPremiseR l) := rightLaws ..

/-- Arbitrarily many constant positions without an inhabitant of the variable type. -/
def topPremise : (n : Nat) → G Empty (List.replicate n .top) [.top]
  | 0 => G.topI
  | n+1 => G.thinL [] _ _ .top (topPremise n)

def botPremise : (n : Nat) → G Empty [.bot] (List.replicate n .bot)
  | 0 => G.botE
  | n+1 => G.thinR _ [] _ .bot (botPremise n)

theorem emptyP_interior_left :
    LeftLaws (GapExchange.interior (.top : NormalForm Empty) [[]] [] [.top] [.top] [.top,.top] [.top] [.top])
      (by change 2 ≤ 2; omega) [.top] (topPremise 8) := leftLaws ..

theorem emptyP_interior_right :
    RightLaws (GapExchange.interior (.bot : NormalForm Empty) [[]] [] [.bot] [.bot] [.bot,.bot] [.bot] [.bot])
      (by change 2 ≤ 2; omega) [.bot] (botPremise 8) := rightLaws ..

theorem emptyP_terminal_left :
    LeftLaws (GapExchange.terminal (.top : NormalForm Empty) [[],[]] [.top] [.top] [.top,.top] [.top])
      (by change 2 ≤ 2; omega) [.top] (topPremise 7) := leftLaws ..

theorem emptyP_terminal_right :
    RightLaws (GapExchange.terminal (.bot : NormalForm Empty) [[],[]] [.bot] [.bot] [.bot,.bot] [.bot])
      (by change 2 ≤ 2; omega) [.bot] (botPremise 7) := rightLaws ..

/-- Compound fixed formulas are allowed, with no new Atomized hypothesis. -/
def compoundPremiseL (l : Literal P) : G P [.lit l,.conj (.lit l) (.lit l),.lit l,.lit l] [.lit l] :=
  G.thinL [.lit l,.conj (.lit l) (.lit l)] [.lit l] _ (.lit l)
    (G.thinL [.lit l] [.lit l] _ (.conj (.lit l) (.lit l)) (W1.cutPremiseL l))

theorem compound_left (l : Literal P) :
    LeftLaws (GapExchange.interior (.lit l) [[]] [] [] [.conj (.lit l) (.lit l)] [.lit l] [] [])
      (by change 2 ≤ 2; omega) [.lit l] (compoundPremiseL l) := leftLaws ..

def compoundPremiseR (l : Literal P) : G P [.lit l] [.lit l,.conj (.lit l) (.lit l),.lit l,.lit l] :=
  G.thinR _ [.lit l,.conj (.lit l) (.lit l)] [.lit l] (.lit l)
    (G.thinR _ [.lit l] [.lit l] (.conj (.lit l) (.lit l)) (W1.cutPremiseR l))

theorem compound_right (l : Literal P) :
    RightLaws (GapExchange.interior (.lit l) [[]] [] [] [.conj (.lit l) (.lit l)] [.lit l] [] [])
      (by change 2 ≤ 2; omega) [.lit l] (compoundPremiseR l) := rightLaws ..

theorem both_signs_actual_cut (p : P) :
    (newL (repeatedData (.pos p)) (by change 2 ≤ 3; omega) _ (repeatedPremiseL (.pos p))).cutCount = 1 ∧
    (newR (emptyData (.neg p)) (by change 2 ≤ 2; omega) _ (W1.cutPremiseR (.neg p))).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.SameSideExchange
