module

public import DosenPetric.GentzenSameSideThinningInstances
public import DosenPetric.GentzenExchangeCommutationExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideThinning
universe u
variable {P : Type u}

/-- Three selected copies; the fourth equal formula is fixed in the split gap. -/
def repeatedData (l : Literal P) :=
  GapInsertion.interior (.lit l) (.lit l) [[]] [[]] [.lit l] [] []

theorem repeated_left (l : Literal P) :
    LeftLaws (repeatedData l) (by change 2 ≤ 3; omega) _ (W1.Exchange.repeatedPremiseL l) := leftLaws ..

theorem repeated_right (l : Literal P) :
    RightLaws (repeatedData l) (by change 2 ≤ 3; omega) _ (W1.Exchange.repeatedPremiseR l) := rightLaws ..

theorem repeated_selected_indices (l : Literal P) :
    ((repeatedData l).selected0.map At.index) = [0,2,3] ∧
    ((repeatedData l).selected1.map At.index) = [0,3,4] ∧
    (repeatedData l).zUpper.index = 2 ∧ (repeatedData l).zLower.index = 1 ∧
    (repeatedData l).keep1.index = 2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- E=C does not select the new occurrence, or the equal fixed gap occurrence. -/
theorem repeated_inserted_distinct (l : Literal P) :
    (repeatedData l).zLower ≠ (repeatedData l).keep1 :=
  (repeatedData l).inserted_distinct (h := rfl)

theorem repeated_endpoint_loss (l : Literal P) :
    (oldL (repeatedData l) (by change 2 ≤ 3; omega) _ (W1.Exchange.repeatedPremiseL l)).rho .left
      (repeatedData l).keep1 =
    (newL (repeatedData l) (by change 2 ≤ 3; omega) _ (W1.Exchange.repeatedPremiseL l)).rho .left
      (repeatedData l).keep1 + 2 := by
  have h := (repeated_left l).endpoint_loss
  change _ + 1 = _ + 3 at h
  omega

/-- Two selected copies, insertion in the first gap, with a real cut. -/
def beforeData (l : Literal P) := GapInsertion.interior (.lit l) (.lit l) [] [[]] [] [] []

/-- Two selected copies, insertion between them, with both gap halves empty. -/
def betweenData (l : Literal P) := GapInsertion.interior (.lit l) (.lit l) [[]] [] [] [] []

def afterData (l : Literal P) := GapInsertion.terminal (.lit l) (.lit l) [[],[]] [] []

theorem before_left (l : Literal P) :
    LeftLaws (beforeData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseL l) := leftLaws ..

theorem between_right (l : Literal P) :
    RightLaws (betweenData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseR l) := rightLaws ..

theorem after_left (l : Literal P) :
    LeftLaws (afterData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseL l) := leftLaws ..

theorem after_right (l : Literal P) :
    RightLaws (afterData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseR l) := rightLaws ..

theorem before_between_after_indices (l : Literal P) :
    (beforeData l).zUpper.index = 0 ∧ (betweenData l).zUpper.index = 1 ∧
    (afterData l).zUpper.index = 2 ∧
    ((betweenData l).selected1.map At.index) = [0,2] ∧
    ((afterData l).selected1.map At.index) = [0,1] := by exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Insertion at the end, after a nonempty tail containing another equal formula. -/
def tailPremiseL (l : Literal P) : G P [.lit l,.lit l,.lit l] [.lit l] :=
  G.thinL [] [.lit l,.lit l] _ (.lit l) (W1.cutPremiseL l)

def tailPremiseR (l : Literal P) : G P [.lit l] [.lit l,.lit l,.lit l] :=
  G.thinR _ [] [.lit l,.lit l] (.lit l) (W1.cutPremiseR l)

def endData (l : Literal P) := GapInsertion.terminal (.lit l) (.lit l) [[],[]] [.lit l] []

theorem end_left (l : Literal P) :
    LeftLaws (endData l) (by change 2 ≤ 2; omega) _ (tailPremiseL l) := leftLaws ..

theorem end_right (l : Literal P) :
    RightLaws (endData l) (by change 2 ≤ 2; omega) _ (tailPremiseR l) := rightLaws ..

theorem end_indices (l : Literal P) :
    (endData l).keep1.index = 0 ∧ (endData l).zLower.index = 2 ∧
    (endData l).zUpper.index = 3 := by exact ⟨rfl,rfl,rfl⟩

/-- A nonempty terminal split: insertion between two fixed equal tail positions. -/
def tailMiddleData (l : Literal P) :=
  GapInsertion.terminal (.lit l) (.lit l) [[],[]] [.lit l] [.lit l]

theorem tail_middle_left (l : Literal P) :
    LeftLaws (tailMiddleData l) (by change 2 ≤ 2; omega) _ (W1.Exchange.repeatedPremiseL l) := leftLaws ..

theorem tail_middle_right (l : Literal P) :
    RightLaws (tailMiddleData l) (by change 2 ≤ 2; omega) _ (W1.Exchange.repeatedPremiseR l) := rightLaws ..

/-- Both halves of the first fixed gap are nonempty, with no freshness condition. -/
def gapMiddleData (l : Literal P) :=
  GapInsertion.interior (.lit l) (.lit l) [] [[]] [.lit l] [.lit l] []

theorem gap_middle_left (l : Literal P) :
    LeftLaws (gapMiddleData l) (by change 2 ≤ 2; omega) _ (W1.Exchange.repeatedPremiseL l) := leftLaws ..

theorem gap_middle_right (l : Literal P) :
    RightLaws (gapMiddleData l) (by change 2 ≤ 2; omega) _ (W1.Exchange.repeatedPremiseR l) := rightLaws ..

/-- Compound thinning is permitted by the equality/rank laws, but is not atomized. -/
def compoundData (l : Literal P) :=
  GapInsertion.interior (.lit l) (.conj (.lit l) (.lit l)) [[]] [] [] [] []

theorem compound_left (l : Literal P) :
    LeftLaws (compoundData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseL l) := leftLaws ..

theorem compound_not_atomized (l : Literal P) :
    ¬ (newL (compoundData l) (by change 2 ≤ 2; omega) _ (W1.cutPremiseL l)).Atomized := by
  intro h
  exact h.1

/-- Genuine constant proof trees with no variable inhabitant. -/
theorem emptyP_interior_left :
    LeftLaws (GapInsertion.interior (.top : NormalForm Empty) .bot [] [[]] [] [] [])
      (by change 2 ≤ 2; omega) [.top] W1.constantPremiseL := leftLaws ..

theorem emptyP_interior_right :
    RightLaws (GapInsertion.interior (.bot : NormalForm Empty) .top [[]] [] [] [] [])
      (by change 2 ≤ 2; omega) [.bot] W1.constantPremiseR := rightLaws ..

theorem emptyP_terminal_left :
    LeftLaws (GapInsertion.terminal (.top : NormalForm Empty) .top [[],[]] [] [])
      (by change 2 ≤ 2; omega) [.top] W1.constantPremiseL := leftLaws ..

theorem emptyP_terminal_right :
    RightLaws (GapInsertion.terminal (.bot : NormalForm Empty) .bot [[],[]] [] [])
      (by change 2 ≤ 2; omega) [.bot] W1.constantPremiseR := rightLaws ..

theorem both_signs_actual_cut (p : P) :
    (newL (repeatedData (.pos p)) (by change 2 ≤ 3; omega) _
      (W1.Exchange.repeatedPremiseL (.pos p))).cutCount = 1 ∧
    (newR (afterData (.neg p)) (by change 2 ≤ 2; omega) _
      (W1.cutPremiseR (.neg p))).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.SameSideThinning
