module

public import DosenPetric.GentzenSameSideLogicalInstances
public import DosenPetric.GentzenSameSideExchangeExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideLogical
universe u
variable {P : Type u}

/-- A=B=C, with the two consumed equal positions fixed between selected copies. -/
def repeatedData (o : Op) (l : Literal P) := GapLogical.interior o (.lit l) (.lit l) (.lit l) [[]] [[]] [] [] []

theorem repeated_left (l : Literal P) :
    LeftLaws (repeatedData .conj l) (by change 2 ≤ 3; omega) _ (W1.SameSideExchange.repeatedPremiseL l) := leftLaws ..

theorem repeated_right (l : Literal P) :
    RightLaws (repeatedData .disj l) (by change 2 ≤ 3; omega) _ (W1.SameSideExchange.repeatedPremiseR l) := rightLaws ..

theorem equal_labels_consumed_slots (o : Op) (l : Literal P) :
    (repeatedData o l).uParent (repeatedData o l).aUpper = none ∧
    (repeatedData o l).uParent (repeatedData o l).bUpper = none ∧
    (repeatedData o l).aUpper ≠ (repeatedData o l).bUpper ∧
    ((repeatedData o l).selected0.map At.index) = [0,3,4] ∧
    ((repeatedData o l).selected1.map At.index) = [0,2,3] := by
  refine ⟨(repeatedData o l).consumed_first,(repeatedData o l).consumed_second,?_,rfl,rfl⟩
  intro h
  have hi := congrArg At.index h
  change 1 = 2 at hi
  omega

theorem repeated_endpoint_loss (l : Literal P) :
    (oldL (repeatedData .conj l) (by change 2 ≤ 3; omega) _ (W1.SameSideExchange.repeatedPremiseL l)).rho .left
      (repeatedData .conj l).keep1 =
    (newL (repeatedData .conj l) (by change 2 ≤ 3; omega) _ (W1.SameSideExchange.repeatedPremiseL l)).rho .left
      (repeatedData .conj l).keep1 + 2 := by
  have h := (repeated_left l).endpoint_loss
  change _ + 1 = _ + 3 at h
  omega

/-- Existing constant proofs inhabit all contexts, without an inhabitant of Empty. -/
def constantLeft : (Γ : List (NormalForm Empty)) → G Empty Γ [.top]
  | [] => G.topI
  | A :: Γ => G.thinL [] Γ [.top] A (constantLeft Γ)

def constantRight : (Δ : List (NormalForm Empty)) → G Empty [.bot] Δ
  | [] => G.botE
  | A :: Δ => G.thinR [.bot] [] Δ A (constantRight Δ)

def nonemptyLeft := GapLogical.interior .conj (.top : NormalForm Empty) .top .top [[]] [] [.top] [.top] [.top]
def nonemptyRight := GapLogical.interior .disj (.bot : NormalForm Empty) .bot .bot [[]] [] [.bot] [.bot] [.bot]

theorem emptyP_interior_left : LeftLaws nonemptyLeft (by change 2 ≤ 2; omega) [.top] (constantLeft _) := leftLaws ..
theorem emptyP_interior_right : RightLaws nonemptyRight (by change 2 ≤ 2; omega) [.bot] (constantRight _) := rightLaws ..

theorem emptyP_terminal_left :
    LeftLaws (GapLogical.terminal .conj (.top : NormalForm Empty) .top .top [[],[]] [.top] [.top])
      (by change 2 ≤ 2; omega) [.top] (constantLeft _) := leftLaws ..

theorem emptyP_terminal_right :
    RightLaws (GapLogical.terminal .disj (.bot : NormalForm Empty) .bot .bot [[],[]] [.bot] [.bot])
      (by change 2 ≤ 2; omega) [.bot] (constantRight _) := rightLaws ..

def compoundCopyLeft := GapLogical.interior .conj (.top : NormalForm Empty) .top (.conj .top .top) [[]] [] [] [] []
def compoundCopyRight := GapLogical.interior .disj (.bot : NormalForm Empty) .bot (.disj .bot .bot) [[]] [] [] [] []

theorem compound_is_retained_label_left :
    compoundCopyLeft.zLower ≠ compoundCopyLeft.keep1 ∧
    LeftLaws compoundCopyLeft (by change 2 ≤ 2; omega) [.top] (constantLeft _) := by
  refine ⟨?_,leftLaws ..⟩
  intro h
  exact compoundCopyLeft.principal_distinct (congrArg At.index h)

theorem compound_is_retained_label_right :
    compoundCopyRight.zLower ≠ compoundCopyRight.keep1 ∧
    RightLaws compoundCopyRight (by change 2 ≤ 2; omega) [.bot] (constantRight _) := by
  refine ⟨?_,rightLaws ..⟩
  intro h
  exact compoundCopyRight.principal_distinct (congrArg At.index h)

theorem compound_components_left :
    LeftLaws (GapLogical.terminal .conj (.conj (.top : NormalForm Empty) .bot) (.disj .top .bot) .top [[],[]] [] [])
      (by change 2 ≤ 2; omega) [.top] (constantLeft _) := leftLaws ..

theorem compound_components_right :
    RightLaws (GapLogical.terminal .disj (.conj (.top : NormalForm Empty) .bot) (.disj .top .bot) .bot [[],[]] [] [])
      (by change 2 ≤ 2; omega) [.bot] (constantRight _) := rightLaws ..

theorem other_fixed_example :
    (newL nonemptyLeft (by change 2 ≤ 2; omega) [.top] (constantLeft _)).rho .left
      (.here .top [.conj .top .top,.top,.top,.top]) =
    (oldL nonemptyLeft (by change 2 ≤ 2; omega) [.top] (constantLeft _)).rho .left
      (.here .top [.conj .top .top,.top,.top,.top]) :=
  other_rankL _ _ _ _ _ (by change 0 ≠ 1; omega) (by change 0 ≠ 3; omega)

theorem both_signs_actual_cut (p : P) :
    (newL (repeatedData .conj (.pos p)) (by change 2 ≤ 3; omega) _
      (W1.SameSideExchange.repeatedPremiseL (.pos p))).cutCount = 1 ∧
    (newR (repeatedData .disj (.neg p)) (by change 2 ≤ 3; omega) _
      (W1.SameSideExchange.repeatedPremiseR (.neg p))).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.SameSideLogical
