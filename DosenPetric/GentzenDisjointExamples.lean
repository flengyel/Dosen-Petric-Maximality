module

public import DosenPetric.GentzenDisjointInstances
public import DosenPetric.GentzenSameSideLogicalExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.DisjointContraction
universe u
variable {P : Type u}

/-- The requested n=2,m=3 test has one additional fixed formula equal to C=E. -/
def twoThree (T : NormalForm P) := Disjoint.fixedGap T T [[]] [] [[],[]] [T] [] [] []

def sixTags (T : NormalForm P) : List (At (twoThree T).F T) :=
  [.here T [T,T,T,T,T],.there (.here T [T,T,T,T]),.there (.there (.here T [T,T,T])),
   .there (.there (.there (.here T [T,T]))),.there (.there (.there (.there (.here T [T])))),
   .there (.there (.there (.there (.there (.here T [])))))]

theorem selectedC0_indices (T : NormalForm P) : ((twoThree T).selectedC0.map At.index) = [0,5] :=
  (twoThree T).bc0.selected_indices

theorem selectedE0_indices (T : NormalForm P) : ((twoThree T).selectedE0.map At.index) = [2,3,4] :=
  (twoThree T).be0.selected_indices

theorem selectedC1_indices (T : NormalForm P) : ((twoThree T).selectedC1.map At.index) = [0,3] :=
  (twoThree T).bc1.selected_indices

theorem selectedE1_indices (T : NormalForm P) : ((twoThree T).selectedE1.map At.index) = [1,2,3] :=
  (twoThree T).be1.selected_indices

theorem old_composite_indices (T : NormalForm P) :
    ((sixTags T).map (fun a => ((twoThree T).c1.get ((twoThree T).e0.get a)).index)) = [2,0,1,1,1,2] := by
  have he : (sixTags T).map (fun a => ((twoThree T).c1.get ((twoThree T).e0.get a)).index) =
      (sixTags T).map (fun a => copyIndex (twoThree T).bc1.gs (copyIndex (twoThree T).be0.gs a.index)) := by
    apply List.map_congr_left
    intro a _
    rw [ContractionBlock.get_index,ContractionBlock.get_index]
  exact he.trans rfl

theorem new_composite_indices (T : NormalForm P) :
    ((sixTags T).map (fun a => ((twoThree T).e1.get ((twoThree T).c0.get a)).index)) = [2,0,1,1,1,2] := by
  have he : (sixTags T).map (fun a => ((twoThree T).e1.get ((twoThree T).c0.get a)).index) =
      (sixTags T).map (fun a => copyIndex (twoThree T).be1.gs (copyIndex (twoThree T).bc0.gs a.index)) := by
    apply List.map_congr_left
    intro a _
    rw [ContractionBlock.get_index,ContractionBlock.get_index]
  exact he.trans rfl

theorem equal_label_indices (T : NormalForm P) :
    ((twoThree T).selectedC0.map At.index) = [0,5] ∧
    ((twoThree T).selectedE0.map At.index) = [2,3,4] ∧
    ((twoThree T).selectedC1.map At.index) = [0,3] ∧
    ((twoThree T).selectedE1.map At.index) = [1,2,3] ∧
    (twoThree T).xE.index = 1 ∧ (twoThree T).xC.index = 2 ∧
    ((sixTags T).map (fun a => ((twoThree T).c1.get ((twoThree T).e0.get a)).index)) = [2,0,1,1,1,2] ∧
    ((sixTags T).map (fun a => ((twoThree T).e1.get ((twoThree T).c0.get a)).index)) = [2,0,1,1,1,2] :=
  ⟨selectedC0_indices T,selectedE0_indices T,selectedC1_indices T,selectedE1_indices T,
    (twoThree T).xE_index,(twoThree T).xC_index,old_composite_indices T,new_composite_indices T⟩

theorem equal_label_fixed_tag (T : NormalForm P) :
    ((twoThree T).c1.get ((twoThree T).e0.get (.there (.here T [T,T,T,T])))).index = 0 ∧
    (.here T [T,T] : At (twoThree T).K T).index = 0 ∧
    (.there (.here T [T,T,T,T]) : At (twoThree T).F T) ∉ (twoThree T).selectedC0 ∧
    (.there (.here T [T,T,T,T]) : At (twoThree T).F T) ∉ (twoThree T).selectedE0 := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro h
    have hm := (List.mem_map (f := At.index)).mpr ⟨_,h,rfl⟩
    change 1 ∈ [0,5] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    omega
  · intro h
    have hm := (List.mem_map (f := At.index)).mpr ⟨_,h,rfl⟩
    change 1 ∈ [2,3,4] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    omega

def literalPremiseL (l : Literal P) : G P (twoThree (.lit l)).F [.lit l,.lit l,.lit l] :=
  G.thinL [] _ _ (.lit l) (W1.SameSideExchange.repeatedPremiseL l)
def literalPremiseR (l : Literal P) : G P [.lit l,.lit l,.lit l] (twoThree (.lit l)).F :=
  G.thinR _ [] _ (.lit l) (W1.SameSideExchange.repeatedPremiseR l)

theorem literal_left (l : Literal P) : LeftLaws (twoThree (.lit l)) (by change 2 ≤ 2; omega)
    (by change 2 ≤ 3; omega) _ (literalPremiseL l) := leftLaws ..
theorem literal_right (l : Literal P) : RightLaws (twoThree (.lit l)) (by change 2 ≤ 2; omega)
    (by change 2 ≤ 3; omega) _ (literalPremiseR l) := rightLaws ..

theorem two_three_sum_increases_left (l : Literal P) :
    endpointSumL (twoThree (.lit l)) _ (newL (twoThree (.lit l)) (by change 2 ≤ 2; omega)
      (by change 2 ≤ 3; omega) _ (literalPremiseL l)) =
    endpointSumL (twoThree (.lit l)) _ (oldL (twoThree (.lit l)) (by change 2 ≤ 2; omega)
      (by change 2 ≤ 3; omega) _ (literalPremiseL l))+1 := by
  have h := (literal_left l).sumBalance
  change _+3 = _+2 at h
  omega

theorem two_three_sum_increases_right (l : Literal P) :
    endpointSumR (twoThree (.lit l)) _ (newR (twoThree (.lit l)) (by change 2 ≤ 2; omega)
      (by change 2 ≤ 3; omega) _ (literalPremiseR l)) =
    endpointSumR (twoThree (.lit l)) _ (oldR (twoThree (.lit l)) (by change 2 ≤ 2; omega)
      (by change 2 ≤ 3; omega) _ (literalPremiseR l))+1 := by
  have h := (literal_right l).sumBalance
  change _+3 = _+2 at h
  omega

def equalTwo (T : NormalForm P) := Disjoint.fixedGap T T [[]] [] [[]] [] [] [] []
def compoundThreeTwo := Disjoint.fixedGap (.conj (.top : NormalForm Empty) .bot) (.disj .top .bot)
  [[]] [[.top]] [[]] [.top] [.bot,.top] [.conj .top .top] [.top]

theorem emptyP_two_three_left : LeftLaws (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega)
    (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _) := leftLaws ..
theorem emptyP_two_three_right : RightLaws (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega)
    (by change 2 ≤ 3; omega) [.bot] (W1.SameSideLogical.constantRight _) := rightLaws ..
theorem emptyP_compound_left : LeftLaws compoundThreeTwo (by change 2 ≤ 3; omega)
    (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _) := leftLaws ..
theorem emptyP_compound_right : RightLaws compoundThreeTwo (by change 2 ≤ 3; omega)
    (by change 2 ≤ 2; omega) [.bot] (W1.SameSideLogical.constantRight _) := rightLaws ..

theorem emptyP_equal_arity :
    endpointSumL (equalTwo (.top : NormalForm Empty)) [.top]
      (oldL (equalTwo .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)) =
    endpointSumL (equalTwo (.top : NormalForm Empty)) [.top]
      (newL (equalTwo .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)) :=
  sum_eq_of_arity_eqL _ _ _ _ _ rfl

theorem emptyP_sum_increases :
    endpointSumL (twoThree (.top : NormalForm Empty)) [.top]
      (newL (twoThree .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _)) =
    endpointSumL (twoThree (.top : NormalForm Empty)) [.top]
      (oldL (twoThree .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _))+1 := by
  have h := emptyP_two_three_left.sumBalance
  change _+3 = _+2 at h
  omega

theorem emptyP_fixed_rank :
    (oldL (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega)
      [.top] (W1.SameSideLogical.constantLeft _)).rho .left (.here .top [.top,.top]) =
    (newL (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega)
      [.top] (W1.SameSideLogical.constantLeft _)).rho .left (.here .top [.top,.top]) := by
  exact (other_oldL _ _ _ _ _ _ (by change 0 ≠ 2; omega) (by change 0 ≠ 1; omega)).trans
    (other_newL _ _ _ _ _ _ (by change 0 ≠ 2; omega) (by change 0 ≠ 1; omega)).symm

theorem both_signs_actual_cuts (p : P) :
    (newL (twoThree (.lit (.pos p))) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega)
      _ (literalPremiseL (.pos p))).cutCount = 1 ∧
    (newR (twoThree (.lit (.neg p))) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega)
      _ (literalPremiseR (.neg p))).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.DisjointContraction
