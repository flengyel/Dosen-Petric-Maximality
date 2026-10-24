module

public import DosenPetric.GentzenTerminalContractionInstances
public import DosenPetric.GentzenDisjointExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.DisjointContraction.Terminal
universe u
variable {P : Type u}

def twoThree (T : NormalForm P) := TerminalContraction.terminalTail T T [[],[]] [[],[]] [T] [] []
def sourceTags (T : NormalForm P) : List (At (twoThree T).F T) := selectedCopies T [[],[],[],[],[],[]] []
def tagsFE (T : NormalForm P) : List (At (twoThree T).FE T) := selectedCopies T [[],[],[],[]] []
def tagsFC (T : NormalForm P) : List (At (twoThree T).FC T) := selectedCopies T [[],[],[],[],[]] []

theorem all_source_tags (T : NormalForm P) : (sourceTags T).map At.index = [0,1,2,3,4,5] := selectedCopies_indices T [[],[],[],[],[],[]] []
theorem C0_indices (T : NormalForm P) : (twoThree T).selectedC0.map At.index = [0,1] := (twoThree T).frame.bc0.selected_indices
theorem C1_indices (T : NormalForm P) : (twoThree T).selectedC1.map At.index = [0,1] := (twoThree T).frame.bc1.selected_indices
theorem E0_indices (T : NormalForm P) : (twoThree T).selectedE0.map At.index = [3,4,5] := (twoThree T).frame.be0.selected_indices
theorem E1_indices (T : NormalForm P) : (twoThree T).selectedE1.map At.index = [2,3,4] := (twoThree T).frame.be1.selected_indices

theorem route_indices {U K : List (NormalForm P)} (b : ContractionBlock P U K) {A : NormalForm P} (xs : List (At U A)) :
    xs.map (fun a => (b.route.get a).index) = xs.map (fun a => copyIndex b.gs a.index) :=
  List.map_congr_left (fun a _ => b.get_index a)

theorem composite_indices {U M K : List (NormalForm P)} (b : ContractionBlock P U M) (c : ContractionBlock P M K)
    {A : NormalForm P} (xs : List (At U A)) :
    xs.map (fun a => (c.route.get (b.route.get a)).index) = xs.map (fun a => copyIndex c.gs (copyIndex b.gs a.index)) := by
  apply List.map_congr_left
  intro a _
  rw [ContractionBlock.get_index,ContractionBlock.get_index]

theorem c0_indices (T : NormalForm P) :
    (sourceTags T).map (fun a => ((twoThree T).c0.get a).index) = [0,0,1,2,3,4] :=
  (route_indices (twoThree T).frame.bc0 (sourceTags T)).trans rfl

theorem e0_indices (T : NormalForm P) :
    (sourceTags T).map (fun a => ((twoThree T).e0.get a).index) = [0,1,2,3,3,3] :=
  (route_indices (twoThree T).frame.be0 (sourceTags T)).trans rfl

theorem c1_indices (T : NormalForm P) :
    (tagsFE T).map (fun a => ((twoThree T).c1.get a).index) = [0,0,1,2] :=
  (route_indices (twoThree T).frame.bc1 (tagsFE T)).trans rfl

theorem e1_indices (T : NormalForm P) :
    (tagsFC T).map (fun a => ((twoThree T).e1.get a).index) = [0,1,2,2,2] :=
  (route_indices (twoThree T).frame.be1 (tagsFC T)).trans rfl

theorem old_composite_indices (T : NormalForm P) :
    (sourceTags T).map (fun a => ((twoThree T).c1.get ((twoThree T).e0.get a)).index) = [0,0,1,2,2,2] :=
  (composite_indices (twoThree T).frame.be0 (twoThree T).frame.bc1 (sourceTags T)).trans rfl

theorem new_composite_indices (T : NormalForm P) :
    (sourceTags T).map (fun a => ((twoThree T).e1.get ((twoThree T).c0.get a)).index) = [0,0,1,2,2,2] :=
  (composite_indices (twoThree T).frame.bc0 (twoThree T).frame.be1 (sourceTags T)).trans rfl

theorem retained_indices (T : NormalForm P) : (twoThree T).xC.index = 0 ∧ (twoThree T).xE.index = 2 :=
  ⟨(twoThree T).xC_index,(twoThree T).xE_index⟩

def fixedSource (T : NormalForm P) : At (twoThree T).F T := .there (.there (.here T [T,T,T]))
def fixedFinal (T : NormalForm P) : At (twoThree T).K T := .there (.here T [T])

theorem fixed_tag (T : NormalForm P) :
    (fixedSource T).index = 2 ∧ (fixedFinal T).index = 1 ∧
    ((twoThree T).c1.get ((twoThree T).e0.get (fixedSource T))).index = 1 := by
  refine ⟨rfl,rfl,?_⟩
  rw [ContractionBlock.get_index,ContractionBlock.get_index]
  rfl

theorem fixed_original (T : NormalForm P) :
    (twoThree T).original (fixedFinal T) (by change 1 ≠ 0; omega) (by change 1 ≠ 2; omega) = fixedSource T := by
  symm
  apply (twoThree T).frame.original_unique (twoThree T).c1_keepE0 _ _ _
  apply At.index_injective
  exact (fixed_tag T).2.2

def premiseL (l : Literal P) : G P (twoThree (.lit l)).F [.lit l,.lit l,.lit l] := W1.DisjointContraction.literalPremiseL l
def premiseR (l : Literal P) : G P [.lit l,.lit l,.lit l] (twoThree (.lit l)).F := W1.DisjointContraction.literalPremiseR l

theorem literal_left (l : Literal P) :
    ofTerm (terminalNewL (twoThree (.lit l)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) _ (premiseL l)).denote =
    ofTerm (terminalOldL (twoThree (.lit l)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) _ (premiseL l)).denote := terminalDenoteL ..

theorem literal_right (l : Literal P) :
    ofTerm (terminalNewR (twoThree (.lit l)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) _ (premiseR l)).denote =
    ofTerm (terminalOldR (twoThree (.lit l)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) _ (premiseR l)).denote := terminalDenoteR ..

theorem emptyP_left_ranks :
    (terminalOldL (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _)).rho .left (twoThree .top).xC =
      terminalLCL (twoThree .top) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)+2 := terminal_old_xCL ..

theorem emptyP_right_ranks :
    (terminalNewR (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.bot] (W1.SameSideLogical.constantRight _)).rho .right (twoThree .top).xE =
      terminalLER (twoThree .top) (by change 2 ≤ 3; omega) [.bot] (W1.SameSideLogical.constantRight _)+3 := terminal_new_xER ..

theorem emptyP_sum_increases :
    terminalSumL (twoThree (.top : NormalForm Empty)) [.top]
      (terminalNewL (twoThree .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _)) =
    terminalSumL (twoThree (.top : NormalForm Empty)) [.top]
      (terminalOldL (twoThree .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _))+1 := by
  have h := terminal_sum_balanceL (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega)
    (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _)
  change terminalSumL (twoThree (.top : NormalForm Empty)) [.top]
    (terminalOldL (twoThree .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _))+3 =
    terminalSumL (twoThree (.top : NormalForm Empty)) [.top]
    (terminalNewL (twoThree .top) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _))+2 at h
  omega

def compound := TerminalContraction.terminalTail (.conj (.top : NormalForm Empty) .bot) (.disj .bot .top)
  [[],[.top],[]] [[.bot]] [.top] [.conj .top .top] [.disj .top .bot]

theorem compound_left :
    ofTerm (terminalNewL compound (by change 2 ≤ 3; omega) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)).denote =
    ofTerm (terminalOldL compound (by change 2 ≤ 3; omega) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)).denote := terminalDenoteL ..

theorem compound_right :
    ofTerm (terminalNewR compound (by change 2 ≤ 3; omega) (by change 2 ≤ 2; omega) [.bot] (W1.SameSideLogical.constantRight _)).denote =
    ofTerm (terminalOldR compound (by change 2 ≤ 3; omega) (by change 2 ≤ 2; omega) [.bot] (W1.SameSideLogical.constantRight _)).denote := terminalDenoteR ..

def equalTwo := TerminalContraction.terminalTail (.top : NormalForm Empty) .top [[],[]] [[]] [] [] []

theorem equal_arity_sum :
    terminalSumL equalTwo [.top] (terminalOldL equalTwo (by change 2 ≤ 2; omega) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)) =
    terminalSumL equalTwo [.top] (terminalNewL equalTwo (by change 2 ≤ 2; omega) (by change 2 ≤ 2; omega) [.top] (W1.SameSideLogical.constantLeft _)) := terminal_sum_eqL _ _ _ _ _ rfl

theorem fixed_rank_formula :
    (terminalNewL (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _)).rho .left (fixedFinal .top) =
      2+(W1.SameSideLogical.constantLeft (twoThree .top).F).rho .left (fixedSource .top) := by
  have h := terminal_other_newL (twoThree (.top : NormalForm Empty)) (by change 2 ≤ 2; omega)
    (by change 2 ≤ 3; omega) [.top] (W1.SameSideLogical.constantLeft _) (fixedFinal .top)
    (by change 1 ≠ 0; omega) (by change 1 ≠ 2; omega)
  exact h.trans (congrArg (fun a : At (twoThree (.top : NormalForm Empty)).F .top =>
    2+(W1.SameSideLogical.constantLeft (twoThree .top).F).rho .left a) (fixed_original (.top : NormalForm Empty)))

theorem both_signs_actual_cuts (p : P) :
    (terminalNewL (twoThree (.lit (.pos p))) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) _ (premiseL (.pos p))).cutCount = 1 ∧
    (terminalNewR (twoThree (.lit (.neg p))) (by change 2 ≤ 2; omega) (by change 2 ≤ 3; omega) _ (premiseR (.neg p))).cutCount = 1 := ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.W1.DisjointContraction.Terminal
