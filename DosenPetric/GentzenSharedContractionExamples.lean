module

public import DosenPetric.GentzenSharedContractionInstances
public import DosenPetric.GentzenTerminalContractionExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W3.SharedContraction.Examples
universe u
variable {P : Type u}

def twoThree (C : NormalForm P) : Gentzen.SharedContraction.Data P :=
  ⟨C,[[],[C]],[[C],[],[]],[C,C,C],[C],rfl⟩
def threeTwo (C : NormalForm P) : Gentzen.SharedContraction.Data P :=
  ⟨C,[[],[C],[]],[[],[]],[C],[C],rfl⟩
def middleThree (C : NormalForm P) : Gentzen.SharedContraction.Data P :=
  ⟨C,[[C],[]],[[],[],[]],[C],[],rfl⟩
def equalTwo (C : NormalForm P) : Gentzen.SharedContraction.Data P :=
  ⟨C,[[],[]],[[],[]],[C],[],rfl⟩

theorem shared23 (C : NormalForm P) : (twoThree C).Shared := by
  apply ((twoThree C).outer.selected_iff _).mpr
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index,ContractionBlock.keep_index]
  rfl
theorem shared32 (C : NormalForm P) : (threeTwo C).Shared := by
  apply ((threeTwo C).outer.selected_iff _).mpr
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index,ContractionBlock.keep_index]
  rfl
theorem sharedMiddle (C : NormalForm P) : (middleThree C).Shared := by
  apply ((middleThree C).outer.selected_iff _).mpr
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index,ContractionBlock.keep_index]
  rfl
theorem sharedEqual (C : NormalForm P) : (equalTwo C).Shared := by
  apply ((equalTwo C).outer.selected_iff _).mpr
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index,ContractionBlock.keep_index]
  rfl

def tags23 (C : NormalForm P) : List (At (twoThree C).F C) :=
  selectedCopies C [[],[],[],[],[],[]] []
def tagsI23 (C : NormalForm P) : List (At (twoThree C).I C) :=
  selectedCopies C [[],[],[],[],[]] []
def tags32 (C : NormalForm P) : List (At (threeTwo C).F C) :=
  selectedCopies C [[],[],[],[],[]] []

theorem inner_indices23 (C : NormalForm P) : (twoThree C).inner.selected.map At.index = [0,2] :=
  (twoThree C).inner.selected_indices
theorem outer_indices23 (C : NormalForm P) : (twoThree C).outer.selected.map At.index = [1,2,3] :=
  (twoThree C).outer.selected_indices
theorem inner_map23 (C : NormalForm P) :
    (tags23 C).map (fun a => ((twoThree C).inner.route.get a).index) = [1,0,1,2,3,4] :=
  (W1.DisjointContraction.Terminal.route_indices (twoThree C).inner (tags23 C)).trans rfl
theorem outer_map23 (C : NormalForm P) :
    (tagsI23 C).map (fun a => ((twoThree C).outer.route.get a).index) = [0,1,1,1,2] :=
  (W1.DisjointContraction.Terminal.route_indices (twoThree C).outer (tagsI23 C)).trans rfl
theorem composite_map23 (C : NormalForm P) :
    (tags23 C).map (fun a => ((twoThree C).outer.route.get ((twoThree C).inner.route.get a)).index) =
      [1,0,1,1,1,2] :=
  (W1.DisjointContraction.Terminal.composite_indices (twoThree C).inner (twoThree C).outer (tags23 C)).trans rfl

theorem flat_gaps23 (C : NormalForm P) :
    ((twoThree C).flat (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 C)).gs = [[],[C],[],[]] := rfl
theorem flat_selected23 (C : NormalForm P) :
    ((twoThree C).flat (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 C)).selected.map At.index = [0,2,3,4] :=
  (((twoThree C).flat (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 C)).selected_indices).trans rfl
theorem flat_map23 (C : NormalForm P) :
    (tags23 C).map (fun a => (((twoThree C).flat (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 C)).route.get a).index) =
      [1,0,1,1,1,2] := by
  exact (List.map_congr_left (fun a _ => congrArg At.index
    ((twoThree C).square (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 C) a))).trans (composite_map23 C)

def fixedBefore (C : NormalForm P) : At (twoThree C).K C := .here C [C,C]
def fixedAfter (C : NormalForm P) : At (twoThree C).K C := .there (.there (.here C []))
theorem fixed_original23 (C : NormalForm P) :
    ((twoThree C).original (shared23 C) (fixedBefore C) (by change 0 ≠ 1; decide)).index = 1 ∧
    ((twoThree C).original (shared23 C) (fixedAfter C) (by change 2 ≠ 1; decide)).index = 5 := ⟨rfl,rfl⟩

theorem flat_gaps32 (C : NormalForm P) :
    ((threeTwo C).flat (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared32 C)).gs = [[],[],[],[]] := rfl
theorem flat_selected32 (C : NormalForm P) :
    ((threeTwo C).flat (Nat.le_succ 2) (Nat.le_refl 2) (shared32 C)).selected.map At.index = [0,1,2,3] :=
  (((threeTwo C).flat (Nat.le_succ 2) (Nat.le_refl 2) (shared32 C)).selected_indices).trans rfl
theorem composite_map32 (C : NormalForm P) :
    (tags32 C).map (fun a => ((threeTwo C).outer.route.get ((threeTwo C).inner.route.get a)).index) =
      [0,0,0,0,1] :=
  (W1.DisjointContraction.Terminal.composite_indices (threeTwo C).inner (threeTwo C).outer (tags32 C)).trans rfl

theorem shared_offsets (C : NormalForm P) :
    (twoThree C).inner.keep.index = 1 ∧ (threeTwo C).inner.keep.index = 1 ∧
    (middleThree C).inner.keep.index = 1 ∧
    (threeTwo C).outer.selected.map At.index = [0,1] ∧
    (middleThree C).outer.selected.map At.index = [0,1,2] := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem empty_left_rank_drop :
    (oldL (twoThree (.top : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (twoThree .top).outer.keep =
    (flatL (twoThree (.top : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 .top) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (twoThree .top).outer.keep+3 := retained_rankL ..
theorem empty_right_rank_drop :
    (oldR (twoThree (.top : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (twoThree .top).outer.keep =
    (flatR (twoThree (.top : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 .top) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (twoThree .top).outer.keep+3 := retained_rankR ..

theorem fixed_other_loss_left :
    (oldL (twoThree (.top : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_succ 2) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (fixedBefore .top) =
    (flatL (twoThree (.top : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_succ 2) (shared23 _) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (fixedBefore .top)+1 :=
  other_lossL _ _ _ _ _ _ (fixedBefore .top) (by change 0 ≠ 1; decide)

theorem fixed_other_loss_right :
    (oldR (twoThree (.top : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_succ 2) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (fixedAfter .top) =
    (flatR (twoThree (.top : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_succ 2) (shared23 _) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (fixedAfter .top)+1 :=
  other_lossR _ _ _ _ _ _ (fixedAfter .top) (by change 2 ≠ 1; decide)

def compound : NormalForm Empty := .conj .top (.disj .bot .top)
theorem compound_left :
    ofTerm (flatL (threeTwo compound) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared32 _) [.top]
      (W1.SameSideLogical.constantLeft _)).denote =
    ofTerm (oldL (threeTwo compound) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) [.top]
      (W1.SameSideLogical.constantLeft _)).denote := denoteL ..
theorem compound_right :
    ofTerm (flatR (threeTwo compound) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared32 _) [.bot]
      (W1.SameSideLogical.constantRight _)).denote =
    ofTerm (oldR (threeTwo compound) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) [.bot]
      (W1.SameSideLogical.constantRight _)).denote := denoteR ..

theorem middle_left :
    ofTerm (flatL (middleThree (.bot : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (sharedMiddle _) [.top]
      (W1.SameSideLogical.constantLeft _)).denote =
    ofTerm (oldL (middleThree (.bot : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) [.top]
      (W1.SameSideLogical.constantLeft _)).denote := denoteL ..
theorem middle_right :
    ofTerm (flatR (middleThree (.bot : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_succ 2) (sharedMiddle _) [.bot]
      (W1.SameSideLogical.constantRight _)).denote =
    ofTerm (oldR (middleThree (.bot : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_succ 2) [.bot]
      (W1.SameSideLogical.constantRight _)).denote := denoteR ..
theorem equal_left :
    ofTerm (flatL (equalTwo (.bot : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_refl 2) (sharedEqual _) [.top]
      (W1.SameSideLogical.constantLeft _)).denote =
    ofTerm (oldL (equalTwo (.bot : NormalForm Empty)) (Nat.le_refl 2) (Nat.le_refl 2) [.top]
      (W1.SameSideLogical.constantLeft _)).denote := denoteL ..
theorem equal_right :
    ofTerm (flatR (equalTwo (.bot : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (sharedEqual _) [.bot]
      (W1.SameSideLogical.constantRight _)).denote =
    ofTerm (oldR (equalTwo (.bot : NormalForm Empty)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) [.bot]
      (W1.SameSideLogical.constantRight _)).denote := denoteR ..

theorem literal_left (l : Literal P) :
    ofTerm (flatL (twoThree (.lit l)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 _) _
      (W1.DisjointContraction.Terminal.premiseL l)).denote =
    ofTerm (oldL (twoThree (.lit l)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) _
      (W1.DisjointContraction.Terminal.premiseL l)).denote := denoteL ..
theorem literal_right (l : Literal P) :
    ofTerm (flatR (twoThree (.lit l)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 _) _
      (W1.DisjointContraction.Terminal.premiseR l)).denote =
    ofTerm (oldR (twoThree (.lit l)) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) _
      (W1.DisjointContraction.Terminal.premiseR l)).denote := denoteR ..

theorem both_signs_actual_cuts (p : P) :
    (flatL (twoThree (.lit (.pos p))) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 _) _
      (W1.DisjointContraction.Terminal.premiseL (.pos p))).cutCount = 1 ∧
    (flatR (twoThree (.lit (.neg p))) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (by first | exact Nat.le_refl 2 | exact Nat.le_succ 2) (shared23 _) _
      (W1.DisjointContraction.Terminal.premiseR (.neg p))).cutCount = 1 :=
  ⟨(flat_countL ..).trans rfl,(flat_countR ..).trans rfl⟩

end DosenPetric.Reduced.Gentzen.W3.SharedContraction.Examples
