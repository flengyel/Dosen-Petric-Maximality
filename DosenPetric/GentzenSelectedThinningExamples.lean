module

public import DosenPetric.GentzenSelectedThinningRanks
public import DosenPetric.GentzenTerminalContractionExamples
public import DosenPetric.PositiveThinningAtomization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W2.SelectedThinning.Examples
universe u
variable {P : Type u}

def two (C : NormalForm P) : Gentzen.SelectedThinning.Data P := ⟨C,[[],[]],[]⟩
def tagged (C : NormalForm P) : Gentzen.SelectedThinning.Data P := ⟨C,[[C],[C]],[C,C]⟩
def three (C : NormalForm P) : Gentzen.SelectedThinning.Data P := ⟨C,[[],[],[]],[C]⟩

def tagsF (C : NormalForm P) : List (At (tagged C).F C) := selectedCopies C [[],[],[],[],[],[]] []
def tagsU (C : NormalForm P) : List (At (tagged C).U C) := selectedCopies C [[],[],[],[],[],[],[]] []
def tagsI (C : NormalForm P) : List (At (tagged C).I C) := selectedCopies C [[],[],[],[],[]] []

theorem inner_selected (C : NormalForm P) : (tagged C).inner.selected.map At.index = [1,3] :=
  (tagged C).inner.selected_indices
theorem outer_selected (C : NormalForm P) : (tagged C).outer.selected.map At.index = [1,3,6] :=
  (tagged C).outer.selected_indices
theorem inserted_retained (C : NormalForm P) : (tagged C).z.index = 6 ∧ (tagged C).x.index = 4 :=
  ⟨(tagged C).z_index,(tagged C).x_index⟩
theorem outer_map (C : NormalForm P) :
    (tagsU C).map (fun a => ((tagged C).outer.route.get a).index) = [0,4,1,4,2,3,4] :=
  (W1.DisjointContraction.Terminal.route_indices (tagged C).outer (tagsU C)).trans rfl
theorem inner_map (C : NormalForm P) :
    (tagsF C).map (fun a => ((tagged C).inner.route.get a).index) = [0,2,1,2,3,4] :=
  (W1.DisjointContraction.Terminal.route_indices (tagged C).inner (tagsF C)).trans rfl
theorem thinning_map (C : NormalForm P) :
    (tagsF C).map (fun a => ((tagged C).t.get a).index) = [0,1,2,3,4,5] :=
  (List.map_congr_left (fun a _ => (tagged C).t_index a)).trans
    (selectedCopies_indices C [[],[],[],[],[],[]] [])
theorem exchange_map (C : NormalForm P) :
    (tagsI C).map (fun a => ((tagged C).e.get a).index) = [0,1,4,2,3] :=
  (List.map_congr_left (fun a _ => (tagged C).e_index a)).trans rfl

theorem old_composite_map (C : NormalForm P) :
    (tagsF C).map (fun a => ((tagged C).outer.route.get ((tagged C).t.get a)).index) = [0,4,1,4,2,3] := by
  have he : (tagsF C).map (fun a => ((tagged C).outer.route.get ((tagged C).t.get a)).index) =
      (tagsF C).map (fun a => copyIndex (tagged C).outer.gs a.index) := by
    apply List.map_congr_left
    intro a _
    rw [ContractionBlock.get_index,(tagged C).t_index]
  exact he.trans rfl
theorem new_composite_map (C : NormalForm P) :
    (tagsF C).map (fun a => ((tagged C).e.get ((tagged C).inner.route.get a)).index) = [0,4,1,4,2,3] :=
  (List.map_congr_left (fun a _ => congrArg At.index ((tagged C).square a).symm)).trans
    (old_composite_map C)

theorem outer_retained_indices (C : NormalForm P) :
    ((TraceRoute.full (tagged C).outer.route).fiber (tagged C).x).map At.index = [1,3,6] :=
  (congrArg (List.map At.index) (tagged C).outer.selected_fiber).trans (outer_selected C)
theorem original_retained_indices (C : NormalForm P) :
    ((TraceRoute.full ((tagged C).inner.route.map (tagged C).e.get)).fiber (tagged C).x).map At.index = [1,3] :=
  (congrArg (List.map At.index) (tagged C).new_composite_fiber).trans (inner_selected C)

def fixed0 (C : NormalForm P) : At (tagged C).K C := .here C [C,C,C,C]
def fixed2 (C : NormalForm P) : At (tagged C).K C := .there (.there (.here C [C,C]))
theorem fixed_original_indices (C : NormalForm P) :
    ((tagged C).original (fixed0 C) (by change 0 ≠ 4; decide)).index = 0 ∧
    ((tagged C).original (fixed2 C) (by change 2 ≠ 4; decide)).index = 4 := ⟨rfl,rfl⟩

theorem empty_left :
    ofTerm (newL (tagged (.top : NormalForm Empty)) (Nat.le_refl 2) [.top]
      (W1.SameSideLogical.constantLeft _)).denote =
    ofTerm (oldL (tagged (.top : NormalForm Empty)) (Nat.le_refl 2) [.top]
      (W1.SameSideLogical.constantLeft _)).denote := denoteL ..
theorem empty_right :
    ofTerm (newR (tagged (.bot : NormalForm Empty)) (Nat.le_refl 2) [.bot]
      (W1.SameSideLogical.constantRight _)).denote =
    ofTerm (oldR (tagged (.bot : NormalForm Empty)) (Nat.le_refl 2) [.bot]
      (W1.SameSideLogical.constantRight _)).denote := denoteR ..

theorem empty_exchange_adds_node_left :
    (newL (two (.top : NormalForm Empty)) (Nat.le_refl 2) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (two .top).x =
      rankNewL (two (.top : NormalForm Empty)) (Nat.le_refl 2) [.top]
        (W1.SameSideLogical.constantLeft _)+1 := new_endpointL ..
theorem empty_exchange_adds_node_right :
    (newR (two (.bot : NormalForm Empty)) (Nat.le_refl 2) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (two .bot).x =
      rankNewR (two (.bot : NormalForm Empty)) (Nat.le_refl 2) [.bot]
        (W1.SameSideLogical.constantRight _)+1 := new_endpointR ..

theorem fixed_rank_left :
    (newL (tagged (.top : NormalForm Empty)) (Nat.le_refl 2) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (fixed2 .top) =
    (oldL (tagged (.top : NormalForm Empty)) (Nat.le_refl 2) [.top]
      (W1.SameSideLogical.constantLeft _)).rho .left (fixed2 .top) :=
  fixed_equalL _ _ _ _ _ (by change 2 ≠ 4; decide)
theorem fixed_rank_right :
    (newR (tagged (.bot : NormalForm Empty)) (Nat.le_refl 2) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (fixed0 .bot) =
    (oldR (tagged (.bot : NormalForm Empty)) (Nat.le_refl 2) [.bot]
      (W1.SameSideLogical.constantRight _)).rho .right (fixed0 .bot) :=
  fixed_equalR _ _ _ _ _ (by change 0 ≠ 4; decide)

def compound : NormalForm Empty := .conj .top .bot
def compoundLeft : G Empty (two compound).F [.top] :=
  G.atomize (W1.SameSideLogical.constantLeft _)
def compoundRight : G Empty [.bot] (three compound).F :=
  G.atomize (W1.SameSideLogical.constantRight _)

theorem compound_left :
    ofTerm (newL (two compound) (Nat.le_refl 2) [.top] compoundLeft).denote =
      ofTerm (oldL (two compound) (Nat.le_refl 2) [.top] compoundLeft).denote := denoteL ..
theorem compound_right :
    ofTerm (newR (three compound) (Nat.le_succ 2) [.bot] compoundRight).denote =
      ofTerm (oldR (three compound) (Nat.le_succ 2) [.bot] compoundRight).denote := denoteR ..
theorem compound_atomized_left :
    (newL (two compound) (Nat.le_refl 2) [.top] compoundLeft).Atomized ∧
      ¬ (oldL (two compound) (Nat.le_refl 2) [.top] compoundLeft).Atomized := by
  constructor
  · exact (new_atomizedL ..).mpr (G.atomize_atomized _)
  · intro h
    exact ((old_atomizedL ..).mp h).1
theorem compound_atomized_right :
    (newR (three compound) (Nat.le_succ 2) [.bot] compoundRight).Atomized ∧
      ¬ (oldR (three compound) (Nat.le_succ 2) [.bot] compoundRight).Atomized := by
  constructor
  · exact (new_atomizedR ..).mpr (G.atomize_atomized _)
  · intro h
    exact ((old_atomizedR ..).mp h).1

def literalLeft (l : Literal P) : G P (three (.lit l)).F [.lit l,.lit l,.lit l] :=
  W1.Exchange.repeatedPremiseL l
def literalRight (l : Literal P) : G P [.lit l,.lit l,.lit l] (three (.lit l)).F :=
  W1.Exchange.repeatedPremiseR l
theorem literal_left (l : Literal P) :
    ofTerm (newL (three (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).denote =
      ofTerm (oldL (three (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).denote := denoteL ..
theorem literal_right (l : Literal P) :
    ofTerm (newR (three (.lit l)) (Nat.le_succ 2) _ (literalRight l)).denote =
      ofTerm (oldR (three (.lit l)) (Nat.le_succ 2) _ (literalRight l)).denote := denoteR ..
theorem three_loss_left (l : Literal P) :
    (oldL (three (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).rho .left (three (.lit l)).x =
      (newL (three (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).rho .left (three (.lit l)).x+3 :=
  endpoint_lossL ..
theorem three_loss_right (l : Literal P) :
    (oldR (three (.lit l)) (Nat.le_succ 2) _ (literalRight l)).rho .right (three (.lit l)).x =
      (newR (three (.lit l)) (Nat.le_succ 2) _ (literalRight l)).rho .right (three (.lit l)).x+3 :=
  endpoint_lossR ..
theorem both_signs_actual_cuts (p : P) :
    (newL (three (.lit (.pos p))) (Nat.le_succ 2) _ (literalLeft (.pos p))).cutCount = 1 ∧
    (newR (three (.lit (.neg p))) (Nat.le_succ 2) _ (literalRight (.neg p))).cutCount = 1 :=
  ⟨(new_countL ..).trans rfl,(new_countR ..).trans rfl⟩

end DosenPetric.Reduced.Gentzen.W2.SelectedThinning.Examples
