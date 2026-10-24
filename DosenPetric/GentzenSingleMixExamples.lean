module

public import DosenPetric.GentzenSingleMixRanks
public import DosenPetric.GentzenSelectedLogicalExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.SinglePremiseMix.Examples
universe u
variable {P : Type u}
abbrev two (C : NormalForm P) := block C [[],[]] []
abbrev three (C : NormalForm P) := block C [[],[],[]] []
abbrev tagged (C : NormalForm P) := block C [[C],[C]] [C]
def tagsF (C : NormalForm P) : List (At (repeated C [[C],[C]]++[C]) C) :=
  selectedCopies C [[],[],[],[],[]] []
def tagsU (C : NormalForm P) : List (At ((repeated C [[C],[C]]++[C])++[C]) C) :=
  selectedCopies C [[],[],[],[],[],[]] []
theorem selected_indices (C : NormalForm P) :
    (tagged C).selected.map At.index = [1,3] ∧
    ((tagged C).extend [C]).selected.map At.index = [1,3] :=
  ⟨(tagged C).selected_indices,((tagged C).extend [C]).selected_indices⟩
theorem outer_map (C : NormalForm P) :
    (tagsU C).map (fun a => (((tagged C).extend [C]).route.get a).index) = [0,2,1,2,3,4] :=
  (W1.DisjointContraction.Terminal.route_indices _ _).trans rfl
theorem g_map (C : NormalForm P) :
    (tagsF C).map (fun a => ((SingleMix.newG (tagged C) [C]).get a).map At.index) =
      [some 0,some 2,some 1,some 2,some 3] := by
  have he : (tagsF C).map (fun a => ((SingleMix.newG (tagged C) [C]).get a).map At.index) =
      (tagsF C).map (fun a => some (copyIndex (tagged C).gs a.index)) := by
    apply List.map_congr_left
    intro a _
    simp only [SingleMix.newG,TraceRoute.get_ofMap,Option.map_some,At.index_before,ContractionBlock.get_index]
  exact he.trans rfl
theorem old_g_map (C : NormalForm P) :
    (tagsF C).map (fun a => ((SingleMix.oldG (tagged C) [C]).get a).map At.index) =
      [some 0,some 2,some 1,some 2,some 3] := by
  rw [SingleMix.squareG]
  exact g_map C
theorem f_map (C : NormalForm P) :
    ((SingleMix.oldF (tagged C) [C]).get (.here C [])).map At.index = some 4 := by
  rw [SingleMix.squareF,SingleMix.newF,TraceRoute.shift,TraceRoute.get_ofMap]
  rfl
theorem retained_fibers (C : NormalForm P) :
    ((SingleMix.oldG (tagged C) [C]).fiber ((tagged C).keep.before [C])).map At.index = [1,3] ∧
    (SingleMix.oldF (tagged C) [C]).fiber ((tagged C).keep.before [C]) = [] :=
  ⟨(congrArg (List.map At.index) (SingleMix.old_retained_fibers (tagged C) [C]).1).trans
      (selected_indices C).1,(SingleMix.old_retained_fibers (tagged C) [C]).2⟩
theorem equal_f_label_not_selected (C : NormalForm P) :
    At.shift (repeated C [[C],[C]]++[C]) (.here C []) ∉ ((tagged C).extend [C]).selected :=
  SingleMix.f_not_selected _ _ _

def cutIdentity (l : Literal P) : G P [.lit l] [.lit l] := G.cut (G.identity l) (G.identity l)
def gLeft (l : Literal P) : G P (repeated (.lit l) [[.lit l],[.lit l]]++[.lit l]) [.lit l] :=
  W4.SelectedLogical.Examples.prefixL [.lit l,.lit l,.lit l,.lit l] (cutIdentity l)
def gRight (l : Literal P) : G P [.lit l] (repeated (.lit l) [[.lit l],[.lit l]]++[.lit l]) :=
  W4.SelectedLogical.Examples.prefixR [.lit l,.lit l,.lit l,.lit l] (cutIdentity l)
theorem literal_left (l : Literal P) :
    ofTerm (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).denote =
      ofTerm (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).denote := denoteL ..
theorem literal_right (l : Literal P) :
    ofTerm (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).denote =
      ofTerm (oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).denote := denoteR ..
theorem both_signs_two_actual_cuts (p : P) :
    (newL (tagged (.lit (.pos p))) (Nat.le_refl 2) (cutIdentity (.pos p)) (gLeft (.pos p))).cutCount = 2 ∧
    (newR (tagged (.lit (.neg p))) (Nat.le_refl 2) (cutIdentity (.neg p)) (gRight (.neg p))).cutCount = 2 :=
  ⟨(new_countL ..).trans rfl,(new_countR ..).trans rfl⟩
theorem only_g_cut (l : Literal P) :
    (newL (tagged (.lit l)) (Nat.le_refl 2) (G.identity l) (gLeft l)).cutCount = 1 :=
  (new_countL ..).trans rfl
theorem only_f_cut (l : Literal P) :
    (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l)
      (W4.SelectedLogical.Examples.prefixR [.lit l,.lit l,.lit l,.lit l] (G.identity l))).cutCount = 1 :=
  (new_countR ..).trans rfl

def constLeft (C : NormalForm Empty) (n : Nat) :
    G Empty (List.replicate n C) [.top] := G.atomize (W1.SameSideLogical.constantLeft _)
def constRight (C : NormalForm Empty) (n : Nat) :
    G Empty [.bot] (List.replicate n C) := G.atomize (W1.SameSideLogical.constantRight _)
theorem empty_f_source_left :
    ofTerm (newL (two (.top : NormalForm Empty)) (Nat.le_refl 2) G.topI (constLeft .top 2)).denote =
      ofTerm (oldL (two .top) (Nat.le_refl 2) G.topI (constLeft .top 2)).denote := denoteL ..
theorem empty_f_target_right :
    ofTerm (newR (two (.bot : NormalForm Empty)) (Nat.le_refl 2) G.botE (constRight .bot 2)).denote =
      ofTerm (oldR (two .bot) (Nat.le_refl 2) G.botE (constRight .bot 2)).denote := denoteR ..
theorem compound_atomized_left :
    (newL (three (.conj (.top : NormalForm Empty) .bot)) (Nat.le_succ 2)
      (G.atomize (W1.SameSideLogical.constantLeft [.top])) (constLeft (.conj .top .bot) 3)).Atomized :=
  (new_atomizedL ..).mpr ⟨G.atomize_atomized _,G.atomize_atomized _⟩
theorem compound_atomized_right :
    (newR (three (.disj (.top : NormalForm Empty) .bot)) (Nat.le_succ 2)
      (G.atomize (W1.SameSideLogical.constantRight [.bot])) (constRight (.disj .top .bot) 3)).Atomized :=
  (new_atomizedR ..).mpr ⟨G.atomize_atomized _,G.atomize_atomized _⟩
theorem compound_equality_left :
    ofTerm (newL (three (.conj (.top : NormalForm Empty) .bot)) (Nat.le_succ 2)
      (G.atomize (W1.SameSideLogical.constantLeft [.top])) (constLeft (.conj .top .bot) 3)).denote =
    ofTerm (oldL (three (.conj .top .bot)) (Nat.le_succ 2)
      (G.atomize (W1.SameSideLogical.constantLeft [.top])) (constLeft (.conj .top .bot) 3)).denote := denoteL ..
theorem compound_equality_right :
    ofTerm (newR (three (.disj (.top : NormalForm Empty) .bot)) (Nat.le_succ 2)
      (G.atomize (W1.SameSideLogical.constantRight [.bot])) (constRight (.disj .top .bot) 3)).denote =
    ofTerm (oldR (three (.disj .top .bot)) (Nat.le_succ 2)
      (G.atomize (W1.SameSideLogical.constantRight [.bot])) (constRight (.disj .top .bot) 3)).denote := denoteR ..
theorem empty_mix_adds_node :
    (newL (two (.top : NormalForm Empty)) (Nat.le_refl 2) G.topI (constLeft .top 2)).rho .left
      ((two .top).keep.before []) = rankInnerL (two .top) (Nat.le_refl 2) (constLeft .top 2)+1 := new_endpointL ..
theorem three_loss_left :
    (oldL (three (.top : NormalForm Empty)) (Nat.le_succ 2) G.topI (constLeft .top 3)).rho .left
      ((three .top).keep.before []) =
    (newL (three .top) (Nat.le_succ 2) G.topI (constLeft .top 3)).rho .left
      ((three .top).keep.before [])+2 := by
  have h := endpoint_balanceL (three (.top : NormalForm Empty)) (Nat.le_succ 2) G.topI (constLeft .top 3)
  change _+1 = _+3 at h
  omega
theorem three_loss_right :
    (oldR (three (.bot : NormalForm Empty)) (Nat.le_succ 2) G.botE (constRight .bot 3)).rho .right
      ((three .bot).keep.before []) =
    (newR (three .bot) (Nat.le_succ 2) G.botE (constRight .bot 3)).rho .right
      ((three .bot).keep.before [])+2 := by
  have h := endpoint_balanceR (three (.bot : NormalForm Empty)) (Nat.le_succ 2) G.botE (constRight .bot 3)
  change _+1 = _+3 at h
  omega
theorem fixed_f_drops_left (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      (At.shift (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l]) (.here (.lit l) [])) =
    (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      (At.shift (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l]) (.here (.lit l) []))+1 := by
  have ho := fixed_f_oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l) (.here (.lit l) [])
  have he := fixed_f_newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l) (.here (.lit l) [])
  omega
theorem corrected_opposite_left (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .right
      ((At.here (.lit l) []).before [.lit l]) =
    (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .right
      ((At.here (.lit l) []).before [.lit l]) := opposite_g_equalL ..
theorem corrected_opposite_right (l : Literal P) :
    (oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .left
      ((At.here (.lit l) []).before [.lit l]) =
    (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .left
      ((At.here (.lit l) []).before [.lit l]) := opposite_g_equalR ..
theorem fixed_g_unchanged_left (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      ((At.here (.lit l) [.lit l,.lit l,.lit l]).before [.lit l]) =
    (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      ((At.here (.lit l) [.lit l,.lit l,.lit l]).before [.lit l]) :=
  (fixed_g_oldL _ _ _ _ _ (by change 0 ≠ 2; decide)).trans
    (fixed_g_newL _ _ _ _ _ (by change 0 ≠ 2; decide)).symm
theorem fixed_f_drops_right (l : Literal P) :
    (oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .right
      (At.shift (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l]) (.here (.lit l) [])) =
    (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .right
      (At.shift (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l]) (.here (.lit l) []))+1 := by
  have ho := fixed_f_oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l) (.here (.lit l) [])
  have he := fixed_f_newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l) (.here (.lit l) [])
  omega
theorem old_opposite_not_one (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .right
      ((At.here (.lit l) []).before [.lit l]) ≠ 1+(gLeft l).rho .right (.here (.lit l) []) := by
  have h := opposite_g_oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l) (.here (.lit l) [])
  omega
end DosenPetric.Reduced.Gentzen.W5.SinglePremiseMix.Examples
