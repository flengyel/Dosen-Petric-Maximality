module

public import DosenPetric.GentzenOtherMixRanks
public import DosenPetric.GentzenSingleMixExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix.Examples
open SinglePremiseMix.Examples
universe u
variable {P : Type u}
def tagsU (C : NormalForm P) : List (At ([C]++(repeated C [[C],[C]]++[C])) C) :=
  selectedCopies C [[],[],[],[],[],[]] []
theorem selected_indices (C : NormalForm P) :
    (tagged C).selected.map At.index = [1,3] ∧
    ((tagged C).prepend (Nat.le_refl 2) [C]).selected.map At.index = [2,4] := by
  constructor
  · exact (tagged C).selected_indices
  · rw [ContractionBlock.prepend_selected,List.map_map]
    rfl
theorem raw_gaps (C : NormalForm P) :
    ((tagged C).prepend (Nat.le_refl 2) [C]).gs = [[C,C],[C]] :=
  (tagged C).prepend_gaps (Nat.le_refl 2) [C] [C] [[C]] rfl
theorem outer_map (C : NormalForm P) :
    (tagsU C).map (fun a => (((tagged C).prepend (Nat.le_refl 2) [C]).route.get a).index) =
      [0,1,3,2,3,4] := by
  have h := W1.DisjointContraction.Terminal.route_indices
    ((tagged C).prepend (Nat.le_refl 2) [C]) (tagsU C)
  rw [raw_gaps] at h
  exact h.trans rfl

theorem g_map (C : NormalForm P) :
    (SinglePremiseMix.Examples.tagsF C).map
      (fun a => ((OtherMix.newG (tagged C) (Nat.le_refl 2) [C]).get a).map At.index) =
      [some 1,some 3,some 2,some 3,some 4] := by
  have he : (SinglePremiseMix.Examples.tagsF C).map
      (fun a => ((OtherMix.newG (tagged C) (Nat.le_refl 2) [C]).get a).map At.index) =
      (SinglePremiseMix.Examples.tagsF C).map (fun a => some (1+copyIndex (tagged C).gs a.index)) := by
    apply List.map_congr_left
    intro a _
    simp only [OtherMix.newG,TraceRoute.get_ofMap,Option.map_some,At.index_shift,
      ContractionBlock.get_index,List.length_cons,List.length_nil]
  exact he.trans rfl
theorem old_g_map (C : NormalForm P) :
    (SinglePremiseMix.Examples.tagsF C).map
      (fun a => ((OtherMix.oldG (tagged C) (Nat.le_refl 2) [C]).get a).map At.index) =
      [some 1,some 3,some 2,some 3,some 4] := by
  rw [OtherMix.squareG]
  exact g_map C
theorem f_map (C : NormalForm P) :
    ((OtherMix.oldF (tagged C) (Nat.le_refl 2) [C]).get (.here C [])).map At.index = some 0 := by
  rw [OtherMix.squareF,OtherMix.newF,TraceRoute.before,TraceRoute.get_ofMap]
  rfl
theorem retained_fibers (C : NormalForm P) :
    ((OtherMix.oldG (tagged C) (Nat.le_refl 2) [C]).fiber (At.shift [C] (tagged C).keep)).map At.index = [1,3] ∧
    (OtherMix.oldF (tagged C) (Nat.le_refl 2) [C]).fiber (At.shift [C] (tagged C).keep) = [] :=
  ⟨(congrArg (List.map At.index) (OtherMix.old_retained_fibers (tagged C) (Nat.le_refl 2) [C]).1).trans
      (selected_indices C).1,(OtherMix.old_retained_fibers (tagged C) (Nat.le_refl 2) [C]).2⟩
theorem outer_retained_fiber_indices (C : NormalForm P) :
    ((TraceRoute.full ((tagged C).prepend (Nat.le_refl 2) [C]).route).fiber
      (At.shift [C] (tagged C).keep)).map At.index = [2,4] := by
  rw [OtherMix.outer_retained_fiber,List.map_map]
  change (tagged C).selected.map (fun a => 1+a.index) = [2,4]
  exact (List.map_map (f := At.index) (g := fun n => 1+n)).symm.trans
    ((congrArg (List.map (fun n => 1+n)) (selected_indices C).1).trans rfl)
theorem retained_index (C : NormalForm P) :
    (At.shift [C] (tagged C).keep).index = 3 :=
  (OtherMix.retained_index (tagged C) [C]).trans rfl

theorem equal_f_label_not_selected (C : NormalForm P) :
    (At.here C []).before (repeated C [[C],[C]]++[C]) ∉
      ((tagged C).prepend (Nat.le_refl 2) [C]).selected :=
  OtherMix.f_not_selected _ _ _ _

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
      (At.shift [] (two .top).keep) = rankInnerL (two .top) (Nat.le_refl 2) (constLeft .top 2)+1 := new_endpointL ..
theorem three_loss_left :
    (oldL (three (.top : NormalForm Empty)) (Nat.le_succ 2) G.topI (constLeft .top 3)).rho .left
      (At.shift [] (three .top).keep) =
    (newL (three .top) (Nat.le_succ 2) G.topI (constLeft .top 3)).rho .left
      (At.shift [] (three .top).keep)+2 := by
  have h := endpoint_balanceL (three (.top : NormalForm Empty)) (Nat.le_succ 2) G.topI (constLeft .top 3)
  change _+1 = _+3 at h
  omega
theorem three_loss_right :
    (oldR (three (.bot : NormalForm Empty)) (Nat.le_succ 2) G.botE (constRight .bot 3)).rho .right
      (At.shift [] (three .bot).keep) =
    (newR (three .bot) (Nat.le_succ 2) G.botE (constRight .bot 3)).rho .right
      (At.shift [] (three .bot).keep)+2 := by
  have h := endpoint_balanceR (three (.bot : NormalForm Empty)) (Nat.le_succ 2) G.botE (constRight .bot 3)
  change _+1 = _+3 at h
  omega
theorem fixed_f_drops_left (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      ((At.here (.lit l) []).before (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l])) =
    (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      ((At.here (.lit l) []).before (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l]))+1 := by
  have ho := fixed_f_oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l) (.here (.lit l) [])
  have he := fixed_f_newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l) (.here (.lit l) [])
  omega
theorem corrected_opposite_left (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .right
      (At.shift [.lit l] (At.here (.lit l) [])) =
    (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .right
      (At.shift [.lit l] (At.here (.lit l) [])) := opposite_g_equalL ..
theorem corrected_opposite_right (l : Literal P) :
    (oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .left
      (At.shift [.lit l] (At.here (.lit l) [])) =
    (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .left
      (At.shift [.lit l] (At.here (.lit l) [])) := opposite_g_equalR ..
theorem fixed_g_unchanged_left (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      (At.shift [.lit l] (At.here (.lit l) [.lit l,.lit l,.lit l])) =
    (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .left
      (At.shift [.lit l] (At.here (.lit l) [.lit l,.lit l,.lit l])) :=
  (fixed_g_oldL _ _ _ _ _ (by change 0 ≠ 2; decide)).trans
    (fixed_g_newL _ _ _ _ _ (by change 0 ≠ 2; decide)).symm
theorem fixed_f_drops_right (l : Literal P) :
    (oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .right
      ((At.here (.lit l) []).before (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l])) =
    (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .right
      ((At.here (.lit l) []).before (gaps [[.lit l],[.lit l]]++(.lit l)::[.lit l]))+1 := by
  have ho := fixed_f_oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l) (.here (.lit l) [])
  have he := fixed_f_newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l) (.here (.lit l) [])
  omega
theorem old_opposite_not_one (l : Literal P) :
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).rho .right
      (At.shift [.lit l] (At.here (.lit l) [])) ≠ 1+(gLeft l).rho .right (.here (.lit l) []) := by
  have h := opposite_g_oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l) (.here (.lit l) [])
  omega

theorem empty_mix_adds_node_right :
    (newR (three (.bot : NormalForm Empty)) (Nat.le_succ 2) G.botE (constRight .bot 3)).rho .right
      (At.shift [] (three .bot).keep) = rankInnerR (three .bot) (Nat.le_succ 2) (constRight .bot 3)+1 := new_endpointR ..
theorem fixed_g_unchanged_right (l : Literal P) :
    (oldR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .right
      (At.shift [.lit l] (At.here (.lit l) [.lit l,.lit l,.lit l])) =
    (newR (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gRight l)).rho .right
      (At.shift [.lit l] (At.here (.lit l) [.lit l,.lit l,.lit l])) :=
  (fixed_g_oldR _ _ _ _ _ (by change 0 ≠ 2; decide)).trans
    (fixed_g_newR _ _ _ _ _ (by change 0 ≠ 2; decide)).symm
end DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix.Examples
