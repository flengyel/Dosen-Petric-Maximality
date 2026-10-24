module

public import DosenPetric.GentzenSelectedLogicalRanks
public import DosenPetric.GentzenTerminalContractionExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.SelectedLogical.Examples
universe u
variable {P : Type u}

abbrev two (o : Op) (A B : NormalForm P) : Gentzen.SelectedLogical.Data P o := ⟨A,B,[[],[]],[]⟩
abbrev three (o : Op) (A B : NormalForm P) : Gentzen.SelectedLogical.Data P o := ⟨A,B,[[],[],[]],[]⟩
abbrev tagged (o : Op) (A B : NormalForm P) : Gentzen.SelectedLogical.Data P o :=
  ⟨A,B,[[o.formula A B],[o.formula A B]],[o.formula A B,o.formula A B]⟩
def tagsU (o : Op) (A B : NormalForm P) : List (At (tagged o A B).U (o.formula A B)) :=
  selectedCopies (o.formula A B) [[],[],[],[],[],[],[]] []
def tagsJ (o : Op) (A B : NormalForm P) : List (At (tagged o A B).J (o.formula A B)) :=
  selectedCopies (o.formula A B) [[],[],[],[],[],[]] []
def originals (o : Op) (A B : NormalForm P) : List (At (tagged o A B).F (o.formula A B)) :=
  (selectedCopies (o.formula A B) [[],[],[],[],[],[]] []).map (fun a => a.before [A,B])

theorem selections (o : Op) (A B : NormalForm P) :
    (tagged o A B).inner.selected.map At.index = [1,3] ∧
    (tagged o A B).outer.selected.map At.index = [1,3,6] ∧
    (tagged o A B).last.selected.map At.index = [2,5] :=
  ⟨(tagged o A B).inner.selected_indices,(tagged o A B).outer.selected_indices,
    (tagged o A B).last.selected_indices⟩
theorem outer_map (o : Op) (A B : NormalForm P) :
    (tagsU o A B).map (fun a => ((tagged o A B).outer.route.get a).index) = [0,4,1,4,2,3,4] :=
  (W1.DisjointContraction.Terminal.route_indices _ _).trans rfl
theorem last_map (o : Op) (A B : NormalForm P) :
    (tagsJ o A B).map (fun a => ((tagged o A B).last.route.get a).index) = [0,1,4,2,3,4] :=
  (W1.DisjointContraction.Terminal.route_indices _ _).trans rfl
theorem old_partial_map (o : Op) (A B : NormalForm P) :
    (originals o A B).map (fun a => ((tagged o A B).oldTrace.get a).map At.index) =
      [some 0,some 4,some 1,some 4,some 2,some 3] := by
  unfold originals
  rw [List.map_map]
  have he := List.map_congr_left (l := selectedCopies (o.formula A B) [[],[],[],[],[],[]] [])
    (fun a _ => congrArg (Option.map At.index) ((tagged o A B).old_prefix a))
  exact he.trans (by
    apply Eq.trans (List.map_congr_left (fun a _ =>
      congrArg some ((tagged o A B).outer.get_index (a.before [o.formula A B]))))
    rfl)
theorem new_partial_map (o : Op) (A B : NormalForm P) :
    (originals o A B).map (fun a => ((tagged o A B).newTrace.get a).map At.index) =
      [some 0,some 4,some 1,some 4,some 2,some 3] :=
  (List.map_congr_left (fun a _ => congrArg (Option.map At.index) ((tagged o A B).trace_square a).symm)).trans
    (old_partial_map o A B)
theorem both_consumed (o : Op) (T : NormalForm P) :
    (tagged o T T).uParent (tagged o T T).a = none ∧
    (tagged o T T).uParent (tagged o T T).b = none ∧
    (tagged o T T).a ≠ (tagged o T T).b := by
  refine ⟨(tagged o T T).consumed_a,(tagged o T T).consumed_b,?_⟩
  intro he
  have hi := congrArg At.index he
  change 6 = 7 at hi
  omega
theorem complete_fibers (o : Op) (A B : NormalForm P) :
    ((tagged o A B).oldTrace.fiber (tagged o A B).x).map At.index = [1,3] ∧
    ((tagged o A B).newTrace.fiber (tagged o A B).x).map At.index = [1,3] :=
  ⟨(congrArg (List.map At.index) (tagged o A B).old_retained_fiber).trans (selections o A B).1,
    (congrArg (List.map At.index) (tagged o A B).new_retained_fiber).trans (selections o A B).1⟩

def fixed0 (o : Op) (A B : NormalForm P) : At (tagged o A B).K (o.formula A B) :=
  .here _ [o.formula A B,o.formula A B,o.formula A B,o.formula A B]
theorem fixed_original (o : Op) (A B : NormalForm P) :
    ((tagged o A B).original (fixed0 o A B) (by change 0 ≠ 4; decide)).index = 0 := rfl

def constLeft (d : Gentzen.SelectedLogical.Data Empty .conj) : G Empty d.F [.top] :=
  G.atomize (W1.SameSideLogical.constantLeft _)
def constRight (d : Gentzen.SelectedLogical.Data Empty .disj) : G Empty [.bot] d.F :=
  G.atomize (W1.SameSideLogical.constantRight _)
theorem empty_left :
    ofTerm (newL (two .conj (.top : NormalForm Empty) .top) (Nat.le_refl 2) _ (constLeft _)).denote =
      ofTerm (oldL (two .conj .top .top) (Nat.le_refl 2) _ (constLeft _)).denote := denoteL ..
theorem empty_right :
    ofTerm (newR (two .disj (.bot : NormalForm Empty) .bot) (Nat.le_refl 2) _ (constRight _)).denote =
      ofTerm (oldR (two .disj .bot .bot) (Nat.le_refl 2) _ (constRight _)).denote := denoteR ..
theorem tie_left :
    (newL (two .conj (.top : NormalForm Empty) .top) (Nat.le_refl 2) _ (constLeft _)).rho .left (two .conj .top .top).x =
      (oldL (two .conj .top .top) (Nat.le_refl 2) _ (constLeft _)).rho .left (two .conj .top .top).x := endpoint_tieL _ _ _ _ rfl
theorem tie_right :
    (newR (two .disj (.bot : NormalForm Empty) .bot) (Nat.le_refl 2) _ (constRight _)).rho .right (two .disj .bot .bot).x =
      (oldR (two .disj .bot .bot) (Nat.le_refl 2) _ (constRight _)).rho .right (two .disj .bot .bot).x := endpoint_tieR _ _ _ _ rfl
theorem fixed_increase_left :
    (newL (tagged .conj (.top : NormalForm Empty) .top) (Nat.le_refl 2) _ (constLeft _)).rho .left (fixed0 .conj .top .top) =
      (oldL (tagged .conj .top .top) (Nat.le_refl 2) _ (constLeft _)).rho .left (fixed0 .conj .top .top)+1 :=
  fixed_increasesL _ _ _ _ _ (by change 0 ≠ 4; decide)
theorem fixed_increase_right :
    (newR (tagged .disj (.bot : NormalForm Empty) .bot) (Nat.le_refl 2) _ (constRight _)).rho .right (fixed0 .disj .bot .bot) =
      (oldR (tagged .disj .bot .bot) (Nat.le_refl 2) _ (constRight _)).rho .right (fixed0 .disj .bot .bot)+1 :=
  fixed_increasesR _ _ _ _ _ (by change 0 ≠ 4; decide)
theorem compound_atomized_left :
    (oldL (two .conj (.top : NormalForm Empty) .bot) (Nat.le_refl 2) _ (constLeft _)).Atomized ∧
      (newL (two .conj .top .bot) (Nat.le_refl 2) _ (constLeft _)).Atomized :=
  ⟨(old_atomizedL ..).mpr (G.atomize_atomized _),(new_atomizedL ..).mpr (G.atomize_atomized _)⟩
theorem compound_atomized_right :
    (oldR (two .disj (.top : NormalForm Empty) .bot) (Nat.le_refl 2) _ (constRight _)).Atomized ∧
      (newR (two .disj .top .bot) (Nat.le_refl 2) _ (constRight _)).Atomized :=
  ⟨(old_atomizedR ..).mpr (G.atomize_atomized _),(new_atomizedR ..).mpr (G.atomize_atomized _)⟩
theorem compound_components_left :
    ofTerm (newL (three .conj (.conj (.top : NormalForm Empty) .bot) (.disj .bot .top))
      (Nat.le_succ 2) _ (constLeft _)).denote = ofTerm (oldL (three .conj (.conj .top .bot) (.disj .bot .top))
      (Nat.le_succ 2) _ (constLeft _)).denote := denoteL ..
theorem compound_components_right :
    ofTerm (newR (three .disj (.conj (.top : NormalForm Empty) .bot) (.disj .bot .top))
      (Nat.le_succ 2) _ (constRight _)).denote = ofTerm (oldR (three .disj (.conj .top .bot) (.disj .bot .top))
      (Nat.le_succ 2) _ (constRight _)).denote := denoteR ..

def prefixL {Γ Δ : List (NormalForm P)} (Ξ : List (NormalForm P)) (f : G P Γ Δ) : G P (Ξ++Γ) Δ :=
  match Ξ with
  | [] => f
  | A::Ξ => G.thinL [] (Ξ++Γ) Δ A (prefixL Ξ f)
def prefixR {Γ Δ : List (NormalForm P)} (Ξ : List (NormalForm P)) (f : G P Γ Δ) : G P Γ (Ξ++Δ) :=
  match Ξ with
  | [] => f
  | A::Ξ => G.thinR Γ [] (Ξ++Δ) A (prefixR Ξ f)
def literalLeft (l : Literal P) : G P (three .conj (.lit l) (.lit l)).F [.lit l] :=
  prefixL [.conj (.lit l) (.lit l),.conj (.lit l) (.lit l),.conj (.lit l) (.lit l)] (W1.cutPremiseL l)
def literalRight (l : Literal P) : G P [.lit l] (three .disj (.lit l) (.lit l)).F :=
  prefixR [.disj (.lit l) (.lit l),.disj (.lit l) (.lit l),.disj (.lit l) (.lit l)] (W1.cutPremiseR l)
theorem literal_left (l : Literal P) :
    ofTerm (newL (three .conj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).denote =
      ofTerm (oldL (three .conj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).denote := denoteL ..
theorem literal_right (l : Literal P) :
    ofTerm (newR (three .disj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalRight l)).denote =
      ofTerm (oldR (three .disj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalRight l)).denote := denoteR ..
theorem both_signs_actual_cuts (p : P) :
    (newL (three .conj (.lit (.pos p)) (.lit (.pos p))) (Nat.le_succ 2) _ (literalLeft (.pos p))).cutCount = 1 ∧
    (newR (three .disj (.lit (.neg p)) (.lit (.neg p))) (Nat.le_succ 2) _ (literalRight (.neg p))).cutCount = 1 :=
  ⟨(new_countL ..).trans rfl,(new_countR ..).trans rfl⟩
theorem three_strict_left (l : Literal P) :
    (newL (three .conj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).rho .left (three .conj (.lit l) (.lit l)).x <
      (oldL (three .conj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalLeft l)).rho .left (three .conj (.lit l) (.lit l)).x :=
  endpoint_decreasesL _ _ _ _ (Nat.le_refl 3)
theorem three_strict_right (l : Literal P) :
    (newR (three .disj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalRight l)).rho .right (three .disj (.lit l) (.lit l)).x <
      (oldR (three .disj (.lit l) (.lit l)) (Nat.le_succ 2) _ (literalRight l)).rho .right (three .disj (.lit l) (.lit l)).x :=
  endpoint_decreasesR _ _ _ _ (Nat.le_refl 3)
end DosenPetric.Reduced.Gentzen.W4.SelectedLogical.Examples
