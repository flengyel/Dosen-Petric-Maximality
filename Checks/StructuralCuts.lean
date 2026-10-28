module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C) :
    ofTerm (PositionalCut.cut (p.right f) x g z).denote =
      ofTerm (((p.residual x y h).prefixFixed Λ).right (PositionalCut.cut f y g z)).denote :=
  CutCommutation.same_right p x y h f g z

example {P : Type u} {F U Γ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ Δ) (z : At Δ C) (g : G P U Λ) :
    ofTerm (PositionalCut.cut f z (p.left g) x).denote =
      ofTerm (((p.residual x y h).suffixFixed Γ).left (PositionalCut.cut f z g y)).denote :=
  CutCommutation.same_left p x y h f z g

example {P : Type u} {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (x : At F C) (y : At U C)
    (hy : p.get y = x) (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C)
    (hc : PositionalCut.Clean (p.right f) x g z) :
    PositionalCut.Clean f y g z ∧
      PositionalCut.rank f y g z < PositionalCut.rank (p.right f) x g z :=
  ⟨PositionalCut.clean_same_right p x y hy f g z hc,
    PositionalCut.rank_same_right p hp x y hy f g z⟩

example {P : Type u} (F X Y U : List (NormalForm P)) {C : NormalForm P}
    (y : At (F ++ X ++ Y ++ U) C) :
    (.exchange F X Y U : StructuralProgram P _ _).route.SingleFiber
      (y.swapBlocks F X Y U) y := StructuralProgram.exchange_singleFiber F X Y U y

example {P : Type u} (F U : List (NormalForm P)) (E : NormalForm P)
    {C : NormalForm P} (y : At (F ++ U) C) :
    (.thin F U E : StructuralProgram P _ _).route.SingleFiber ((Route.thin F U E).get y) y :=
  StructuralProgram.thin_singleFiber F U E y

example {P : Type u} (C : NormalForm P) :
    (.contract C [[C],[],[]] [] (by change 2 ≤ 3; decide) : StructuralProgram P _ _).route.SingleFiber
      (.here C [C]) (fixedCopyAt C [[C],[],[]] [] (.here C [C]) (by change 0 ≠ 1; decide)) :=
  StructuralProgram.contract_singleFiber C [[C],[],[]] [] (by change 2 ≤ 3; decide) (.here C [C]) (by change 0 ≠ 1; decide)

example {P : Type u} {F U Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (f : G P U Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) (hc : PositionalCut.Clean (p.left f) x g y) :
    PositionalCut.Clean f x g y ∧
      PositionalCut.rank f x g y < PositionalCut.rank (p.left f) x g y :=
  PositionalCut.selected_opposite_left_descent p hp f x g y hc

example : (StructuralProgram.exchange [] [] [] [] : StructuralProgram Empty [] []).steps = 1 := rfl

#check CutCommutation.same_right_rank_step
#check CutCommutation.same_left_rank_step
#print axioms Route.residual_square
#print axioms CutCommutation.same_right
#print axioms CutCommutation.same_left
#print axioms CutCommutation.same_right_rank_step
#print axioms CutCommutation.same_left_rank_step
#print axioms CutCommutation.selected_opposite_left
#print axioms CutCommutation.selected_opposite_right
