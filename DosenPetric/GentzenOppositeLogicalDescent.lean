module

public import DosenPetric.GentzenCutOppositeDisjunction
public import DosenPetric.GentzenSelectedRecursion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

theorem opposite_conjL_descent {F U Δ Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F ++ A :: B :: U) Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean (G.conjL F U Δ A B f) x g y) :
    Clean f x g y ∧ rank f x g y < rank (G.conjL F U Δ A B f) x g y := by
  let a : Upper (G.conjL F U Δ A B f) .right C := ⟨⟨_,_,f,Premise.conjL F U Δ A B f⟩,x⟩
  have ha : (G.conjL F U Δ A B f).IsPredecessor .right x a := rfl
  exact ⟨clean_left_predecessor hc a ha,rank_left_predecessor _ x g y a ha⟩

theorem opposite_disjR_descent {Γ Δ Θ F U : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ (F ++ A :: B :: U)) (y : At Θ C)
    (hc : Clean f x (G.disjR Θ F U A B g) y) :
    Clean f x g y ∧ rank f x g y < rank f x (G.disjR Θ F U A B g) y := by
  let a : Upper (G.disjR Θ F U A B g) .left C := ⟨⟨_,_,g,Premise.disjR Θ F U A B g⟩,y⟩
  have ha : (G.disjR Θ F U A B g).IsPredecessor .left y a := rfl
  exact ⟨clean_right_predecessor hc a ha,rank_right_predecessor f x _ y a ha⟩

end PositionalCut
namespace CutCommutation

/-- The conjunction-left branch of the inner clean selected-rank induction. -/
theorem opposite_conjL_rank_step {F U Δ Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F ++ A :: B :: U) Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : PositionalCut.Clean (G.conjL F U Δ A B f) x g y)
    (ih : ∀ {I J K L : List (NormalForm P)} (a : G P I J) (v : At J C)
      (b : G P K L) (w : At K C),
      PositionalCut.rank a v b w < PositionalCut.rank (G.conjL F U Δ A B f) x g y →
      PositionalCut.Clean a v b w → PositionalCut.Eliminated a v b w) :
    PositionalCut.Eliminated (G.conjL F U Δ A B f) x g y := by
  have hd := PositionalCut.opposite_conjL_descent f x g y hc
  exact opposite_conjL_eliminated f x g y (ih f x g y hd.2 hd.1)

/-- The disjunction-right branch with its own exact context indices. -/
theorem opposite_disjR_rank_step {Γ Δ Θ F U : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ (F ++ A :: B :: U)) (y : At Θ C)
    (hc : PositionalCut.Clean f x (G.disjR Θ F U A B g) y)
    (ih : ∀ {I J K L : List (NormalForm P)} (a : G P I J) (v : At J C)
      (b : G P K L) (w : At K C),
      PositionalCut.rank a v b w < PositionalCut.rank f x (G.disjR Θ F U A B g) y →
      PositionalCut.Clean a v b w → PositionalCut.Eliminated a v b w) :
    PositionalCut.Eliminated f x (G.disjR Θ F U A B g) y := by
  have hd := PositionalCut.opposite_disjR_descent f x g y hc
  exact opposite_disjR_eliminated f x g y (ih f x g y hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
