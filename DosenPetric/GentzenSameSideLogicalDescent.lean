module

public import DosenPetric.GentzenSameSideLogicalReplacement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Inherit cleanliness and lower rank at the actual conjL before predecessor. -/
theorem same_conjL_before_descent {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At F C)
    (hc : Clean f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U))) :
    Clean f x g (a.before (A :: B :: U)) ∧ rank f x g (a.before (A :: B :: U)) < rank f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)) := by
  let b : Upper (G.conjL F U Λ A B g) .left C := ⟨⟨_,_,g,Premise.conjL F U Λ A B g⟩,a.before (A :: B :: U)⟩
  have hb : (G.conjL F U Λ A B g).IsPredecessor .left (a.before (.conj A B :: U)) b := At.fixed_before F [A,B] [.conj A B] U a
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor f x _ (a.before (.conj A B :: U)) b hb⟩

/-- Inherit cleanliness and lower rank at the actual conjL tail predecessor. -/
theorem same_conjL_tail_descent {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At U C)
    (hc : Clean f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a))) :
    Clean f x g (At.shift F (At.shift [A,B] a)) ∧ rank f x g (At.shift F (At.shift [A,B] a)) < rank f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)) := by
  let b : Upper (G.conjL F U Λ A B g) .left C := ⟨⟨_,_,g,Premise.conjL F U Λ A B g⟩,At.shift F (At.shift [A,B] a)⟩
  have hb : (G.conjL F U Λ A B g).IsPredecessor .left (At.shift F (At.shift [.conj A B] a)) b := At.fixed_tail F [A,B] [.conj A B] U a
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor f x _ (At.shift F (At.shift [.conj A B] a)) b hb⟩

/-- Inherit cleanliness and lower rank at the actual disjR before predecessor. -/
theorem same_disjR_before_descent {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At F C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y) :
    Clean f (a.before (A :: B :: U)) g y ∧ rank f (a.before (A :: B :: U)) g y < rank (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y := by
  let b : Upper (G.disjR Γ F U A B f) .right C := ⟨⟨_,_,f,Premise.disjR Γ F U A B f⟩,a.before (A :: B :: U)⟩
  have hb : (G.disjR Γ F U A B f).IsPredecessor .right (a.before (.disj A B :: U)) b := At.fixed_before F [A,B] [.disj A B] U a
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ (a.before (.disj A B :: U)) g y b hb⟩

/-- Inherit cleanliness and lower rank at the actual disjR tail predecessor. -/
theorem same_disjR_tail_descent {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At U C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y) :
    Clean f (At.shift F (At.shift [A,B] a)) g y ∧ rank f (At.shift F (At.shift [A,B] a)) g y < rank (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y := by
  let b : Upper (G.disjR Γ F U A B f) .right C := ⟨⟨_,_,f,Premise.disjR Γ F U A B f⟩,At.shift F (At.shift [A,B] a)⟩
  have hb : (G.disjR Γ F U A B f).IsPredecessor .right (At.shift F (At.shift [.disj A B] a)) b := At.fixed_tail F [A,B] [.disj A B] U a
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ (At.shift F (At.shift [.disj A B] a)) g y b hb⟩

end PositionalCut
namespace CutCommutation

/-- Apply the rank hypothesis before routing the conjL before child to the head. -/
theorem same_conjL_before_rank_step {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At F C)
    (hc : PositionalCut.Clean f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)))
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)) := by
  have hd := PositionalCut.same_conjL_before_descent f x g a hc
  exact same_conjL_before_eliminated f x g a (ih f x g (a.before (A :: B :: U)) hd.2 hd.1)

/-- Apply the rank hypothesis before routing the conjL tail child to the head. -/
theorem same_conjL_tail_rank_step {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At U C)
    (hc : PositionalCut.Clean f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)))
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)) := by
  have hd := PositionalCut.same_conjL_tail_descent f x g a hc
  exact same_conjL_tail_eliminated f x g a (ih f x g (At.shift F (At.shift [A,B] a)) hd.2 hd.1)

/-- Apply the rank hypothesis before routing the disjR before child to the head. -/
theorem same_disjR_before_rank_step {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At F C) (g : G P Θ Λ) (y : At Θ C)
    (hc : PositionalCut.Clean (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y)
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y := by
  have hd := PositionalCut.same_disjR_before_descent f a g y hc
  exact same_disjR_before_eliminated f a g y (ih f (a.before (A :: B :: U)) g y hd.2 hd.1)

/-- Apply the rank hypothesis before routing the disjR tail child to the head. -/
theorem same_disjR_tail_rank_step {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At U C) (g : G P Θ Λ) (y : At Θ C)
    (hc : PositionalCut.Clean (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y)
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y := by
  have hd := PositionalCut.same_disjR_tail_descent f a g y hc
  exact same_disjR_tail_eliminated f a g y (ih f (At.shift F (At.shift [A,B] a)) g y hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
