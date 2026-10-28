module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.PositionalCut

example {P : Type u} {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At F C)
    (hc : PositionalCut.Clean f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)))
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)) :=
  CutCommutation.same_conjL_before_rank_step f x g a hc ih

example {P : Type u} {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At U C)
    (hc : PositionalCut.Clean f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)))
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)) :=
  CutCommutation.same_conjL_tail_rank_step f x g a hc ih

example {P : Type u} {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At F C) (g : G P Θ Λ) (y : At Θ C)
    (hc : PositionalCut.Clean (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y)
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y :=
  CutCommutation.same_disjR_before_rank_step f a g y hc ih

example {P : Type u} {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At U C) (g : G P Θ Λ) (y : At Θ C)
    (hc : PositionalCut.Clean (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y)
    (ih : ∀ {I J K L : List (NormalForm P)} (b : G P I J) (v : At J C)
      (d : G P K L) (w : At K C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y :=
  CutCommutation.same_disjR_tail_rank_step f a g y hc ih

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.mix f g) (At.shift Λ a) h z) :
    Clean f (a) h z ∧ rank f (a) h z < rank (G.mix f g) (At.shift Λ a) h z :=
  PositionalCut.mix_left_first_descent f g a h z hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.mix f g) (a.before Δ) h z) :
    Clean g (a) h z ∧ rank g (a) h z < rank (G.mix f g) (a.before Δ) h z :=
  PositionalCut.mix_left_second_descent f g a h z hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : Clean h z (G.mix f g) (At.shift Θ a)) :
    Clean h z f (a) ∧ rank h z f (a) < rank h z (G.mix f g) (At.shift Θ a) :=
  PositionalCut.mix_right_first_descent f g h z a hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : Clean h z (G.mix f g) (a.before Γ)) :
    Clean h z g (a) ∧ rank h z g (a) < rank h z (G.mix f g) (a.before Γ) :=
  PositionalCut.mix_right_second_descent f g h z a hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.conjR f g) ((a.before Λ).there) h z) :
    Clean f (a.there) h z ∧ rank f (a.there) h z < rank (G.conjR f g) ((a.before Λ).there) h z :=
  PositionalCut.conjR_left_first_descent f g a h z hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.conjR f g) ((At.shift Δ a).there) h z) :
    Clean g (a.there) h z ∧ rank g (a.there) h z < rank (G.conjR f g) ((At.shift Δ a).there) h z :=
  PositionalCut.conjR_left_second_descent f g a h z hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : Clean h z (G.conjR f g) (a.before Θ)) :
    Clean h z f (a) ∧ rank h z f (a) < rank h z (G.conjR f g) (a.before Θ) :=
  PositionalCut.conjR_right_first_descent f g h z a hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : Clean h z (G.conjR f g) (At.shift Γ a)) :
    Clean h z g (a) ∧ rank h z g (a) < rank h z (G.conjR f g) (At.shift Γ a) :=
  PositionalCut.conjR_right_second_descent f g h z a hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.disjL f g) (a.before Λ) h z) :
    Clean f (a) h z ∧ rank f (a) h z < rank (G.disjL f g) (a.before Λ) h z :=
  PositionalCut.disjL_left_first_descent f g a h z hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.disjL f g) (At.shift Δ a) h z) :
    Clean g (a) h z ∧ rank g (a) h z < rank (G.disjL f g) (At.shift Δ a) h z :=
  PositionalCut.disjL_left_second_descent f g a h z hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : Clean h z (G.disjL f g) ((a.before Θ).there)) :
    Clean h z f (a.there) ∧ rank h z f (a.there) < rank h z (G.disjL f g) ((a.before Θ).there) :=
  PositionalCut.disjL_right_first_descent f g h z a hc

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : Clean h z (G.disjL f g) ((At.shift Γ a).there)) :
    Clean h z g (a.there) ∧ rank h z g (a.there) < rank h z (G.disjL f g) ((At.shift Γ a).there) :=
  PositionalCut.disjL_right_second_descent f g h z a hc

example {P : Type u} {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At F C) :
    ofTerm (PositionalCut.cut f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U))).denote =
      ofTerm (SameSideLogical.conjBefore a
        (PositionalCut.cut f x g (a.before (A :: B :: U)))).denote :=
  CutCommutation.same_conjL_before f x g a

example {P : Type u} {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At F C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y).denote =
      ofTerm (SameSideLogical.disjBefore a
        (PositionalCut.cut f (a.before (A :: B :: U)) g y)).denote :=
  CutCommutation.same_disjR_before f a g y

example {P : Type u} {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At U C) :
    ofTerm (PositionalCut.cut f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a))).denote =
      ofTerm (SameSideLogical.conjTail a
        (PositionalCut.cut f x g (At.shift F (At.shift [A,B] a)))).denote :=
  CutCommutation.same_conjL_tail f x g a

example {P : Type u} {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At U C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y).denote =
      ofTerm (SameSideLogical.disjTail a
        (PositionalCut.cut f (At.shift F (At.shift [A,B] a)) g y)).denote :=
  CutCommutation.same_disjR_tail f a g y

-- Repeated labels retain distinct occurrence tags, including compound labels.
example {P : Type u} (o : Op) (A : NormalForm P) :
    ((LogicalDeletion.headBefore (.there (.here (o.formula A A) [])) [o.formula A A]).get
      (.here (o.formula A A) [o.formula A A,o.formula A A])).index = 1 := by
  rw [LogicalDeletion.headBefore_index]
  rfl

example {P : Type u} (o : Op) (A : NormalForm P) :
    ((LogicalDeletion.headUnder [] [o.formula A A]
      (.there (.here (o.formula A A) []))).get
      (.here (o.formula A A) [o.formula A A,o.formula A A])).index = 1 := by
  rw [LogicalDeletion.headUnder_index]
  rfl

-- Negative literals and empty prefix are allowed in the actual logical square.
example (p : Nat) :
    (side Nat .disj).comp
      ((LogicalDeletion.headUnder [] [.disj (.lit (.neg p)) (.lit (.neg p))]
        (.here (.lit (.neg p)) [])).arrow .disj)
      (logicalSide .disj [] [.lit (.neg p)] (.lit (.neg p)) (.lit (.neg p))) =
    (side Nat .disj).comp
      ((sideM Nat .disj).tensor ((side Nat .disj).id (.lit (.neg p)))
        (logicalSide .disj [] [] (.lit (.neg p)) (.lit (.neg p))))
      ((LogicalDeletion.headUnder [] [.lit (.neg p),.lit (.neg p)]
        (.here (.lit (.neg p)) [])).arrow .disj) :=
  LogicalDeletion.tail_square .disj [] (.lit (.neg p)) (.lit (.neg p)) (.here (.lit (.neg p)) [])

#print axioms LogicalDeletion.before_square

#print axioms LogicalDeletion.tail_square

#print axioms CutCommutation.same_conjL_before_rank_step

#print axioms CutCommutation.same_conjL_tail_rank_step

#print axioms CutCommutation.same_disjR_before_rank_step

#print axioms CutCommutation.same_disjR_tail_rank_step

#print axioms CutCommutation.selected_opposite_left_rank_step

#print axioms CutCommutation.selected_opposite_right_rank_step
