module

public import DosenPetric.GentzenOppositeStructuralReplacement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Descend through the first mix branch on the left cut side at its original tag. -/
theorem mix_left_first_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.mix f g) (At.shift Λ a) h z) :
    Clean f (a) h z ∧ rank f (a) h z < rank (G.mix f g) (At.shift Λ a) h z := by
  let b : Upper (G.mix f g) .right C := ⟨⟨_,_,f,Premise.mix_left f g⟩,a⟩
  have hb : (G.mix f g).IsPredecessor .right (At.shift Λ a) b := rfl
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ (At.shift Λ a) h z b hb⟩

/-- Descend through the second mix branch on the left cut side at its original tag. -/
theorem mix_left_second_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.mix f g) (a.before Δ) h z) :
    Clean g (a) h z ∧ rank g (a) h z < rank (G.mix f g) (a.before Δ) h z := by
  let b : Upper (G.mix f g) .right C := ⟨⟨_,_,g,Premise.mix_right f g⟩,a⟩
  have hb : (G.mix f g).IsPredecessor .right (a.before Δ) b := rfl
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ (a.before Δ) h z b hb⟩

/-- Descend through the first mix branch on the right cut side at its original tag. -/
theorem mix_right_first_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : Clean h z (G.mix f g) (At.shift Θ a)) :
    Clean h z f (a) ∧ rank h z f (a) < rank h z (G.mix f g) (At.shift Θ a) := by
  let b : Upper (G.mix f g) .left C := ⟨⟨_,_,f,Premise.mix_left f g⟩,a⟩
  have hb : (G.mix f g).IsPredecessor .left (At.shift Θ a) b := rfl
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor h z _ (At.shift Θ a) b hb⟩

/-- Descend through the second mix branch on the right cut side at its original tag. -/
theorem mix_right_second_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : Clean h z (G.mix f g) (a.before Γ)) :
    Clean h z g (a) ∧ rank h z g (a) < rank h z (G.mix f g) (a.before Γ) := by
  let b : Upper (G.mix f g) .left C := ⟨⟨_,_,g,Premise.mix_right f g⟩,a⟩
  have hb : (G.mix f g).IsPredecessor .left (a.before Γ) b := rfl
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor h z _ (a.before Γ) b hb⟩

/-- Descend through the first conjR branch on the left cut side at its original tag. -/
theorem conjR_left_first_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.conjR f g) ((a.before Λ).there) h z) :
    Clean f (a.there) h z ∧ rank f (a.there) h z < rank (G.conjR f g) ((a.before Λ).there) h z := by
  let b : Upper (G.conjR f g) .right C := ⟨⟨_,_,f,Premise.conjR_left f g⟩,a.there⟩
  have hb : (G.conjR f g).IsPredecessor .right ((a.before Λ).there) b := rfl
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ ((a.before Λ).there) h z b hb⟩

/-- Descend through the second conjR branch on the left cut side at its original tag. -/
theorem conjR_left_second_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.conjR f g) ((At.shift Δ a).there) h z) :
    Clean g (a.there) h z ∧ rank g (a.there) h z < rank (G.conjR f g) ((At.shift Δ a).there) h z := by
  let b : Upper (G.conjR f g) .right C := ⟨⟨_,_,g,Premise.conjR_right f g⟩,a.there⟩
  have hb : (G.conjR f g).IsPredecessor .right ((At.shift Δ a).there) b := rfl
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ ((At.shift Δ a).there) h z b hb⟩

/-- Descend through the first conjR branch on the right cut side at its original tag. -/
theorem conjR_right_first_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : Clean h z (G.conjR f g) (a.before Θ)) :
    Clean h z f (a) ∧ rank h z f (a) < rank h z (G.conjR f g) (a.before Θ) := by
  let b : Upper (G.conjR f g) .left C := ⟨⟨_,_,f,Premise.conjR_left f g⟩,a⟩
  have hb : (G.conjR f g).IsPredecessor .left (a.before Θ) b := rfl
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor h z _ (a.before Θ) b hb⟩

/-- Descend through the second conjR branch on the right cut side at its original tag. -/
theorem conjR_right_second_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : Clean h z (G.conjR f g) (At.shift Γ a)) :
    Clean h z g (a) ∧ rank h z g (a) < rank h z (G.conjR f g) (At.shift Γ a) := by
  let b : Upper (G.conjR f g) .left C := ⟨⟨_,_,g,Premise.conjR_right f g⟩,a⟩
  have hb : (G.conjR f g).IsPredecessor .left (At.shift Γ a) b := rfl
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor h z _ (At.shift Γ a) b hb⟩

/-- Descend through the first disjL branch on the left cut side at its original tag. -/
theorem disjL_left_first_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.disjL f g) (a.before Λ) h z) :
    Clean f (a) h z ∧ rank f (a) h z < rank (G.disjL f g) (a.before Λ) h z := by
  let b : Upper (G.disjL f g) .right C := ⟨⟨_,_,f,Premise.disjL_left f g⟩,a⟩
  have hb : (G.disjL f g).IsPredecessor .right (a.before Λ) b := rfl
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ (a.before Λ) h z b hb⟩

/-- Descend through the second disjL branch on the left cut side at its original tag. -/
theorem disjL_left_second_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : Clean (G.disjL f g) (At.shift Δ a) h z) :
    Clean g (a) h z ∧ rank g (a) h z < rank (G.disjL f g) (At.shift Δ a) h z := by
  let b : Upper (G.disjL f g) .right C := ⟨⟨_,_,g,Premise.disjL_right f g⟩,a⟩
  have hb : (G.disjL f g).IsPredecessor .right (At.shift Δ a) b := rfl
  exact ⟨clean_left_predecessor hc b hb,rank_left_predecessor _ (At.shift Δ a) h z b hb⟩

/-- Descend through the first disjL branch on the right cut side at its original tag. -/
theorem disjL_right_first_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : Clean h z (G.disjL f g) ((a.before Θ).there)) :
    Clean h z f (a.there) ∧ rank h z f (a.there) < rank h z (G.disjL f g) ((a.before Θ).there) := by
  let b : Upper (G.disjL f g) .left C := ⟨⟨_,_,f,Premise.disjL_left f g⟩,a.there⟩
  have hb : (G.disjL f g).IsPredecessor .left ((a.before Θ).there) b := rfl
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor h z _ ((a.before Θ).there) b hb⟩

/-- Descend through the second disjL branch on the right cut side at its original tag. -/
theorem disjL_right_second_descent {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : Clean h z (G.disjL f g) ((At.shift Γ a).there)) :
    Clean h z g (a.there) ∧ rank h z g (a.there) < rank h z (G.disjL f g) ((At.shift Γ a).there) := by
  let b : Upper (G.disjL f g) .left C := ⟨⟨_,_,g,Premise.disjL_right f g⟩,a.there⟩
  have hb : (G.disjL f g).IsPredecessor .left ((At.shift Γ a).there) b := rfl
  exact ⟨clean_right_predecessor hc b hb,rank_right_predecessor h z _ ((At.shift Γ a).there) b hb⟩

end PositionalCut
end DosenPetric.Reduced.Gentzen
