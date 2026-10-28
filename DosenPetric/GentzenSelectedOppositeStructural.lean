module

public import DosenPetric.GentzenStructuralCutDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Every opposite antecedent structural program commutes with an arbitrary selected cut. -/
theorem selected_opposite_left {F U Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P U Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (p.left f) x g y).denote =
      ofTerm ((p.prefixFixed y.erase).left (PositionalCut.cut f x g y)).denote := by
  rw [PositionalCut.splice_denote, StructuralProgram.left_denote,
    StructuralProgram.left_denote, PositionalCut.splice_denote, Laws.assoc, Splice.input]
  have he : comp ((p.prefixFixed y.erase).arrow .conj)
      (ofTerm (append .conj y.erase U).invTerm) =
      comp (ofTerm (append .conj y.erase F).invTerm)
        (tensor .conj (id (ante y.erase)) (p.arrow .conj)) := p.prefixFixed_split .conj y.erase
  simp only [Laws.assoc]
  rw [← Laws.assoc ((p.prefixFixed y.erase).arrow .conj),he,Laws.assoc]

/-- Every opposite succedent structural program commutes with an arbitrary selected cut. -/
theorem selected_opposite_right {Γ Δ Θ F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ Δ) (x : At Δ C)
    (g : G P Θ U) (y : At Θ C) :
    ofTerm (PositionalCut.cut f x (p.right g) y).denote =
      ofTerm ((p.suffixFixed x.erase).right (PositionalCut.cut f x g y)).denote := by
  rw [PositionalCut.splice_denote, StructuralProgram.right_denote,
    StructuralProgram.right_denote, PositionalCut.splice_denote, ← Laws.assoc (y.toHead.arrow .conj),
    Splice.output]
  have he : comp (ofTerm (append .disj U x.erase).toTerm)
      ((p.suffixFixed x.erase).arrow .disj) =
      comp (tensor .disj (p.arrow .disj) (id (succ x.erase)))
        (ofTerm (append .disj F x.erase).toTerm) := p.suffixFixed_split .disj x.erase
  simp only [Laws.assoc]
  rw [he]

end CutCommutation
namespace PositionalCut

/-- The original selected cleanliness and rank descend through any nonempty opposite program. -/
theorem selected_opposite_left_descent {F U Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (f : G P U Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) (hc : Clean (p.left f) x g y) :
    Clean f x g y ∧ rank f x g y < rank (p.left f) x g y := by
  rcases hc with ⟨hf,hg,af,ag,bf,bg⟩
  constructor
  · refine ⟨(p.leftAddress f).cutFree hf,hg,(p.leftAddress f).atomized af,ag,?_,bg⟩
    exact bf.inherit (p.leftAddress f) x (p.leftAddress_opposite f x)
  · have hr := p.rho_left_opposite f x
    unfold rank
    omega

theorem selected_opposite_right_descent {Γ Δ Θ F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (f : G P Γ Δ) (x : At Δ C)
    (g : G P Θ U) (y : At Θ C) (hc : Clean f x (p.right g) y) :
    Clean f x g y ∧ rank f x g y < rank f x (p.right g) y := by
  rcases hc with ⟨hf,hg,af,ag,bf,bg⟩
  constructor
  · refine ⟨hf,(p.rightAddress g).cutFree hg,af,(p.rightAddress g).atomized ag,bf,?_⟩
    exact bg.inherit (p.rightAddress g) y (p.rightAddress_opposite g y)
  · have hr := p.rho_right_opposite g y
    unfold rank
    omega

end PositionalCut
end DosenPetric.Reduced.Gentzen
