module

public import DosenPetric.GentzenStructuralSuffix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Every antecedent structural rule in the left cut premise commutes below cut. -/
theorem opposite_left {F U Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P U (C :: Δ)) (g : G P (C :: Θ) Λ) :
    ofTerm (G.cut (p.left f) g).denote =
      ofTerm ((p.prefixFixed Θ).left (G.cut f g)).denote := by
  rw [cut_splice, StructuralProgram.left_denote, Splice.input,
    StructuralProgram.left_denote, cut_splice]
  have he : comp ((p.prefixFixed Θ).arrow .conj) (ofTerm (append .conj Θ U).invTerm) =
      comp (ofTerm (append .conj Θ F).invTerm) (tensor .conj (id (ante Θ)) (p.arrow .conj)) :=
    p.prefixFixed_split .conj Θ
  simp only [Laws.assoc]
  rw [← Laws.assoc ((p.prefixFixed Θ).arrow .conj), he, Laws.assoc]

/-- Every succedent structural rule in the right cut premise commutes below cut. -/
theorem opposite_right {Γ Θ Δ F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) U) :
    ofTerm (G.cut f (p.right g)).denote =
      ofTerm ((p.suffixFixed Δ).right (G.cut f g)).denote := by
  rw [cut_splice, StructuralProgram.right_denote, Splice.output,
    StructuralProgram.right_denote, cut_splice]
  have he : comp (ofTerm (append .disj U Δ).toTerm) ((p.suffixFixed Δ).arrow .disj) =
      comp (tensor .disj (p.arrow .disj) (id (succ Δ))) (ofTerm (append .disj F Δ).toTerm) :=
    p.suffixFixed_split .disj Δ
  simp only [Laws.assoc]
  rw [he]

end CutCommutation
end DosenPetric.Reduced.Gentzen
