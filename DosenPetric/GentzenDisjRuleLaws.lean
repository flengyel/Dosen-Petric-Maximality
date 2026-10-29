module

public import DosenPetric.GentzenDisjFirstCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem disjPair_input {A B X Y X' Y' U V : NormalForm P}
    (x : Hom X X') (y : Hom Y Y') (f : Hom (.conj A X') U) (g : Hom (.conj B Y') V) :
    comp (tensor .conj (id (.disj A B)) (tensor .conj x y)) (disjPair f g) =
      disjPair (comp (tensor .conj (id A) x) f) (comp (tensor .conj (id B) y) g) := by
  have hs := sourceConj_nat x y (id A) (id B)
  rw [Laws.tensor_id] at hs
  unfold disjPair
  rw [← Laws.assoc (tensor .conj (id (.disj A B)) (tensor .conj x y)),← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (tensor .conj x y) (id (.disj A B))),← hs]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp]
  have ha := (Laws.swap_nat .conj x (id A)).symm
  have hb := (Laws.swap_nat .conj y (id B)).symm
  rw [← Laws.assoc (tensor .conj x (id A)),ha,
    ← Laws.assoc (tensor .conj y (id B)),hb]
  simp only [Laws.assoc]

theorem disjPair_output {A B X Y U V U' V' : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B Y) V) (u : Hom U U') (v : Hom V V') :
    comp (disjPair f g) (tensor .disj u v) = disjPair (comp f u) (comp g v) := by
  simp only [disjPair,Laws.assoc,Laws.tensor_comp]

theorem disjPair_output_first {A B X Y U V U' : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B Y) V) (u : Hom U U') :
    disjPair (comp f u) g = comp (disjPair f g) (tensor .disj u (id V)) := by
  simpa only [Laws.comp_id] using (disjPair_output f g u (id V)).symm

theorem disjPair_input_first {A B X Y X' U V : NormalForm P}
    (x : Hom X X') (f : Hom (.conj A X') U) (g : Hom (.conj B Y) V) :
    disjPair (comp (tensor .conj (id A) x) f) g =
      comp (tensor .conj (id (.disj A B)) (tensor .conj x (id Y))) (disjPair f g) := by
  simpa only [Laws.tensor_id,Laws.id_comp] using (disjPair_input x (id Y) f g).symm

theorem disjL_denote {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    ofTerm (G.disjL f g).denote =
      comp (tensor .conj (id (.disj A B)) (ofTerm (append .conj Γ Θ).invTerm))
        (comp (disjPair (ofTerm f.denote) (ofTerm g.denote)) (ofTerm (append .disj Δ Λ).toTerm)) := by
  rw [G.denote_disjL]
  simp only [Rules.disjLeft,ofTerm_comp,ofTerm_tensor,ofTerm_id,term_swap,disjPair,Laws.assoc]
  rw [← Laws.assoc (tensor .disj (swap .conj (ante Γ) A) (swap .conj (ante Θ) B)),Laws.tensor_comp]

end DisjLogical
end DosenPetric.Reduced.Gentzen
