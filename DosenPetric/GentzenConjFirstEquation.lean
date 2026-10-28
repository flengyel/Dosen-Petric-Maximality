module

public import DosenPetric.GentzenConjFirstNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjFirstNative_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (C :: Γ) (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (conjFirstNative (G.cut h f) g).denote =
      comp (firstInput Γ Θ I)
        (comp (tensor .conj (comp (splice (ofTerm h.denote) (ofTerm f.denote))
          (assocL .disj A (succ Δ) (succ D))) (ofTerm g.denote))
          (comp (ofTerm (Term.mixedDisj A (.disj (succ Δ) (succ D)) B (succ Λ)))
            (firstOutput (.conj A B) Δ Λ D))) := by
  unfold conjFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [cut_splice]
  have hd := split_cons .disj A Δ D
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hd
  rw [hd]
  have ht : tensor .conj
      (comp (ofTerm (append .conj Γ I).invTerm)
        (comp (splice (ofTerm h.denote) (ofTerm f.denote))
          (comp (assocL .disj A (succ Δ) (succ D))
            (tensor .disj (id A) (ofTerm (append .disj Δ D).toTerm)))))
      (ofTerm g.denote) =
      comp (tensor .conj (ofTerm (append .conj Γ I).invTerm) (id (ante Θ)))
        (comp (tensor .conj
          (comp (splice (ofTerm h.denote) (ofTerm f.denote)) (assocL .disj A (succ Δ) (succ D)))
          (ofTerm g.denote))
          (tensor .conj (tensor .disj (id A) (ofTerm (append .disj Δ D).toTerm)) (id (succ (B :: Λ))))) := by
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id,Laws.assoc]
  rw [ht]
  have hm : comp (tensor .conj (tensor .disj (id A) (ofTerm (append .disj Δ D).toTerm))
      (id (succ (B :: Λ)))) (ofTerm (Term.mixedDisj A (succ (Δ ++ D)) B (succ Λ))) =
      comp (ofTerm (Term.mixedDisj A (.disj (succ Δ) (succ D)) B (succ Λ)))
        (tensor .disj (id (.conj A B))
          (tensor .disj (ofTerm (append .disj Δ D).toTerm) (id (succ Λ)))) := by
    simpa only [Laws.tensor_id] using
      (mixedDisj_nat (id A) (ofTerm (append .disj Δ D).toTerm) (id B) (id (succ Λ))).symm
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (tensor .disj (id A) (ofTerm (append .disj Δ D).toTerm))
    (id (succ (B :: Λ)))) ,hm]
  rw [← first_input Γ Θ I]
  simp only [firstOutput,Laws.assoc]
  rfl

theorem conjFirstParent_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (C :: Γ) (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h (G.conjR f g)).denote =
      comp (firstInput Γ Θ I)
        (comp (tensor .conj (comp (splice (ofTerm h.denote) (ofTerm f.denote))
          (assocL .disj A (succ Δ) (succ D))) (ofTerm g.denote))
          (comp (ofTerm (Term.mixedDisj A (.disj (succ Δ) (succ D)) B (succ Λ)))
            (firstOutput (.conj A B) Δ Λ D))) := by
  have hh : ofTerm (G.conjR f g).denote =
      comp (tensor .conj (id C) (ofTerm (append .conj Γ Θ).invTerm))
        (comp (assocR .conj C (ante Γ) (ante Θ))
          (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
            (comp (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ)))
              (tensor .disj (id (.conj A B)) (ofTerm (append .disj Δ Λ).toTerm))))) := by
    rw [G.denote_conjR]
    simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
    have hi := split_cons .conj C Γ Θ
    dsimp only [side,sideM,conjMonoidal,category,split] at hi
    rw [hi]
    simp only [Laws.assoc]
  rw [cut_splice,hh,Splice.context]
  have hs : splice (ofTerm h.denote)
      (comp (assocR .conj C (ante Γ) (ante Θ))
        (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (comp (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ)))
            (tensor .disj (id (.conj A B)) (ofTerm (append .disj Δ Λ).toTerm))))) =
      comp (splice (ofTerm h.denote)
        (comp (assocR .conj C (ante Γ) (ante Θ))
          (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
            (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ))))))
        (tensor .disj (tensor .disj (id (.conj A B)) (ofTerm (append .disj Δ Λ).toTerm))
          (id (succ D))) := by
    simpa only [Laws.assoc] using Splice.output (ofTerm h.denote)
      (comp (assocR .conj C (ante Γ) (ante Θ))
        (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ)))))
      (tensor .disj (id (.conj A B)) (ofTerm (append .disj Δ Λ).toTerm))
  rw [hs,conjR_right_first_core]
  simp only [firstInput,Laws.assoc]
  rw [first_output]
  rfl

theorem conjFirstNative_equation {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (C :: Γ) (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h (G.conjR f g)).denote =
      ofTerm (conjFirstNative (G.cut h f) g).denote :=
  (conjFirstParent_denote f g h).trans (conjFirstNative_denote f g h).symm

end BinaryLogical
end DosenPetric.Reduced.Gentzen
