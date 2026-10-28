module

public import DosenPetric.GentzenConjRightSecondNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjSecondParent_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P (C :: Θ) (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front Γ Θ C).left (G.conjR f g))).denote =
      comp (BinaryMix.rightInput Γ Θ I)
        (comp (tensor .conj (ofTerm f.denote)
          (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (assocL .disj B (succ Λ) (succ D))))
          (comp (ofTerm (Term.mixedDisj A (succ Δ) B (.disj (succ Λ) (succ D))))
            (tensor .disj (id (.conj A B)) (BinaryMix.rightOutput Δ Λ D)))) := by
  let Q := NormalForm.conj A B
  have hh : ofTerm ((HeadRouting.front Γ Θ C).left (G.conjR f g)).denote =
      comp (tensor .conj (id C) (ofTerm (append .conj Γ Θ).invTerm))
        (comp ((sideM P .conj).cross C (ante Γ) (ante Θ))
          (comp (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
            (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ))))
            (tensor .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm)))) := by
    rw [ExchangeScript.left_denote,G.denote_conjR]
    simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id,Laws.assoc]
    have he : comp ((HeadRouting.front Γ Θ C).arrow .conj)
        (ofTerm (append .conj Γ (C :: Θ)).invTerm) =
        comp (tensor .conj (id C) (ofTerm (append .conj Γ Θ).invTerm))
          ((sideM P .conj).cross C (ante Γ) (ante Θ)) := HeadRouting.front_split .conj Γ Θ C
    rw [← Laws.assoc,he]
    simp only [Laws.assoc]
    rfl
  rw [cut_splice,hh,Splice.context]
  have hs : splice (ofTerm h.denote)
      (comp ((sideM P .conj).cross C (ante Γ) (ante Θ))
        (comp (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ))))
          (tensor .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm)))) =
      comp (splice (ofTerm h.denote)
        (comp ((sideM P .conj).cross C (ante Γ) (ante Θ))
          (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
            (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ))))))
        (tensor .disj (tensor .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm)) (id (succ D))) := by
    simpa only [Laws.assoc] using Splice.output (ofTerm h.denote)
      (comp ((sideM P .conj).cross C (ante Γ) (ante Θ))
        (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ)))))
      (tensor .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm))
  rw [hs]
  have ho : comp (tensor .disj (tensor .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm)) (id (succ D)))
      (ofTerm (append .disj (Q :: (Δ ++ Λ)) D).toTerm) =
      comp (assocL .disj Q (.disj (succ Δ) (succ Λ)) (succ D))
        (tensor .disj (id Q) (comp (tensor .disj (ofTerm (append .disj Δ Λ).toTerm) (id (succ D)))
          (ofTerm (append .disj (Δ ++ Λ) D).toTerm))) := by
    have he := split_cons .disj Q (Δ ++ Λ) D
    dsimp only [side,category,opposite,sideM,disjMonoidal,split] at he
    rw [he,← Laws.assoc,← Laws.assocL_nat,Laws.assoc,Laws.tensor_comp,Laws.id_comp]
  simp only [Laws.assoc]
  erw [ho]
  have hc : comp (tensor .disj (id Q) (assocL .disj (succ Δ) (succ Λ) (succ D)))
      (tensor .disj (id Q) (BinaryMix.rightOutput Δ Λ D)) =
      tensor .disj (id Q) (comp (tensor .disj (ofTerm (append .disj Δ Λ).toTerm) (id (succ D)))
        (ofTerm (append .disj (Δ ++ Λ) D).toTerm)) := by
    rw [Laws.tensor_comp,Laws.id_comp]
    unfold BinaryMix.rightOutput
    rw [← Laws.assoc,Laws.assocL_R,Laws.id_comp]
  have he := congrArg (fun k => comp
    (comp (ofTerm (append .conj (Γ ++ Θ) I).invTerm)
      (tensor .conj (ofTerm (append .conj Γ Θ).invTerm) (id (ante I))))
    (comp k (tensor .disj (id Q) (BinaryMix.rightOutput Δ Λ D))))
    (conjR_right_second_core (ofTerm f.denote) (ofTerm g.denote) (ofTerm h.denote))
  dsimp only [Q,ante,succ] at hc he ⊢
  simpa only [Laws.assoc,hc,BinaryMix.rightInput] using he

theorem conjSecondNative_equation {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P (C :: Θ) (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front Γ Θ C).left (G.conjR f g))).denote =
      ofTerm (conjSecondNative f (G.cut h g)).denote :=
  (conjSecondParent_denote f g h).trans (conjSecondNative_denote f g h).symm

end BinaryLogical
end DosenPetric.Reduced.Gentzen
