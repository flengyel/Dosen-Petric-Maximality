module

public import DosenPetric.GentzenConjRightSecondDiagram

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

def conjSecondNative {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (Θ ++ I) (B :: (Λ ++ D))) :
    G P ((Γ ++ Θ) ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  (((ExchangeScript.appendAssoc Δ Λ D).inverse.consFixed (.conj A B)).right
    ((ExchangeScript.appendAssoc Γ Θ I).inverse.left (G.conjR f k)))

theorem conjSecondNative_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P (C :: Θ) (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (conjSecondNative f (G.cut h g)).denote =
      comp (BinaryMix.rightInput Γ Θ I)
        (comp (tensor .conj (ofTerm f.denote)
          (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (assocL .disj B (succ Λ) (succ D))))
          (comp (ofTerm (Term.mixedDisj A (succ Δ) B (.disj (succ Λ) (succ D))))
            (tensor .disj (id (.conj A B)) (BinaryMix.rightOutput Δ Λ D)))) := by
  unfold conjSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [cut_splice]
  have hd : ofTerm (append .disj (B :: Λ) D).toTerm =
      comp (assocL .disj B (succ Λ) (succ D))
        (tensor .disj (id B) (ofTerm (append .disj Λ D).toTerm)) := split_cons .disj B Λ D
  rw [hd]
  have ht : tensor .conj (ofTerm f.denote)
      (comp (ofTerm (append .conj Θ I).invTerm)
        (comp (splice (ofTerm h.denote) (ofTerm g.denote))
          (comp (assocL .disj B (succ Λ) (succ D))
            (tensor .disj (id B) (ofTerm (append .disj Λ D).toTerm))))) =
      comp (tensor .conj (id (ante Γ)) (ofTerm (append .conj Θ I).invTerm))
        (comp (tensor .conj (ofTerm f.denote)
          (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (assocL .disj B (succ Λ) (succ D))))
          (tensor .conj (id (succ (A :: Δ)))
            (tensor .disj (id B) (ofTerm (append .disj Λ D).toTerm)))) := by
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id,Laws.assoc]
  rw [ht]
  have hm : comp (tensor .conj (id (succ (A :: Δ)))
      (tensor .disj (id B) (ofTerm (append .disj Λ D).toTerm)))
      (ofTerm (Term.mixedDisj A (succ Δ) B (succ (Λ ++ D)))) =
      comp (ofTerm (Term.mixedDisj A (succ Δ) B (.disj (succ Λ) (succ D))))
        (tensor .disj (id (.conj A B))
          (tensor .disj (id (succ Δ)) (ofTerm (append .disj Λ D).toTerm))) := by
    simpa only [Laws.tensor_id] using
      (mixedDisj_nat (id A) (id (succ Δ)) (id B) (ofTerm (append .disj Λ D).toTerm)).symm
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (succ (A :: Δ)))
    (tensor .disj (id B) (ofTerm (append .disj Λ D).toTerm))),hm]
  simp only [Laws.assoc]
  rw [ExchangeScript.consFixed_arrow]
  have ho : comp (tensor .disj (id (succ Δ)) (ofTerm (append .disj Λ D).toTerm))
      (comp (ofTerm (append .disj Δ (Λ ++ D)).toTerm)
        ((ExchangeScript.appendAssoc Δ Λ D).inverse.arrow .disj)) = BinaryMix.rightOutput Δ Λ D := by
    have he := split_assoc_inverse .disj Δ Λ D
    dsimp only [side,category,opposite,sideM,disjMonoidal,split,BinaryMix.rightOutput] at he ⊢
    simpa only [Laws.assoc] using he
  dsimp only [sideM,side,disjMonoidal,opposite,category]
  rw [Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,ho]
  have hi : comp ((ExchangeScript.appendAssoc Γ Θ I).inverse.arrow .conj)
      (comp (ofTerm (append .conj Γ (Θ ++ I)).invTerm)
        (tensor .conj (id (ante Γ)) (ofTerm (append .conj Θ I).invTerm))) =
      BinaryMix.rightInput Γ Θ I := split_assoc_inverse .conj Γ Θ I
  have he := congrArg (fun k => comp k
    (comp (tensor .conj (ofTerm f.denote)
      (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (assocL .disj B (succ Λ) (succ D))))
      (comp (ofTerm (Term.mixedDisj A (succ Δ) B (.disj (succ Λ) (succ D))))
        (tensor .disj (id (.conj A B)) (BinaryMix.rightOutput Δ Λ D))))) hi
  simpa only [Laws.assoc] using he

end BinaryLogical
end DosenPetric.Reduced.Gentzen
