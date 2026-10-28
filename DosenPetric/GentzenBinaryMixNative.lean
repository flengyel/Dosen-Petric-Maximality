module

public import DosenPetric.GentzenBinaryMixFirst

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix
variable {Γ Θ D Λ T J : List (NormalForm P)} {C : NormalForm P}

/-- Associate the native mix around a cut on its leading output child. -/
def leading (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ D)) :
    G P (T ++ (Γ ++ Θ)) (J ++ (D ++ Λ)) :=
  (ExchangeScript.appendAssoc J D Λ).right
    ((ExchangeScript.appendAssoc T Γ Θ).left (G.mix g k))

theorem leading_denote (f : G P Γ (C :: D)) (g : G P Θ Λ) (h : G P (C :: T) J) :
    ofTerm (leading g (G.cut f h)).denote =
      comp (splitThree .conj T Γ Θ)
        (comp (tensor .conj (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm g.denote))
          (comp (mix (.disj (succ J) (succ D)) (succ Λ)) (splitThree .disj J D Λ))) := by
  unfold leading
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.mix g.denote (G.cut f h).denote))) _ = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [cut_splice]
  have ht : tensor .conj
      (comp (ofTerm (append .conj T Γ).invTerm)
        (comp (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm (append .disj J D).toTerm)))
      (ofTerm g.denote) =
      comp (tensor .conj (ofTerm (append .conj T Γ).invTerm) (id (ante Θ)))
        (comp (tensor .conj (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm g.denote))
          (tensor .conj (ofTerm (append .disj J D).toTerm) (id (succ Λ)))) := by
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm (append .disj J D).toTerm) (id (succ Λ))),← Laws.mix_nat]
  simp only [Laws.assoc]
  have hi : comp ((ExchangeScript.appendAssoc T Γ Θ).arrow .conj)
      (comp (ofTerm (append .conj (T ++ Γ) Θ).invTerm)
        (tensor .conj (ofTerm (append .conj T Γ).invTerm) (id (ante Θ)))) =
      splitThree .conj T Γ Θ := by
    rw [splitThree_eq]
    exact split_assoc .conj T Γ Θ
  have ho : comp (tensor .disj (ofTerm (append .disj J D).toTerm) (id (succ Λ)))
      (comp (ofTerm (append .disj (J ++ D) Λ).toTerm)
        ((ExchangeScript.appendAssoc J D Λ).arrow .disj)) = splitThree .disj J D Λ := by
    rw [splitThree_eq]
    have he := split_assoc .disj J D Λ
    dsimp only [side,category,opposite,sideM,disjMonoidal,split] at he ⊢
    simpa only [Laws.assoc] using he
  rw [ho]
  have he := congrArg (fun k => comp k
    (comp (tensor .conj (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm g.denote))
      (comp (mix (.disj (succ J) (succ D)) (succ Λ)) (splitThree .disj J D Λ)))) hi
  simpa only [Laws.assoc] using he

theorem leading_cut_denote (f : G P Γ (C :: D)) (g : G P Θ Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut (G.mix g f) h).denote =
      comp (splitThree .conj T Γ Θ)
        (comp (tensor .conj (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm g.denote))
          (comp (mix (.disj (succ J) (succ D)) (succ Λ)) (splitThree .disj J D Λ))) := by
  have hf : ofTerm (G.mix g f).denote =
      comp (ofTerm (append .conj Γ Θ).invTerm)
        (comp (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (comp (mix (.disj C (succ D)) (succ Λ)) (assocL .disj C (succ D) (succ Λ))))
          (tensor .disj (id C) (ofTerm (append .disj D Λ).toTerm))) := by
    simp only [G.denote,Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
    have he := split_cons .disj C D Λ
    dsimp only [side,category,opposite,sideM,disjMonoidal,split] at he
    rw [he]
    simp only [Laws.assoc]
  rw [cut_splice,hf,Splice.input,Splice.residual,splice_mix]
  simp only [Laws.assoc]
  have ho : comp (assocL .disj (succ J) (succ D) (succ Λ))
      (comp (tensor .disj (id (succ J)) (ofTerm (append .disj D Λ).toTerm))
        (ofTerm (append .disj J (D ++ Λ)).toTerm)) = splitThree .disj J D Λ := by
    rw [splitThree_eq]
    exact (Laws.assoc ..).symm
  dsimp only [succ] at ho
  erw [ho]
  have hi : comp (ofTerm (append .conj T (Γ ++ Θ)).invTerm)
      (comp (tensor .conj (id (ante T)) (ofTerm (append .conj Γ Θ).invTerm))
        (assocR .conj (ante T) (ante Γ) (ante Θ))) = splitThree .conj T Γ Θ := by
    rw [splitThree_eq]
    rfl
  have he := congrArg (fun k => comp k
    (comp (tensor .conj (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm g.denote))
      (comp (mix (.disj (succ J) (succ D)) (succ Λ)) (splitThree .disj J D Λ)))) hi
  simpa only [Laws.assoc] using he

theorem leading_equation (f : G P Γ (C :: D)) (g : G P Θ Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut (G.mix g f) h).denote = ofTerm (leading g (G.cut f h)).denote :=
  (leading_cut_denote f g h).trans (leading_denote f g h).symm

end BinaryMix
end DosenPetric.Reduced.Gentzen
