module

public import DosenPetric.GentzenConjLeftNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem leftFirstParent_selected {Γ Θ D Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: C :: D)) (g : G P Θ (B :: Λ)) :
    ofTerm ((HeadRouting.front [.conj A B] (D ++ Λ) C).right
      (G.conjR (Δ := C :: D) (Λ := Λ) f g)).denote =
      comp (ofTerm (append .conj Γ Θ).invTerm)
        (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (comp (selectedMixed A C (succ D) B (succ Λ))
            (tensor .disj (id C) (tensor .disj (id (.conj A B)) (ofTerm (append .disj D Λ).toTerm))))) := by
  rw [ExchangeScript.right_denote,G.denote_conjR,HeadRouting.front_singleton]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  have hd := split_cons .disj C D Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hd
  rw [hd,tensor_factor .disj (id (.conj A B))]
  simp only [Laws.assoc]
  erw [disj_cross_nat]
  simp only [selectedMixed,Laws.assoc]
  all_goals rfl

theorem leftFirstParent_denote {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: C :: D)) (g : G P Θ (B :: Λ)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front [.conj A B] (D ++ Λ) C).right
      (G.conjR (Δ := C :: D) (Λ := Λ) f g)) h).denote =
      comp (leftFirstInput T Γ Θ)
        (comp (tensor .conj
          (comp (splice (comp (ofTerm f.denote) ((sideM P .disj).cross C A (succ D))) (ofTerm h.denote))
            ((sideM P .disj).cross A (succ J) (succ D))) (ofTerm g.denote))
          (comp (selectedMixed A (succ J) (succ D) B (succ Λ))
            (leftFirstOutput (.conj A B) J D Λ))) := by
  have hs : splice (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
      (comp (selectedMixed A C (succ D) B (succ Λ))
        (tensor .disj (id C) (tensor .disj (id (.conj A B)) (ofTerm (append .disj D Λ).toTerm)))))
        (ofTerm h.denote) =
      comp (splice (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
        (selectedMixed A C (succ D) B (succ Λ))) (ofTerm h.denote))
          (tensor .disj (id (succ J)) (tensor .disj (id (.conj A B)) (ofTerm (append .disj D Λ).toTerm))) := by
    simpa only [Laws.assoc] using Splice.residual
      (tensor .disj (id (.conj A B)) (ofTerm (append .disj D Λ).toTerm))
      (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote)) (selectedMixed A C (succ D) B (succ Λ)))
      (ofTerm h.denote)
  rw [cut_splice,leftFirstParent_selected,Splice.input]
  erw [hs,conjR_left_first_core]
  simp only [leftFirstInput,leftFirstOutput,Laws.assoc]
  all_goals rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
