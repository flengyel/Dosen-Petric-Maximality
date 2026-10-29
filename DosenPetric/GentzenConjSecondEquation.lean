module

public import DosenPetric.GentzenConjSecondParent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjLeftSecondNative_denote {Γ Θ D E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: D)) (g : G P Θ (B :: C :: E)) (h : G P (C :: T) J) :
    ofTerm (conjLeftSecondNative f (G.cut ((HeadRouting.front [B] E C).right g) h)).denote =
      comp (leftSecondInput T Γ Θ)
        (comp (tensor .conj (ofTerm f.denote)
          (comp (splice (comp (ofTerm g.denote) ((sideM P .disj).cross C B (succ E))) (ofTerm h.denote))
            ((sideM P .disj).cross B (succ J) (succ E))))
          (comp (selectedMixedSecond A (succ D) B (succ J) (succ E))
            (leftFirstOutput (.conj A B) J D E))) := by
  unfold conjLeftSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.right_denote,
    ExchangeScript.left_denote,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [ExchangeScript.right_denote,cut_splice,ExchangeScript.right_denote,HeadRouting.front_singleton]
  simp only [Laws.assoc]
  have ha := HeadRouting.front_split .disj J E B
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at ha
  erw [ha]
  have ht : tensor .conj (ofTerm f.denote)
      (comp (ofTerm (append .conj T Θ).invTerm)
        (comp (splice (comp (ofTerm g.denote) ((sideM P .disj).cross C B (succ E))) (ofTerm h.denote))
          (comp ((sideM P .disj).cross B (succ J) (succ E))
            (tensor .disj (id B) (ofTerm (append .disj J E).toTerm))))) =
      comp (tensor .conj (id (ante Γ)) (ofTerm (append .conj T Θ).invTerm))
        (comp (tensor .conj (ofTerm f.denote)
          (comp (splice (comp (ofTerm g.denote) ((sideM P .disj).cross C B (succ E))) (ofTerm h.denote))
            ((sideM P .disj).cross B (succ J) (succ E))))
          (tensor .conj (id (succ (A :: D))) (tensor .disj (id B) (ofTerm (append .disj J E).toTerm)))) := by
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id,Laws.assoc]
  erw [ht]
  have hm : comp (tensor .conj (id (succ (A :: D)))
      (tensor .disj (id B) (ofTerm (append .disj J E).toTerm)))
      (ofTerm (Term.mixedDisj A (succ D) B (succ (J ++ E)))) =
      comp (ofTerm (Term.mixedDisj A (succ D) B (.disj (succ J) (succ E))))
        (tensor .disj (id (.conj A B))
          (tensor .disj (id (succ D)) (ofTerm (append .disj J E).toTerm))) := by
    simpa only [Laws.tensor_id] using
      (mixedDisj_nat (id A) (id (succ D)) (id B) (ofTerm (append .disj J E).toTerm)).symm
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (succ (A :: D)))
    (tensor .disj (id B) (ofTerm (append .disj J E).toTerm))),hm]
  simp only [Laws.assoc]
  erw [left_second_output,← left_second_input T Γ Θ]
  simp only [selectedMixedSecond,Laws.assoc]

theorem conjLeftSecondNative_equation {Γ Θ D E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: D)) (g : G P Θ (B :: C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front (.conj A B :: D) E C).right
      (G.conjR (Δ := D) (Λ := C :: E) f g)) h).denote =
      ofTerm (conjLeftSecondNative f (G.cut ((HeadRouting.front [B] E C).right g) h)).denote :=
  (leftSecondParent_denote f g h).trans (conjLeftSecondNative_denote f g h).symm

end BinaryLogical
end DosenPetric.Reduced.Gentzen
