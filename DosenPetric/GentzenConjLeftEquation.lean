module

public import DosenPetric.GentzenConjLeftParent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem conjLeftFirstNative_denote {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: C :: D)) (g : G P Θ (B :: Λ)) (h : G P (C :: T) J) :
    ofTerm (conjLeftFirstNative (G.cut ((HeadRouting.front [A] D C).right f) h) g).denote =
      comp (leftFirstInput T Γ Θ)
        (comp (tensor .conj
          (comp (splice (comp (ofTerm f.denote) ((sideM P .disj).cross C A (succ D))) (ofTerm h.denote))
            ((sideM P .disj).cross A (succ J) (succ D))) (ofTerm g.denote))
          (comp (selectedMixed A (succ J) (succ D) B (succ Λ))
            (leftFirstOutput (.conj A B) J D Λ))) := by
  unfold conjLeftFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.right_denote,
    ExchangeScript.left_denote,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [ExchangeScript.right_denote,cut_splice,ExchangeScript.right_denote,HeadRouting.front_singleton]
  simp only [Laws.assoc]
  have ha := HeadRouting.front_split .disj J D A
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at ha
  erw [ha]
  have ht : tensor .conj
      (comp (ofTerm (append .conj T Γ).invTerm)
        (comp (splice (comp (ofTerm f.denote) ((sideM P .disj).cross C A (succ D))) (ofTerm h.denote))
          (comp ((sideM P .disj).cross A (succ J) (succ D))
            (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))))) (ofTerm g.denote) =
      comp (tensor .conj (ofTerm (append .conj T Γ).invTerm) (id (ante Θ)))
        (comp (tensor .conj
          (comp (splice (comp (ofTerm f.denote) ((sideM P .disj).cross C A (succ D))) (ofTerm h.denote))
            ((sideM P .disj).cross A (succ J) (succ D))) (ofTerm g.denote))
          (tensor .conj (tensor .disj (id A) (ofTerm (append .disj J D).toTerm)) (id (succ (B :: Λ))))) := by
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id,Laws.assoc]
  erw [ht]
  have hm : comp (tensor .conj (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))
      (id (succ (B :: Λ)))) (ofTerm (Term.mixedDisj A (succ (J ++ D)) B (succ Λ))) =
      comp (ofTerm (Term.mixedDisj A (.disj (succ J) (succ D)) B (succ Λ)))
        (tensor .disj (id (.conj A B))
          (tensor .disj (ofTerm (append .disj J D).toTerm) (id (succ Λ)))) := by
    simpa only [Laws.tensor_id] using
      (mixedDisj_nat (id A) (ofTerm (append .disj J D).toTerm) (id B) (id (succ Λ))).symm
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))
    (id (succ (B :: Λ)))),hm]
  simp only [Laws.assoc]
  erw [left_first_output,← left_first_input T Γ Θ]
  simp only [selectedMixed,Laws.assoc]

theorem conjLeftFirstNative_equation {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: C :: D)) (g : G P Θ (B :: Λ)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front [.conj A B] (D ++ Λ) C).right
      (G.conjR (Δ := C :: D) (Λ := Λ) f g)) h).denote =
      ofTerm (conjLeftFirstNative (G.cut ((HeadRouting.front [A] D C).right f) h) g).denote :=
  (leftFirstParent_denote f g h).trans (conjLeftFirstNative_denote f g h).symm

end BinaryLogical
end DosenPetric.Reduced.Gentzen
