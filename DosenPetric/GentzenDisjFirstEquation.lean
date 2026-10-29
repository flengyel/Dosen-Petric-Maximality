module

public import DosenPetric.GentzenDisjFirstNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem disjFirstParent_denote {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) (C :: D)) (g : G P (B :: Θ) Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut (G.disjL f g) h).denote =
      comp (disjFirstInput (.disj A B) T Γ Θ)
        (comp (disjPair
          (comp ((sideM P .conj).cross A (ante T) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote)))
          (ofTerm g.denote))
          (comp (assocL .disj (succ J) (succ D) (succ Λ)) (disjFirstOutput J D Λ))) := by
  have ho := split_cons .disj C D Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at ho
  rw [cut_splice,disjL_denote,ho]
  rw [Splice.input]
  have hs : splice (comp (disjPair (ofTerm f.denote) (ofTerm g.denote))
      (comp (assocL .disj C (succ D) (succ Λ))
        (tensor .disj (id C) (ofTerm (append .disj D Λ).toTerm)))) (ofTerm h.denote) =
      comp (splice (comp (disjPair (ofTerm f.denote) (ofTerm g.denote))
        (assocL .disj C (succ D) (succ Λ))) (ofTerm h.denote))
          (tensor .disj (id (succ J)) (ofTerm (append .disj D Λ).toTerm)) := by
    simpa only [Laws.assoc] using Splice.residual (ofTerm (append .disj D Λ).toTerm)
      (comp (disjPair (ofTerm f.denote) (ofTerm g.denote)) (assocL .disj C (succ D) (succ Λ)))
      (ofTerm h.denote)
  rw [hs,disjL_left_first_core]
  simp only [disjFirstInput,disjFirstOutput,Laws.assoc]
  all_goals rfl

theorem disjFirstNative_denote {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) (C :: D)) (g : G P (B :: Θ) Λ) (h : G P (C :: T) J) :
    ofTerm (disjFirstNative (G.cut f h) g).denote =
      comp (disjFirstInput (.disj A B) T Γ Θ)
        (comp (disjPair
          (comp ((sideM P .conj).cross A (ante T) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote)))
          (ofTerm g.denote))
          (comp (assocL .disj (succ J) (succ D) (succ Λ)) (disjFirstOutput J D Λ))) := by
  unfold disjFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,ExchangeScript.left_denote,disjL_denote,
    ExchangeScript.left_denote,cut_splice]
  have hf := HeadRouting.front_split .conj T Γ A
  dsimp only [side,sideM,conjMonoidal,category,split] at hf
  simp only [Laws.assoc]
  erw [← Laws.assoc ((HeadRouting.front T Γ A).arrow .conj),hf]
  simp only [Laws.assoc]
  have ht : comp (tensor .conj (id A) (ofTerm (append .conj T Γ).invTerm))
      (comp ((sideM P .conj).cross A (ante T) (ante Γ))
        (comp (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm (append .disj J D).toTerm))) =
      comp (comp (tensor .conj (id A) (ofTerm (append .conj T Γ).invTerm))
        (comp ((sideM P .conj).cross A (ante T) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote))))
          (ofTerm (append .disj J D).toTerm) := by
    simp only [Laws.assoc]
  erw [ht,disjPair_output_first,disjPair_input_first]
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (.disj A B)) (ofTerm (append .conj (T ++ Γ) Θ).invTerm)),
    ← Laws.assoc (((ExchangeScript.appendAssoc T Γ Θ).consFixed (.disj A B)).arrow .conj),
    ← Laws.assoc ((HeadRouting.front T (Γ ++ Θ) (.disj A B)).inverse.arrow .conj),disj_first_input]
  rw [disj_first_output]

theorem disjFirstNative_equation {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) (C :: D)) (g : G P (B :: Θ) Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut (G.disjL f g) h).denote = ofTerm (disjFirstNative (G.cut f h) g).denote :=
  (disjFirstParent_denote f g h).trans (disjFirstNative_denote f g h).symm

end DisjLogical
end DosenPetric.Reduced.Gentzen
