module

public import DosenPetric.GentzenDisjSecondNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem disjPair_output_second {A B X Y U V V' : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B Y) V) (v : Hom V V') :
    disjPair f (comp g v) = comp (disjPair f g) (tensor .disj (id U) v) := by
  simpa only [Laws.comp_id] using (disjPair_output f g (id U) v).symm

theorem disjPair_input_second {A B X Y Y' U V : NormalForm P}
    (y : Hom Y Y') (f : Hom (.conj A X) U) (g : Hom (.conj B Y') V) :
    disjPair f (comp (tensor .conj (id B) y) g) =
      comp (tensor .conj (id (.disj A B)) (tensor .conj (id X) y)) (disjPair f g) := by
  simpa only [Laws.tensor_id,Laws.id_comp] using (disjPair_input (id X) y f g).symm

theorem disjSecondParent_denote {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) (C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front Δ E C).right (G.disjL f g)) h).denote =
      comp (disjSecondInput (.disj A B) T Γ Θ)
        (comp (disjPair (ofTerm f.denote)
          (comp ((sideM P .conj).cross B (ante T) (ante Θ)) (splice (ofTerm g.denote) (ofTerm h.denote))))
          (comp ((sideM P .disj).cross (succ J) (succ Δ) (succ E)) (disjFirstOutput J Δ E))) := by
  have hf := HeadRouting.front_split .disj Δ E C
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hf
  rw [cut_splice,ExchangeScript.right_denote,disjL_denote]
  simp only [Laws.assoc]
  erw [hf]
  rw [Splice.input]
  have hs : splice (comp (disjPair (ofTerm f.denote) (ofTerm g.denote))
      (comp ((sideM P .disj).cross C (succ Δ) (succ E))
        (tensor .disj (id C) (ofTerm (append .disj Δ E).toTerm)))) (ofTerm h.denote) =
      comp (splice (comp (disjPair (ofTerm f.denote) (ofTerm g.denote))
        ((sideM P .disj).cross C (succ Δ) (succ E))) (ofTerm h.denote))
          (tensor .disj (id (succ J)) (ofTerm (append .disj Δ E).toTerm)) := by
    simpa only [Laws.assoc] using Splice.residual (ofTerm (append .disj Δ E).toTerm)
      (comp (disjPair (ofTerm f.denote) (ofTerm g.denote)) ((sideM P .disj).cross C (succ Δ) (succ E)))
      (ofTerm h.denote)
  dsimp only [sideM,side,disjMonoidal,opposite,category] at hs ⊢
  erw [hs,disjL_left_second_core]
  simp only [disjSecondInput,disjFirstOutput,Laws.assoc]
  all_goals rfl

theorem disjSecondNative_denote {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) (C :: E)) (h : G P (C :: T) J) :
    ofTerm (disjSecondNative f (G.cut g h)).denote =
      comp (disjSecondInput (.disj A B) T Γ Θ)
        (comp (disjPair (ofTerm f.denote)
          (comp ((sideM P .conj).cross B (ante T) (ante Θ)) (splice (ofTerm g.denote) (ofTerm h.denote))))
          (comp ((sideM P .disj).cross (succ J) (succ Δ) (succ E)) (disjFirstOutput J Δ E))) := by
  unfold disjSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,ExchangeScript.left_denote,disjL_denote,
    ExchangeScript.left_denote,cut_splice]
  have hf := HeadRouting.front_split .conj T Θ B
  dsimp only [side,sideM,conjMonoidal,category,split] at hf
  simp only [Laws.assoc]
  erw [← Laws.assoc ((HeadRouting.front T Θ B).arrow .conj),hf]
  simp only [Laws.assoc]
  have ht : comp (tensor .conj (id B) (ofTerm (append .conj T Θ).invTerm))
      (comp ((sideM P .conj).cross B (ante T) (ante Θ))
        (comp (splice (ofTerm g.denote) (ofTerm h.denote)) (ofTerm (append .disj J E).toTerm))) =
      comp (comp (tensor .conj (id B) (ofTerm (append .conj T Θ).invTerm))
        (comp ((sideM P .conj).cross B (ante T) (ante Θ)) (splice (ofTerm g.denote) (ofTerm h.denote))))
          (ofTerm (append .disj J E).toTerm) := by
    simp only [Laws.assoc]
  erw [ht,disjPair_output_second,disjPair_input_second]
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (.disj A B)) (ofTerm (append .conj Γ (T ++ Θ)).invTerm)),
    ← Laws.assoc (((BinaryMix.swapBlocks Γ T Θ).consFixed (.disj A B)).arrow .conj),
    ← Laws.assoc ((HeadRouting.front T (Γ ++ Θ) (.disj A B)).inverse.arrow .conj),disj_second_input]
  rw [disj_second_output]

theorem disjSecondNative_equation {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) (C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front Δ E C).right (G.disjL f g)) h).denote =
      ofTerm (disjSecondNative f (G.cut g h)).denote :=
  (disjSecondParent_denote f g h).trans (disjSecondNative_denote f g h).symm

end DisjLogical
end DosenPetric.Reduced.Gentzen
